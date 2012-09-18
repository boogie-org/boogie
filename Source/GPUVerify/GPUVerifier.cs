using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify
{
    class GPUVerifier : CheckingContext
    {
        public string outputFilename;
        public Program Program;
        public ResolutionContext ResContext;

        public Procedure KernelProcedure;
        public Implementation KernelImplementation;
        public Procedure BarrierProcedure;

        public IKernelArrayInfo KernelArrayInfo = new KernelArrayInfoLists();

        private HashSet<string> ReservedNames = new HashSet<string>();

        internal HashSet<string> OnlyThread1 = new HashSet<string>();
        internal HashSet<string> OnlyThread2 = new HashSet<string>();

        private int TempCounter = 0;

        internal const string LOCAL_ID_X_STRING = "local_id_x";
        internal const string LOCAL_ID_Y_STRING = "local_id_y";
        internal const string LOCAL_ID_Z_STRING = "local_id_z";

        internal static Constant _X = null;
        internal static Constant _Y = null;
        internal static Constant _Z = null;

        internal const string GROUP_SIZE_X_STRING = "group_size_x";
        internal const string GROUP_SIZE_Y_STRING = "group_size_y";
        internal const string GROUP_SIZE_Z_STRING = "group_size_z";

        internal static Constant _GROUP_SIZE_X = null;
        internal static Constant _GROUP_SIZE_Y = null;
        internal static Constant _GROUP_SIZE_Z = null;

        internal const string GROUP_ID_X_STRING = "group_id_x";
        internal const string GROUP_ID_Y_STRING = "group_id_y";
        internal const string GROUP_ID_Z_STRING = "group_id_z";

        internal static Constant _GROUP_X = null;
        internal static Constant _GROUP_Y = null;
        internal static Constant _GROUP_Z = null;

        internal const string NUM_GROUPS_X_STRING = "num_groups_x";
        internal const string NUM_GROUPS_Y_STRING = "num_groups_y";
        internal const string NUM_GROUPS_Z_STRING = "num_groups_z";

        internal static Constant _NUM_GROUPS_X = null;
        internal static Constant _NUM_GROUPS_Y = null;
        internal static Constant _NUM_GROUPS_Z = null;

        public IRaceInstrumenter RaceInstrumenter;

        public UniformityAnalyser uniformityAnalyser;
        public MayBePowerOfTwoAnalyser mayBePowerOfTwoAnalyser;
        public LiveVariableAnalyser liveVariableAnalyser;
        public ArrayControlFlowAnalyser arrayControlFlowAnalyser;
        public Dictionary<Implementation, VariableDefinitionAnalysis> varDefAnalyses;
        public Dictionary<Implementation, ReducedStrengthAnalysis> reducedStrengthAnalyses;

        public GPUVerifier(string filename, Program program, ResolutionContext rc, IRaceInstrumenter raceInstrumenter) : this(filename, program, rc, raceInstrumenter, false)
        {
        }

        public GPUVerifier(string filename, Program program, ResolutionContext rc, IRaceInstrumenter raceInstrumenter, bool skipCheck)
            : base((IErrorSink)null)
        {
            this.outputFilename = filename;
            this.Program = program;
            this.ResContext = rc;
            this.RaceInstrumenter = raceInstrumenter;
            if(!skipCheck)
                CheckWellFormedness();
        }

        public void setRaceInstrumenter(IRaceInstrumenter ri)
        {
            this.RaceInstrumenter = ri;
        }

        private void CheckWellFormedness()
        {
            int errorCount = Check();
            if (errorCount != 0)
            {
                Console.WriteLine("{0} GPUVerify format errors detected in {1}", errorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                Environment.Exit(1);
            }
        }

        private Procedure CheckExactlyOneKernelProcedure()
        {
            var p = CheckSingleInstanceOfAttributedProcedure("kernel");
            if (p == null)
            {
                Error(Program, "\"kernel\" attribute has not been specified for any procedure.  You must mark exactly one procedure with this attribute");
            }

            return p;
        }

        private Procedure FindOrCreateBarrierProcedure()
        {
            var p = CheckSingleInstanceOfAttributedProcedure("barrier");
            if (p == null)
            {
                p = new Procedure(Token.NoToken, "barrier", new TypeVariableSeq(),
                                  new VariableSeq(new Variable[] { 
                                    new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "__local_fence", new BvType(1)), true),
                                    new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "__global_fence", new BvType(1)), true) }),
                                  new VariableSeq(),
                                  new RequiresSeq(), new IdentifierExprSeq(),
                                  new EnsuresSeq(),
                                  new QKeyValue(Token.NoToken, "barrier", new List<object>(), null));
                Program.TopLevelDeclarations.Add(p);
                ResContext.AddProcedure(p);
            }
            return p;
        }

        private Procedure CheckSingleInstanceOfAttributedProcedure(string attribute)
        {
            Procedure attributedProcedure = null;

            foreach (Declaration decl in Program.TopLevelDeclarations)
            {
                if (!QKeyValue.FindBoolAttribute(decl.Attributes, attribute))
                {
                    continue;
                }

                if (decl is Implementation)
                {
                    continue;
                }

                if (decl is Procedure)
                {
                    if (attributedProcedure == null)
                    {
                        attributedProcedure = decl as Procedure;
                    }
                    else
                    {
                        Error(decl, "\"{0}\" attribute specified for procedure {1}, but it has already been specified for procedure {2}", attribute, (decl as Procedure).Name, attributedProcedure.Name);
                    }

                }
                else
                {
                    Error(decl, "\"{0}\" attribute can only be applied to a procedure", attribute);
                }
            }

            return attributedProcedure;
        }

        private void CheckLocalVariables()
        {
            foreach (LocalVariable LV in KernelImplementation.LocVars)
            {
                if (QKeyValue.FindBoolAttribute(LV.Attributes, "group_shared"))
                {
                    Error(LV.tok, "Local variable must not be marked 'group_shared' -- promote the variable to global scope");
                }
            }
        }


        private void ReportMultipleAttributeError(string attribute, IToken first, IToken second)
        {
            Error(
                second, 
                "Can only have one {0} attribute, but previously saw this attribute at ({1}, {2})", 
                attribute,
                first.filename,
                first.line, first.col - 1);
        }

        private bool setConstAttributeField(Constant constInProgram, string attr, ref Constant constFieldRef)
        {
            if (QKeyValue.FindBoolAttribute(constInProgram.Attributes, attr))
            {
                if (constFieldRef != null)
                {
                    ReportMultipleAttributeError(attr, constFieldRef.tok, constInProgram.tok);
                    return false;
                }
                CheckSpecialConstantType(constInProgram);
                constFieldRef = constInProgram;
            }
            return true;
        }

        private void MaybeCreateAttributedConst(string attr, ref Constant constFieldRef)
        {
            if (constFieldRef == null)
            {
                constFieldRef = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, attr, Microsoft.Boogie.Type.GetBvType(32)), /*unique=*/false);
                constFieldRef.AddAttribute(attr);
                Program.TopLevelDeclarations.Add(constFieldRef);
            }
        }

        private bool FindNonLocalVariables()
        {
            bool success = true;
            foreach (Declaration D in Program.TopLevelDeclarations)
            {
                if (D is Variable && 
                    (D as Variable).IsMutable && 
                    (D as Variable).TypedIdent.Type is MapType &&
                    !ReservedNames.Contains((D as Variable).Name))
                {
                    if (QKeyValue.FindBoolAttribute(D.Attributes, "group_shared"))
                    {
                        KernelArrayInfo.getGroupSharedArrays().Add(D as Variable);
                    }
                    else if (QKeyValue.FindBoolAttribute(D.Attributes, "global"))
                    {
                        KernelArrayInfo.getGlobalArrays().Add(D as Variable);
                    }
                    else
                    {
                        KernelArrayInfo.getPrivateArrays().Add(D as Variable);
                    }
                }
                else if (D is Constant)
                {
                    Constant C = D as Constant;

                    success &= setConstAttributeField(C, LOCAL_ID_X_STRING, ref _X);
                    success &= setConstAttributeField(C, LOCAL_ID_Y_STRING, ref _Y);
                    success &= setConstAttributeField(C, LOCAL_ID_Z_STRING, ref _Z);

                    success &= setConstAttributeField(C, GROUP_SIZE_X_STRING, ref _GROUP_SIZE_X);
                    success &= setConstAttributeField(C, GROUP_SIZE_Y_STRING, ref _GROUP_SIZE_Y);
                    success &= setConstAttributeField(C, GROUP_SIZE_Z_STRING, ref _GROUP_SIZE_Z);

                    success &= setConstAttributeField(C, GROUP_ID_X_STRING, ref _GROUP_X);
                    success &= setConstAttributeField(C, GROUP_ID_Y_STRING, ref _GROUP_Y);
                    success &= setConstAttributeField(C, GROUP_ID_Z_STRING, ref _GROUP_Z);

                    success &= setConstAttributeField(C, NUM_GROUPS_X_STRING, ref _NUM_GROUPS_X);
                    success &= setConstAttributeField(C, NUM_GROUPS_Y_STRING, ref _NUM_GROUPS_Y);
                    success &= setConstAttributeField(C, NUM_GROUPS_Z_STRING, ref _NUM_GROUPS_Z);


                }
            }

            MaybeCreateAttributedConst(LOCAL_ID_X_STRING, ref _X);
            MaybeCreateAttributedConst(LOCAL_ID_Y_STRING, ref _Y);
            MaybeCreateAttributedConst(LOCAL_ID_Z_STRING, ref _Z);

            MaybeCreateAttributedConst(GROUP_SIZE_X_STRING, ref _GROUP_SIZE_X);
            MaybeCreateAttributedConst(GROUP_SIZE_Y_STRING, ref _GROUP_SIZE_Y);
            MaybeCreateAttributedConst(GROUP_SIZE_Z_STRING, ref _GROUP_SIZE_Z);

            MaybeCreateAttributedConst(GROUP_ID_X_STRING, ref _GROUP_X);
            MaybeCreateAttributedConst(GROUP_ID_Y_STRING, ref _GROUP_Y);
            MaybeCreateAttributedConst(GROUP_ID_Z_STRING, ref _GROUP_Z);

            MaybeCreateAttributedConst(NUM_GROUPS_X_STRING, ref _NUM_GROUPS_X);
            MaybeCreateAttributedConst(NUM_GROUPS_Y_STRING, ref _NUM_GROUPS_Y);
            MaybeCreateAttributedConst(NUM_GROUPS_Z_STRING, ref _NUM_GROUPS_Z);

            return success;
        }

        private void CheckSpecialConstantType(Constant C)
        {
            if (!(C.TypedIdent.Type.Equals(Microsoft.Boogie.Type.Int) || C.TypedIdent.Type.Equals(Microsoft.Boogie.Type.GetBvType(32))))
            {
                Error(C.tok, "Special constant '" + C.Name + "' must have type 'int' or 'bv32'");
            }
        }

        private void GetKernelImplementation()
        {
            foreach (Declaration decl in Program.TopLevelDeclarations)
            {
                if (!(decl is Implementation))
                {
                    continue;
                }

                Implementation Impl = decl as Implementation;

                if (Impl.Proc == KernelProcedure)
                {
                    KernelImplementation = Impl;
                    break;
                }

            }

            if (KernelImplementation == null)
            {
                Error(Token.NoToken, "*** Error: no implementation of kernel procedure");
            }
        }




        protected virtual void CheckKernelImplementation()
        {
            CheckKernelParameters();
            GetKernelImplementation();

            if (KernelImplementation == null)
            {
                return;
            }

            CheckLocalVariables();
            CheckNoReturns();
        }

        private void CheckNoReturns()
        {
            // TODO!
        }

        internal void preProcess()
        {
            RemoveRedundantReturns();

            RemoveElseIfs();

            PullOutNonLocalAccesses();
        }

        private void MergeBlocksIntoPredecessors()
        {
            foreach (var impl in Program.TopLevelDeclarations.OfType<Implementation>())
                VC.VCGen.MergeBlocksIntoPredecessors(Program, impl);
        }

        internal void doit()
        {
            File.Delete(Path.GetFileNameWithoutExtension(CommandLineOptions.inputFiles[0]) + ".loc"); 
            if (CommandLineOptions.Unstructured)
            {
                Microsoft.Boogie.CommandLineOptions.Clo.PrintUnstructured = 2;
            }

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_original");
            }

            preProcess();

            if (CommandLineOptions.ShowStages) {
              emitProgram(outputFilename + "_preprocessed");
            }

            DoLiveVariableAnalysis();

            DoUniformityAnalysis();

            DoVariableDefinitionAnalysis();

            DoReducedStrengthAnalysis();

            DoMayBePowerOfTwoAnalysis();

            DoArrayControlFlowAnalysis();

            if (CommandLineOptions.Inference)
            {
                foreach (var impl in Program.TopLevelDeclarations.OfType<Implementation>().ToList())
                {
                    LoopInvariantGenerator.PreInstrument(this, impl);
                }

                if (CommandLineOptions.ShowStages) {
                  emitProgram(outputFilename + "_pre_inference");
                }

            }

            RaceInstrumenter.AddRaceCheckingInstrumentation();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_instrumented");
            }

            AbstractSharedState();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_abstracted");
            }

            MergeBlocksIntoPredecessors();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_merged_pre_predication");
            }

            MakeKernelPredicated();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_predicated");
            }

            MergeBlocksIntoPredecessors();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_merged_post_predication");
            }

            MakeKernelDualised();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_dualised");
            }

            RaceInstrumenter.AddRaceCheckingDeclarations();

            GenerateBarrierImplementation();

            GenerateStandardKernelContract();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_ready_to_verify");
            }

            if (CommandLineOptions.Inference)
            {
                ComputeInvariant();
            }

            emitProgram(outputFilename);

        }

        private void DoMayBePowerOfTwoAnalysis()
        {
            mayBePowerOfTwoAnalyser = new MayBePowerOfTwoAnalyser(this);
            mayBePowerOfTwoAnalyser.Analyse();
        }

        private void DoArrayControlFlowAnalysis()
        {
            arrayControlFlowAnalyser = new ArrayControlFlowAnalyser(this);
            arrayControlFlowAnalyser.Analyse();
        }

        private void DoUniformityAnalysis()
        {
            uniformityAnalyser = new UniformityAnalyser(this);
            uniformityAnalyser.Analyse();
        }

        private void DoLiveVariableAnalysis()
        {
            liveVariableAnalyser = new LiveVariableAnalyser(this);
            liveVariableAnalyser.Analyse();
        }

        private void DoVariableDefinitionAnalysis()
        {
            varDefAnalyses = Program.TopLevelDeclarations
                .OfType<Implementation>()
                .ToDictionary(i => i, i => VariableDefinitionAnalysis.Analyse(this, i));
        }

        private void DoReducedStrengthAnalysis()
        {
            reducedStrengthAnalyses = Program.TopLevelDeclarations
                .OfType<Implementation>()
                .ToDictionary(i => i, i => ReducedStrengthAnalysis.Analyse(this, i));
        }

        private void emitProgram(string filename)
        {
            using (TokenTextWriter writer = new TokenTextWriter(filename + ".bpl"))
            {
                Program.Emit(writer);
            }
        }

        private void ComputeInvariant()
        {
            for (int i = 0; i < Program.TopLevelDeclarations.Count; i++)
            {
                if (Program.TopLevelDeclarations[i] is Implementation)
                {

                    Implementation Impl = Program.TopLevelDeclarations[i] as Implementation;

                    List<Expr> UserSuppliedInvariants = GetUserSuppliedInvariants(Impl.Name);

                    LoopInvariantGenerator.PostInstrument(this, Impl, UserSuppliedInvariants);

                    Procedure Proc = Impl.Proc;

                    if (QKeyValue.FindIntAttribute(Proc.Attributes, "inline", -1) == 1)
                    {
                        continue;
                    }

                    if (Proc == KernelProcedure)
                    {
                        continue;
                    }

                    AddCandidateRequires(Proc);
                    RaceInstrumenter.AddRaceCheckingCandidateRequires(Proc);
                    AddUserSuppliedCandidateRequires(Proc, UserSuppliedInvariants);

                    AddCandidateEnsures(Proc);
                    RaceInstrumenter.AddRaceCheckingCandidateEnsures(Proc);
                    AddUserSuppliedCandidateEnsures(Proc, UserSuppliedInvariants);

                }


            }

        }

        private void AddCandidateEnsures(Procedure Proc)
        {
            HashSet<string> names = new HashSet<String>();
            foreach (Variable v in Proc.OutParams)
            {
                names.Add(StripThreadIdentifier(v.Name));
            }

            foreach (string name in names)
            {
                if (!uniformityAnalyser.IsUniform(Proc.Name, name))
                {
                    AddEqualityCandidateEnsures(Proc, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, name, Microsoft.Boogie.Type.Int)));
                }
            }

        }

        private void AddCandidateRequires(Procedure Proc)
        {
            HashSet<string> names = new HashSet<String>();
            foreach (Variable v in Proc.InParams)
            {
                names.Add(StripThreadIdentifier(v.Name));
            }

            foreach (string name in names)
            {

                if (IsPredicateOrTemp(name))
                {
                    Debug.Assert(name.Equals("_P"));
                    Debug.Assert(!uniformityAnalyser.IsUniform(Proc.Name));
                    AddCandidateRequires(Proc, Expr.Eq(
                        new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, name + "$1", Microsoft.Boogie.Type.Bool))),
                        new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, name + "$2", Microsoft.Boogie.Type.Bool)))
                    ));
                }
                else
                {
                    if (!uniformityAnalyser.IsUniform(Proc.Name, name))
                    {
                        if (!uniformityAnalyser.IsUniform(Proc.Name))
                        {
                            AddPredicatedEqualityCandidateRequires(Proc, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, name, Microsoft.Boogie.Type.Int)));
                        }
                        AddEqualityCandidateRequires(Proc, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, name, Microsoft.Boogie.Type.Int)));
                    }
                }
            }

        }

        private void AddPredicatedEqualityCandidateRequires(Procedure Proc, Variable v)
        {
            AddCandidateRequires(Proc, Expr.Imp(
                Expr.And(
                    new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, "_P$1", Microsoft.Boogie.Type.Bool))),
                    new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, "_P$2", Microsoft.Boogie.Type.Bool)))
                ),
                Expr.Eq(
                    new IdentifierExpr(Proc.tok, new VariableDualiser(1, uniformityAnalyser, Proc.Name).VisitVariable(v.Clone() as Variable)),
                    new IdentifierExpr(Proc.tok, new VariableDualiser(2, uniformityAnalyser, Proc.Name).VisitVariable(v.Clone() as Variable))
                )
            ));
        }

        private void AddEqualityCandidateRequires(Procedure Proc, Variable v)
        {
            AddCandidateRequires(Proc,
                Expr.Eq(
                    new IdentifierExpr(Proc.tok, new VariableDualiser(1, uniformityAnalyser, Proc.Name).VisitVariable(v.Clone() as Variable)),
                    new IdentifierExpr(Proc.tok, new VariableDualiser(2, uniformityAnalyser, Proc.Name).VisitVariable(v.Clone() as Variable))
                )
            );
        }

        private void AddEqualityCandidateEnsures(Procedure Proc, Variable v)
        {
            AddCandidateEnsures(Proc,
                Expr.Eq(
                    new IdentifierExpr(Proc.tok, new VariableDualiser(1, uniformityAnalyser, Proc.Name).VisitVariable(v.Clone() as Variable)),
                    new IdentifierExpr(Proc.tok, new VariableDualiser(2, uniformityAnalyser, Proc.Name).VisitVariable(v.Clone() as Variable))
                ));
        }


        private void AddUserSuppliedCandidateRequires(Procedure Proc, List<Expr> UserSuppliedInvariants)
        {
            foreach (Expr e in UserSuppliedInvariants)
            {
                Requires r = new Requires(false, e);
                Proc.Requires.Add(r);
                bool OK = ProgramIsOK(Proc);
                Proc.Requires.Remove(r);
                if (OK)
                {
                    AddCandidateRequires(Proc, e);
                }
            }
        }

        private void AddUserSuppliedCandidateEnsures(Procedure Proc, List<Expr> UserSuppliedInvariants)
        {
            foreach (Expr e in UserSuppliedInvariants)
            {
                Ensures ens = new Ensures(false, e);
                Proc.Ensures.Add(ens);
                bool OK = ProgramIsOK(Proc);
                Proc.Ensures.Remove(ens);
                if (OK)
                {
                    AddCandidateEnsures(Proc, e);
                }
            }
        }



        internal void AddCandidateRequires(Procedure Proc, Expr e)
        {
            Constant ExistentialBooleanConstant = Program.MakeExistentialBoolean();
            IdentifierExpr ExistentialBoolean = new IdentifierExpr(Proc.tok, ExistentialBooleanConstant);
            Proc.Requires.Add(new Requires(false, Expr.Imp(ExistentialBoolean, e)));
        }

        internal void AddCandidateEnsures(Procedure Proc, Expr e)
        {
            Constant ExistentialBooleanConstant = Program.MakeExistentialBoolean();
            IdentifierExpr ExistentialBoolean = new IdentifierExpr(Proc.tok, ExistentialBooleanConstant);
            Proc.Ensures.Add(new Ensures(false, Expr.Imp(ExistentialBoolean, e)));
        }

        private List<Expr> GetUserSuppliedInvariants(string ProcedureName)
        {
            List<Expr> result = new List<Expr>();

            if (CommandLineOptions.invariantsFile == null)
            {
                return result;
            }

            StreamReader sr = new StreamReader(new FileStream(CommandLineOptions.invariantsFile, FileMode.Open, FileAccess.Read));
            string line;
            int lineNumber = 1;
            while ((line = sr.ReadLine()) != null)
            {
                string[] components = line.Split(':');

                if (components.Length != 1 && components.Length != 2)
                {
                    Console.WriteLine("Ignoring badly formed candidate invariant '" + line + "' at '" + CommandLineOptions.invariantsFile + "' line " + lineNumber);
                    continue;
                }

                if (components.Length == 2)
                {
                    if (!components[0].Trim().Equals(ProcedureName))
                    {
                        continue;
                    }

                    line = components[1];
                }

                string temp_program_text = "axiom (" + line + ");";
                TokenTextWriter writer = new TokenTextWriter("temp_out.bpl");
                writer.WriteLine(temp_program_text);
                writer.Close();

                Program temp_program = GPUVerify.ParseBoogieProgram(new List<string>(new string[] { "temp_out.bpl" }), false);

                if (null == temp_program)
                {
                    Console.WriteLine("Ignoring badly formed candidate invariant '" + line + "' at '" + CommandLineOptions.invariantsFile + "' line " + lineNumber);
                }
                else
                {
                    Debug.Assert(temp_program.TopLevelDeclarations[0] is Axiom);
                    result.Add((temp_program.TopLevelDeclarations[0] as Axiom).Expr);
                }

                lineNumber++;
            }

            return result;
        }

        internal bool ContainsNamedVariable(HashSet<Variable> variables, string name)
        {
            foreach(Variable v in variables)
            {
                if(StripThreadIdentifier(v.Name) == name)
                {
                    return true;
                }
            }
            return false;
        }

        internal static bool IsPredicate(string v) {
          if (v.Length < 2) {
            return false;
          }
          if (!v.Substring(0, 1).Equals("p")) {
            return false;
          }
          for (int i = 1; i < v.Length; i++) {
            if (!Char.IsDigit(v.ToCharArray()[i])) {
              return false;
            }
          }
          return true;
        }

        internal static bool IsPredicateOrTemp(string lv) {
          
          // We should improve this by having a general convention
          // for names of temporary or predicate variables

          if (lv.Length >= 2) {
            if (lv.Substring(0, 1).Equals("p") || lv.Substring(0, 1).Equals("v")) {
              for (int i = 1; i < lv.Length; i++) {
                if (!Char.IsDigit(lv.ToCharArray()[i])) {
                  return false;
                }
              }
              return true;
            }

          }

          if (lv.Contains("_HAVOC_")) {
            return true;
          }

          return (lv.Length >= 2 && lv.Substring(0,2).Equals("_P")) ||
                  (lv.Length > 3 && lv.Substring(0,3).Equals("_LC")) ||
                  (lv.Length > 5 && lv.Substring(0,5).Equals("_temp"));
        }

        


        internal bool ProgramIsOK(Declaration d)
        {
            Debug.Assert(d is Procedure || d is Implementation);
            TokenTextWriter writer = new TokenTextWriter("temp_out.bpl");
            List<Declaration> RealDecls = Program.TopLevelDeclarations;
            List<Declaration> TempDecls = new List<Declaration>();
            foreach (Declaration d2 in RealDecls)
            {
                if (d is Procedure)
                {
                    if ((d == d2) || !(d2 is Implementation || d2 is Procedure))
                    {
                        TempDecls.Add(d2);
                    }
                }
                else if (d is Implementation)
                {
                    if ((d == d2) || !(d2 is Implementation))
                    {
                        TempDecls.Add(d2);
                    }
                }
            }
            Program.TopLevelDeclarations = TempDecls;
            Program.Emit(writer);
            writer.Close();
            Program.TopLevelDeclarations = RealDecls;
            Program temp_program = GPUVerify.ParseBoogieProgram(new List<string>(new string[] { "temp_out.bpl" }), false);

            if (temp_program == null)
            {
                return false;
            }

            if (temp_program.Resolve() != 0)
            {
                return false;
            }

            if (temp_program.Typecheck() != 0)
            {
                return false;
            }
            return true;
        }

        

        public static Microsoft.Boogie.Type GetTypeOfIdX()
        {
            Contract.Requires(_X != null);
            return _X.TypedIdent.Type;
        }

        public static Microsoft.Boogie.Type GetTypeOfIdY()
        {
            Contract.Requires(_Y != null);
            return _Y.TypedIdent.Type;
        }

        public static Microsoft.Boogie.Type GetTypeOfIdZ()
        {
            Contract.Requires(_Z != null);
            return _Z.TypedIdent.Type;
        }

        public static Microsoft.Boogie.Type GetTypeOfId(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return GetTypeOfIdX();
            if (dimension.Equals("Y")) return GetTypeOfIdY();
            if (dimension.Equals("Z")) return GetTypeOfIdZ();
            Debug.Assert(false);
            return null;
        }

        public bool KernelHasIdX()
        {
            return _X != null;
        }

        public bool KernelHasIdY()
        {
            return _Y != null;
        }

        public bool KernelHasIdZ()
        {
            return _Z != null;
        }

        public bool KernelHasGroupIdX()
        {
            return _GROUP_X != null;
        }

        public bool KernelHasGroupIdY()
        {
            return _GROUP_Y != null;
        }

        public bool KernelHasGroupIdZ()
        {
            return _GROUP_Z != null;
        }

        public bool KernelHasNumGroupsX()
        {
            return _NUM_GROUPS_X != null;
        }

        public bool KernelHasNumGroupsY()
        {
            return _NUM_GROUPS_Y != null;
        }

        public bool KernelHasNumGroupsZ()
        {
            return _NUM_GROUPS_Z != null;
        }

        public bool KernelHasGroupSizeX()
        {
            return _GROUP_SIZE_X != null;
        }

        public bool KernelHasGroupSizeY()
        {
            return _GROUP_SIZE_Y != null;
        }

        public bool KernelHasGroupSizeZ()
        {
            return _GROUP_SIZE_Z != null;
        }

        internal static string StripThreadIdentifier(string p, out int id)
        {
            if (p.EndsWith("$1"))
            {
                id = 1;
                return p.Substring(0, p.Length - 2);
            }
            if (p.EndsWith("$2"))
            {
                id = 2;
                return p.Substring(0, p.Length - 2);
            }

            id = 0;
            return p;
        }

        internal static string StripThreadIdentifier(string p)
        {
            int id;
            return StripThreadIdentifier(p, out id);
        }

        private void GenerateStandardKernelContract()
        {
            RaceInstrumenter.AddKernelPrecondition();

            IToken tok = KernelImplementation.tok;

            GeneratePreconditionsForDimension(tok, "X");
            GeneratePreconditionsForDimension(tok, "Y");
            GeneratePreconditionsForDimension(tok, "Z");

            RaceInstrumenter.AddStandardSourceVariablePreconditions();
            RaceInstrumenter.AddStandardSourceVariablePostconditions();

            foreach (Declaration D in Program.TopLevelDeclarations)
            {
                if (!(D is Procedure))
                {
                    continue;
                }
                Procedure Proc = D as Procedure;
                if (QKeyValue.FindIntAttribute(Proc.Attributes, "inline", -1) == 1)
                {
                    continue;
                }

                Expr DistinctLocalIds =
                    Expr.Or(
                        Expr.Or(
                            Expr.Neq(
                            new IdentifierExpr(tok, MakeThreadId(tok, "X", 1)),
                            new IdentifierExpr(tok, MakeThreadId(tok, "X", 2))
                            ),
                            Expr.Neq(
                            new IdentifierExpr(tok, MakeThreadId(tok, "Y", 1)),
                            new IdentifierExpr(tok, MakeThreadId(tok, "Y", 2))
                            )
                        ),
                        Expr.Neq(
                        new IdentifierExpr(tok, MakeThreadId(tok, "Z", 1)),
                        new IdentifierExpr(tok, MakeThreadId(tok, "Z", 2))
                        )
                    );

                Proc.Requires.Add(new Requires(false, Expr.Imp(ThreadsInSameGroup(), DistinctLocalIds)));

                if (CommandLineOptions.OnlyIntraGroupRaceChecking)
                {
                    Proc.Requires.Add(new Requires(false, ThreadsInSameGroup()));
                }

                if (Proc == KernelProcedure)
                {
                    bool foundNonUniform = false;
                    int indexOfFirstNonUniformParameter;
                    for (indexOfFirstNonUniformParameter = 0; indexOfFirstNonUniformParameter < Proc.InParams.Length; indexOfFirstNonUniformParameter++)
                    {
                        if (!uniformityAnalyser.IsUniform(Proc.Name, StripThreadIdentifier(Proc.InParams[indexOfFirstNonUniformParameter].Name)))
                        {
                            foundNonUniform = true;
                            break;
                        }
                    }

                    if (foundNonUniform)
                    {
                        // I have a feeling this will never be reachable!!!
                        int numberOfNonUniformParameters = (Proc.InParams.Length - indexOfFirstNonUniformParameter) / 2;
                        for (int i = indexOfFirstNonUniformParameter; i < numberOfNonUniformParameters; i++)
                        {
                            Proc.Requires.Add(new Requires(false,
                                Expr.Eq(new IdentifierExpr(Proc.InParams[i].tok, Proc.InParams[i]),
                                        new IdentifierExpr(Proc.InParams[i + numberOfNonUniformParameters].tok, Proc.InParams[i + numberOfNonUniformParameters]))));
                        }
                    }
                }

            }

            foreach (Declaration D in Program.TopLevelDeclarations)
            {
              if (!(D is Implementation))
              {
                continue;
              }
              Implementation Impl = D as Implementation;
              
              foreach (IRegion subregion in RootRegion(Impl).SubRegions())
              {
                RaceInstrumenter.AddSourceLocationLoopInvariants(Impl, subregion);
              }
            }

            foreach (Declaration D in Program.TopLevelDeclarations)
            {
                if (!(D is Implementation))
                {
                    continue;
                }
                Implementation Impl = D as Implementation;

                if (QKeyValue.FindIntAttribute(Impl.Proc.Attributes, "inline", -1) == 1)
                {
                    continue;
                }
                if (Impl.Proc == KernelProcedure)
                {
                    continue;
                }

                new EnsureDisabledThreadHasNoEffectInstrumenter(this, Impl).instrument();

            }

        }

        internal static Expr ThreadsInSameGroup()
        {
            return Expr.And(
                                        Expr.And(
                                            Expr.Eq(
                                            new IdentifierExpr(Token.NoToken, MakeGroupId("X", 1)),
                                            new IdentifierExpr(Token.NoToken, MakeGroupId("X", 2))
                                            ),
                                            Expr.Eq(
                                            new IdentifierExpr(Token.NoToken, MakeGroupId("Y", 1)),
                                            new IdentifierExpr(Token.NoToken, MakeGroupId("Y", 2))
                                            )
                                        ),
                                        Expr.Eq(
                                        new IdentifierExpr(Token.NoToken, MakeGroupId("Z", 1)),
                                        new IdentifierExpr(Token.NoToken, MakeGroupId("Z", 2))
                                        )
                                    );
        }

        internal static void AddInvariantToAllLoops(Expr Invariant, StmtList stmtList)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                AddInvariantToAllLoops(Invariant, bb);
            }
        }

        internal static void AddInvariantToAllLoops(Expr Invariant, BigBlock bb)
        {
            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;
                wc.Invariants.Add(new AssertCmd(wc.tok, Invariant));
                AddInvariantToAllLoops(Invariant, wc.Body);
            }
            Debug.Assert(!(bb.ec is IfCmd));
        }

        internal static int GetThreadSuffix(string p)
        {
            return Int32.Parse(p.Substring(p.IndexOf("$") + 1, p.Length - (p.IndexOf("$") + 1)));
        }

        private void GeneratePreconditionsForDimension(IToken tok, String dimension)
        {
            foreach (Declaration D in Program.TopLevelDeclarations.ToList())
            {
                if (!(D is Procedure))
                {
                    continue;
                }
                Procedure Proc = D as Procedure;
                if (QKeyValue.FindIntAttribute(Proc.Attributes, "inline", -1) == 1)
                {
                    continue;
                }

                Expr GroupSizePositive;
                Expr NumGroupsPositive;
                Expr GroupIdNonNegative;
                Expr GroupIdLessThanNumGroups;

                if (GetTypeOfId(dimension).Equals(Microsoft.Boogie.Type.GetBvType(32)))
                {
                    GroupSizePositive = MakeBVSgt(new IdentifierExpr(tok, GetGroupSize(dimension)), ZeroBV());
                    NumGroupsPositive = MakeBVSgt(new IdentifierExpr(tok, GetNumGroups(dimension)), ZeroBV());
                    GroupIdNonNegative = MakeBVSge(new IdentifierExpr(tok, GetGroupId(dimension)), ZeroBV());
                    GroupIdLessThanNumGroups = MakeBVSlt(new IdentifierExpr(tok, GetGroupId(dimension)), new IdentifierExpr(tok, GetNumGroups(dimension)));
                }
                else
                {
                    GroupSizePositive = Expr.Gt(new IdentifierExpr(tok, GetGroupSize(dimension)), Zero());
                    NumGroupsPositive = Expr.Gt(new IdentifierExpr(tok, GetNumGroups(dimension)), Zero());
                    GroupIdNonNegative = Expr.Ge(new IdentifierExpr(tok, GetGroupId(dimension)), Zero());
                    GroupIdLessThanNumGroups = Expr.Lt(new IdentifierExpr(tok, GetGroupId(dimension)), new IdentifierExpr(tok, GetNumGroups(dimension)));
                }

                Proc.Requires.Add(new Requires(false, GroupSizePositive));
                Proc.Requires.Add(new Requires(false, NumGroupsPositive));
                Proc.Requires.Add(new Requires(false, new VariableDualiser(1, null, null).VisitExpr(GroupIdNonNegative)));
                Proc.Requires.Add(new Requires(false, new VariableDualiser(2, null, null).VisitExpr(GroupIdNonNegative)));
                Proc.Requires.Add(new Requires(false, new VariableDualiser(1, null, null).VisitExpr(GroupIdLessThanNumGroups)));
                Proc.Requires.Add(new Requires(false, new VariableDualiser(2, null, null).VisitExpr(GroupIdLessThanNumGroups)));

                Expr ThreadIdNonNegative =
                    GetTypeOfId(dimension).Equals(Microsoft.Boogie.Type.GetBvType(32)) ?
                            MakeBVSge(new IdentifierExpr(tok, MakeThreadId(tok, dimension)), ZeroBV())
                    :
                            Expr.Ge(new IdentifierExpr(tok, MakeThreadId(tok, dimension)), Zero());
                Expr ThreadIdLessThanGroupSize =
                    GetTypeOfId(dimension).Equals(Microsoft.Boogie.Type.GetBvType(32)) ?
                            MakeBVSlt(new IdentifierExpr(tok, MakeThreadId(tok, dimension)), new IdentifierExpr(tok, GetGroupSize(dimension)))
                    :
                            Expr.Lt(new IdentifierExpr(tok, MakeThreadId(tok, dimension)), new IdentifierExpr(tok, GetGroupSize(dimension)));

                Proc.Requires.Add(new Requires(false, new VariableDualiser(1, null, null).VisitExpr(ThreadIdNonNegative)));
                Proc.Requires.Add(new Requires(false, new VariableDualiser(2, null, null).VisitExpr(ThreadIdNonNegative)));
                Proc.Requires.Add(new Requires(false, new VariableDualiser(1, null, null).VisitExpr(ThreadIdLessThanGroupSize)));
                Proc.Requires.Add(new Requires(false, new VariableDualiser(2, null, null).VisitExpr(ThreadIdLessThanGroupSize)));

            }

        }

        private Function GetOrCreateBVFunction(string functionName, string smtName, Microsoft.Boogie.Type resultType, params Microsoft.Boogie.Type[] argTypes)
        {
            Function f = (Function)ResContext.LookUpProcedure(functionName);
            if (f != null)
                return f;

            f = new Function(Token.NoToken, functionName,
                             new VariableSeq(argTypes.Select(t => new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "", t))).ToArray()),
                             new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "", resultType)));
            f.AddAttribute("bvbuiltin", smtName);
            Program.TopLevelDeclarations.Add(f);
            ResContext.AddProcedure(f);
            return f;
        }

        private Expr MakeBVFunctionCall(string functionName, string smtName, Microsoft.Boogie.Type resultType, params Expr[] args)
        {
            Function f = GetOrCreateBVFunction(functionName, smtName, resultType, args.Select(a => a.Type).ToArray());
            var e = new NAryExpr(Token.NoToken, new FunctionCall(f), new ExprSeq(args));
            e.Type = resultType;
            return e;
        }

        private Expr MakeBitVectorBinaryBoolean(string suffix, string smtName, Expr lhs, Expr rhs)
        {
            return MakeBVFunctionCall("BV" + lhs.Type.BvBits + "_" + suffix, smtName, Microsoft.Boogie.Type.Bool, lhs, rhs);
        }

        private Expr MakeBitVectorBinaryBitVector(string suffix, string smtName, Expr lhs, Expr rhs)
        {
            return MakeBVFunctionCall("BV" + lhs.Type.BvBits + "_" + suffix, smtName, lhs.Type, lhs, rhs);
        }

        internal Expr MakeBVSlt(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBoolean("SLT", "bvslt", lhs, rhs); }
        internal Expr MakeBVSgt(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBoolean("SGT", "bvsgt", lhs, rhs); }
        internal Expr MakeBVSge(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBoolean("SGE", "bvsge", lhs, rhs); }

        internal Expr MakeBVAnd(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBitVector("AND", "bvand", lhs, rhs); }
        internal Expr MakeBVAdd(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBitVector("ADD", "bvadd", lhs, rhs); }
        internal Expr MakeBVSub(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBitVector("SUB", "bvsub", lhs, rhs); }
        internal Expr MakeBVMul(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBitVector("MUL", "bvmul", lhs, rhs); }
        internal Expr MakeBVURem(Expr lhs, Expr rhs) { return MakeBitVectorBinaryBitVector("UREM", "bvurem", lhs, rhs); }

        internal static Expr MakeBitVectorBinaryBoolean(string functionName, Expr lhs, Expr rhs)
        {
            return new NAryExpr(lhs.tok, new FunctionCall(new Function(lhs.tok, functionName, new VariableSeq(new Variable[] { 
                new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "arg1", Microsoft.Boogie.Type.GetBvType(32))),
                new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "arg2", Microsoft.Boogie.Type.GetBvType(32)))
            }), new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "result", Microsoft.Boogie.Type.Bool)))), new ExprSeq(new Expr[] { lhs, rhs }));
        }

        internal static Expr MakeBitVectorBinaryBitVector(string functionName, Expr lhs, Expr rhs)
        {
            return new NAryExpr(lhs.tok, new FunctionCall(new Function(lhs.tok, functionName, new VariableSeq(new Variable[] { 
                new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "arg1", Microsoft.Boogie.Type.GetBvType(32))),
                new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "arg2", Microsoft.Boogie.Type.GetBvType(32)))
            }), new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "result", Microsoft.Boogie.Type.GetBvType(32))))), new ExprSeq(new Expr[] { lhs, rhs }));
        }

        private static bool IsBVFunctionCall(Expr e, string smtName, out ExprSeq args)
        {
            args = null;
            var ne = e as NAryExpr;
            if (ne == null)
                return false;

            var fc = ne.Fun as FunctionCall;
            if (fc == null)
                return false;

            string bvBuiltin = QKeyValue.FindStringAttribute(fc.Func.Attributes, "bvbuiltin");
            if (bvBuiltin == smtName)
            {
                args = ne.Args;
                return true;
            }

            return false;
        }

        private static bool IsBVFunctionCall(Expr e, string smtName, out Expr lhs, out Expr rhs)
        {
            ExprSeq es;
            if (IsBVFunctionCall(e, smtName, out es))
            {
                lhs = es[0]; rhs = es[1];
                return true;
            }
            lhs = null; rhs = null;
            return false;
        }

        internal static bool IsBVAdd(Expr e, out Expr lhs, out Expr rhs) { return IsBVFunctionCall(e, "bvadd", out lhs, out rhs); }
        internal static bool IsBVMul(Expr e, out Expr lhs, out Expr rhs) { return IsBVFunctionCall(e, "bvmul", out lhs, out rhs); }

        internal Constant GetGroupSize(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return _GROUP_SIZE_X;
            if (dimension.Equals("Y")) return _GROUP_SIZE_Y;
            if (dimension.Equals("Z")) return _GROUP_SIZE_Z;
            Debug.Assert(false);
            return null;
        }

        internal Constant GetNumGroups(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return _NUM_GROUPS_X;
            if (dimension.Equals("Y")) return _NUM_GROUPS_Y;
            if (dimension.Equals("Z")) return _NUM_GROUPS_Z;
            Debug.Assert(false);
            return null;
        }

        internal Constant MakeThreadId(IToken tok, string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            string name = null;
            if (dimension.Equals("X")) name = _X.Name;
            if (dimension.Equals("Y")) name = _Y.Name;
            if (dimension.Equals("Z")) name = _Z.Name;
            Debug.Assert(name != null);
            return new Constant(tok, new TypedIdent(tok, name, GetTypeOfId(dimension)));
        }

        internal Constant MakeThreadId(IToken tok, string dimension, int number)
        {
            Constant resultWithoutThreadId = MakeThreadId(tok, dimension);
            return new Constant(tok, new TypedIdent(tok, resultWithoutThreadId.Name + "$" + number, GetTypeOfId(dimension)));
        }

        internal static Constant GetGroupId(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return _GROUP_X;
            if (dimension.Equals("Y")) return _GROUP_Y;
            if (dimension.Equals("Z")) return _GROUP_Z;
            Debug.Assert(false);
            return null;
        }

        internal static Constant MakeGroupId(string dimension, int number)
        {
            Constant resultWithoutThreadId = GetGroupId(dimension);
            return new Constant(Token.NoToken, new TypedIdent(Token.NoToken, resultWithoutThreadId.Name + "$" + number, GetTypeOfId(dimension)));
        }

        private static LiteralExpr Zero()
        {
            return new LiteralExpr(Token.NoToken, BigNum.FromInt(0));
        }

        internal static LiteralExpr ZeroBV()
        {
            return new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 32);
        }

        

        private void GenerateBarrierImplementation()
        {
            IToken tok = BarrierProcedure.tok;

            List<BigBlock> bigblocks = new List<BigBlock>();
            BigBlock barrierEntryBlock = new BigBlock(tok, "__BarrierImpl", new CmdSeq(), null, null);
            bigblocks.Add(barrierEntryBlock);

            Debug.Assert((BarrierProcedure.InParams.Length % 2) == 0);
            int paramsPerThread = BarrierProcedure.InParams.Length / 2;
            IdentifierExpr P1 = new IdentifierExpr(tok, new LocalVariable(tok, BarrierProcedure.InParams[0].TypedIdent));
            IdentifierExpr P2 = new IdentifierExpr(tok, new LocalVariable(tok, BarrierProcedure.InParams[paramsPerThread].TypedIdent));

            Expr LocalFence1 = MakeFenceExpr(BarrierProcedure.InParams[1]);
            Expr LocalFence2 = MakeFenceExpr(BarrierProcedure.InParams[paramsPerThread + 1]);

            Expr GlobalFence1 = MakeFenceExpr(BarrierProcedure.InParams[2]);
            Expr GlobalFence2 = MakeFenceExpr(BarrierProcedure.InParams[paramsPerThread + 2]);

            Expr DivergenceCondition = Expr.Imp(ThreadsInSameGroup(), Expr.Eq(P1, P2));

            Requires nonDivergenceRequires = new Requires(false, DivergenceCondition);
            nonDivergenceRequires.Attributes = new QKeyValue(Token.NoToken, "barrier_divergence",
              new List<object>(new object[] { }), null);
            BarrierProcedure.Requires.Add(nonDivergenceRequires);

            if (!CommandLineOptions.OnlyDivergence)
            {
                List<BigBlock> returnbigblocks = new List<BigBlock>();
                returnbigblocks.Add(new BigBlock(tok, "__Disabled", new CmdSeq(), null, new ReturnCmd(tok)));
                StmtList returnstatement = new StmtList(returnbigblocks, BarrierProcedure.tok);

                Expr IfGuard = Expr.Or(Expr.And(Expr.Not(P1), Expr.Not(P2)), Expr.And(ThreadsInSameGroup(), Expr.Or(Expr.Not(P1), Expr.Not(P2))));
                barrierEntryBlock.ec = new IfCmd(tok, IfGuard, returnstatement, null, null);
            }

            if(KernelArrayInfo.getGroupSharedArrays().Count > 0) {

                Expr IfGuard1 = Expr.And(P1, LocalFence1);
                Expr IfGuard2 = Expr.And(P2, LocalFence2);

                bigblocks.Add(new BigBlock(Token.NoToken, null, new CmdSeq(),
                    new IfCmd(Token.NoToken, IfGuard1, new StmtList(MakeResetBlocks(1, KernelArrayInfo.getGroupSharedArrays()), Token.NoToken), null, null),
                    null));
                bigblocks.Add(new BigBlock(Token.NoToken, null, new CmdSeq(),
                    new IfCmd(Token.NoToken, IfGuard2, new StmtList(MakeResetBlocks(2, KernelArrayInfo.getGroupSharedArrays()), Token.NoToken), null, null),
                    null));

                bigblocks.AddRange(MakeHavocBlocks(KernelArrayInfo.getGroupSharedArrays()));
            }

            if (KernelArrayInfo.getGlobalArrays().Count > 0)
            {
                Expr IfGuard1 = Expr.And(P1, GlobalFence1);
                Expr IfGuard2 = Expr.And(P2, GlobalFence2);

                bigblocks.Add(new BigBlock(Token.NoToken, null, new CmdSeq(),
                    new IfCmd(Token.NoToken, IfGuard1, new StmtList(MakeResetBlocks(1, KernelArrayInfo.getGlobalArrays()), Token.NoToken), null, null),
                    null));
                bigblocks.Add(new BigBlock(Token.NoToken, null, new CmdSeq(),
                    new IfCmd(Token.NoToken, IfGuard2, new StmtList(MakeResetBlocks(2, KernelArrayInfo.getGlobalArrays()), Token.NoToken), null, null),
                    null));

                bigblocks.AddRange(MakeHavocBlocks(KernelArrayInfo.getGlobalArrays()));
            }

            StmtList statements = new StmtList(bigblocks, BarrierProcedure.tok);
            Implementation BarrierImplementation = 
                new Implementation(BarrierProcedure.tok, BarrierProcedure.Name, new TypeVariableSeq(), 
                    BarrierProcedure.InParams, BarrierProcedure.OutParams, new VariableSeq(), statements);

            if (CommandLineOptions.Unstructured)
                BarrierImplementation.Resolve(ResContext);

            BarrierImplementation.AddAttribute("inline", new object[] { new LiteralExpr(tok, BigNum.FromInt(1)) });
            BarrierProcedure.AddAttribute("inline", new object[] { new LiteralExpr(tok, BigNum.FromInt(1)) });

            BarrierImplementation.Proc = BarrierProcedure;

            Program.TopLevelDeclarations.Add(BarrierImplementation);
        }

        private static NAryExpr MakeFenceExpr(Variable v) {
          return Expr.Eq(new IdentifierExpr(Token.NoToken, new LocalVariable(Token.NoToken, v.TypedIdent)), 
            new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 1));
        }

        private static Expr flagIsSet(Expr Flags, int flag)
        {
            return Expr.Eq(new BvExtractExpr(
                                    Token.NoToken, Flags, flag, flag - 1),
                                    new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 1));
        }

        private List<BigBlock> MakeResetBlocks(int Thread, ICollection<Variable> variables)
        {
            Debug.Assert(variables.Count > 0);
            List<BigBlock> ResetAndHavocBlocks = new List<BigBlock>();
            foreach (Variable v in variables)
            {
                ResetAndHavocBlocks.Add(RaceInstrumenter.MakeResetReadWriteSetStatements(v, Thread));
            }
            Debug.Assert(ResetAndHavocBlocks.Count > 0);
            return ResetAndHavocBlocks;
        }

        private List<BigBlock> MakeHavocBlocks(ICollection<Variable> variables) {
          Debug.Assert(variables.Count > 0);
          List<BigBlock> result = new List<BigBlock>();
          foreach (Variable v in variables) {
            if (!ArrayModelledAdversarially(v)) {
              result.Add(HavocSharedArray(v));
            }
          }
          return result;
        }

        public static bool HasZDimension(Variable v)
        {
            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;

                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    if (mt2.Result is MapType)
                    {
                        Debug.Assert(!((mt2.Result as MapType).Result is MapType));
                        return true;
                    }
                }
            }
            return false;
        }

        private BigBlock HavocSharedArray(Variable v)
        {
            return new BigBlock(Token.NoToken, null, 
              new CmdSeq(new Cmd[] { new HavocCmd(Token.NoToken, 
                new IdentifierExprSeq(new IdentifierExpr[] { new IdentifierExpr(Token.NoToken, v) })) }), null, null);
        }

        internal static bool ModifiesSetContains(IdentifierExprSeq Modifies, IdentifierExpr v)
        {
            foreach (IdentifierExpr ie in Modifies)
            {
                if (ie.Name.Equals(v.Name))
                {
                    return true;
                }
            }
            return false;
        }

        private void AbstractSharedState()
        {
          new AdversarialAbstraction(this).Abstract();
        }

        internal static string MakeOffsetVariableName(string Name, string AccessType)
        {
            return "_" + AccessType + "_OFFSET_" + Name;
        }

        internal static GlobalVariable MakeOffsetVariable(string Name, string ReadOrWrite)
        {
          return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, MakeOffsetVariableName(Name, ReadOrWrite), 
            Microsoft.Boogie.Type.GetBvType(32)));
        }

        internal static string MakeSourceVariableName(string Name, string AccessType)
        {
          return "_" + AccessType + "_SOURCE_" + Name;
        }

        internal static GlobalVariable MakeSourceVariable(string name, string ReadOrWrite)
        {
          return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, MakeSourceVariableName(name, ReadOrWrite),
            Microsoft.Boogie.Type.GetBvType(32)));
        }

        internal GlobalVariable FindOrCreateAccessHasOccurredVariable(string varName, string accessType)
        {
            string name = MakeAccessHasOccurredVariableName(varName, accessType) + "$1";
            foreach(Declaration D in Program.TopLevelDeclarations)
            {
                if(D is GlobalVariable && ((GlobalVariable)D).Name.Equals(name))
                {
                    return D as GlobalVariable;
                }
            }

            GlobalVariable result = new VariableDualiser(1, null, null).VisitVariable(
                MakeAccessHasOccurredVariable(varName, accessType)) as GlobalVariable;

            Program.TopLevelDeclarations.Add(result);
            return result;

        }

        internal GlobalVariable FindOrCreateOffsetVariable(string varName, string accessType)
        {
            string name = MakeOffsetVariableName(varName, accessType) + "$1";
            foreach (Declaration D in Program.TopLevelDeclarations)
            {
                if (D is GlobalVariable && ((GlobalVariable)D).Name.Equals(name))
                {
                    return D as GlobalVariable;
                }
            }

            GlobalVariable result = new VariableDualiser(1, null, null).VisitVariable(
                MakeOffsetVariable(varName, accessType)) as GlobalVariable;

            Program.TopLevelDeclarations.Add(result);
            return result;

        }

        internal GlobalVariable FindOrCreateSourceVariable(string varName, string accessType) {
          string name = MakeSourceVariableName(varName, accessType) + "$1";
          foreach (Declaration D in Program.TopLevelDeclarations) {
            if (D is GlobalVariable && ((GlobalVariable)D).Name.Equals(name)) {
              return D as GlobalVariable;
            }
          }

          GlobalVariable result = new VariableDualiser(1, null, null).VisitVariable(
              MakeSourceVariable(varName, accessType)) as GlobalVariable;

          Program.TopLevelDeclarations.Add(result);
          return result;

        }

        internal static GlobalVariable MakeAccessHasOccurredVariable(string varName, string accessType)
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, MakeAccessHasOccurredVariableName(varName, accessType), Microsoft.Boogie.Type.Bool));
        }

        internal static string MakeAccessHasOccurredVariableName(string varName, string accessType)
        {
            return "_" + accessType + "_HAS_OCCURRED_" + varName;
        }

        internal static IdentifierExpr MakeAccessHasOccurredExpr(string varName, string accessType)
        {
            return new IdentifierExpr(Token.NoToken, MakeAccessHasOccurredVariable(varName, accessType));
        }

        internal static bool IsIntOrBv32(Microsoft.Boogie.Type type)
        {
            return type.Equals(Microsoft.Boogie.Type.Int) || type.Equals(Microsoft.Boogie.Type.GetBvType(32));
        }

        private void PullOutNonLocalAccesses()
        {
            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Implementation)
                {
                    (d as Implementation).StructuredStmts = PullOutNonLocalAccesses((d as Implementation).StructuredStmts, (d as Implementation));
                }
            }
        }

        private void RemoveElseIfs()
        {
            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Implementation)
                {
                    (d as Implementation).StructuredStmts = RemoveElseIfs((d as Implementation).StructuredStmts);
                }
            }
        }

        private void RemoveRedundantReturns()
        {
            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Implementation)
                {
                    RemoveRedundantReturns((d as Implementation).StructuredStmts);
                }
            }
        }

        private StmtList RemoveElseIfs(StmtList stmtList)
        {
            Contract.Requires(stmtList != null);

            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(RemoveElseIfs(bodyBlock));
            }

            return result;
        }

        private void RemoveRedundantReturns(StmtList stmtList)
        {
            Contract.Requires(stmtList != null);

            BigBlock bb = stmtList.BigBlocks[stmtList.BigBlocks.Count - 1];

            if (bb.tc is ReturnCmd)
            {
                bb.tc = null;
            }
        }

        private BigBlock RemoveElseIfs(BigBlock bb)
        {
            BigBlock result = bb;
            if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;

                Debug.Assert(IfCommand.elseIf == null || IfCommand.elseBlock == null);

                if (IfCommand.elseIf != null)
                {
                    IfCommand.elseBlock = new StmtList(new List<BigBlock>(new BigBlock[] {
                        new BigBlock(bb.tok, null, new CmdSeq(), IfCommand.elseIf, null)
                    }), bb.tok);
                    IfCommand.elseIf = null;
                }

                IfCommand.thn = RemoveElseIfs(IfCommand.thn);
                if (IfCommand.elseBlock != null)
                {
                    IfCommand.elseBlock = RemoveElseIfs(IfCommand.elseBlock);
                }

            }
            else if (bb.ec is WhileCmd)
            {
                (bb.ec as WhileCmd).Body = RemoveElseIfs((bb.ec as WhileCmd).Body);
            }

            return result;
        }

        private StmtList PullOutNonLocalAccesses(StmtList stmtList, Implementation impl)
        {
            Contract.Requires(stmtList != null);

            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(PullOutNonLocalAccesses(bodyBlock, impl));
            }

            return result;
        }

        private BigBlock PullOutNonLocalAccesses(BigBlock bb, Implementation impl)
        {

            BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            foreach (Cmd c in bb.simpleCmds)
            {

                if (c is CallCmd)
                {
                    CallCmd call = c as CallCmd;

                    List<Expr> newIns = new List<Expr>();

                    for (int i = 0; i < call.Ins.Count; i++)
                    {
                        Expr e = call.Ins[i];

                        while (NonLocalAccessCollector.ContainsNonLocalAccess(e, KernelArrayInfo))
                        {
                            AssignCmd assignToTemp;
                            LocalVariable tempDecl;
                            e = ExtractLocalAccessToTemp(e, out assignToTemp, out tempDecl);
                            result.simpleCmds.Add(assignToTemp);
                            impl.LocVars.Add(tempDecl);
                        }

                        newIns.Add(e);

                    }

                    CallCmd newCall = new CallCmd(call.tok, call.callee, newIns, call.Outs);
                    newCall.Proc = call.Proc;
                    result.simpleCmds.Add(newCall);
                }
                else if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;

                    if (assign.Lhss.Zip(assign.Rhss, (lhs, rhs) =>
                            !NonLocalAccessCollector.ContainsNonLocalAccess(rhs, KernelArrayInfo) || 
                              (!NonLocalAccessCollector.ContainsNonLocalAccess(lhs, KernelArrayInfo) && 
                                NonLocalAccessCollector.IsNonLocalAccess(rhs, KernelArrayInfo))).All(b => b))
                    {
                        result.simpleCmds.Add(c);
                    }
                    else
                    {
                        Debug.Assert(assign.Lhss.Count == 1 && assign.Rhss.Count == 1);
                        AssignLhs lhs = assign.Lhss.ElementAt(0);
                        Expr rhs = assign.Rhss.ElementAt(0);
                        rhs = PullOutNonLocalAccessesIntoTemps(result, rhs, impl);
                        List<AssignLhs> newLhss = new List<AssignLhs>();
                        newLhss.Add(lhs);
                        List<Expr> newRhss = new List<Expr>();
                        newRhss.Add(rhs);
                        result.simpleCmds.Add(new AssignCmd(assign.tok, newLhss, newRhss));
                    }

                }
                else if (c is HavocCmd)
                {
                    result.simpleCmds.Add(c);
                }
                else if (c is AssertCmd)
                {
                    result.simpleCmds.Add(new AssertCmd(c.tok, PullOutNonLocalAccessesIntoTemps(result, (c as AssertCmd).Expr, impl)));
                }
                else if (c is AssumeCmd)
                {
                    result.simpleCmds.Add(new AssumeCmd(c.tok, PullOutNonLocalAccessesIntoTemps(result, (c as AssumeCmd).Expr, impl)));
                }
                else
                {
                    Console.WriteLine(c);
                    Debug.Assert(false);
                }
            }

            if (bb.ec is WhileCmd)
            {
                WhileCmd WhileCommand = bb.ec as WhileCmd;
                while (NonLocalAccessCollector.ContainsNonLocalAccess(WhileCommand.Guard, KernelArrayInfo))
                {
                    AssignCmd assignToTemp;
                    LocalVariable tempDecl;
                    WhileCommand.Guard = ExtractLocalAccessToTemp(WhileCommand.Guard, out assignToTemp, out tempDecl);
                    result.simpleCmds.Add(assignToTemp);
                    impl.LocVars.Add(tempDecl);
                }
                result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard, WhileCommand.Invariants, PullOutNonLocalAccesses(WhileCommand.Body, impl));
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;
                Debug.Assert(IfCommand.elseIf == null); // "else if" must have been eliminated by this phase
                while (NonLocalAccessCollector.ContainsNonLocalAccess(IfCommand.Guard, KernelArrayInfo))
                {
                    AssignCmd assignToTemp;
                    LocalVariable tempDecl;
                    IfCommand.Guard = ExtractLocalAccessToTemp(IfCommand.Guard, out assignToTemp, out tempDecl);
                    result.simpleCmds.Add(assignToTemp);
                    impl.LocVars.Add(tempDecl);
                }
                result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, PullOutNonLocalAccesses(IfCommand.thn, impl), IfCommand.elseIf, IfCommand.elseBlock != null ? PullOutNonLocalAccesses(IfCommand.elseBlock, impl) : null);
            }
            else if (bb.ec is BreakCmd)
            {
                result.ec = bb.ec;
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }

            return result;

        }

        private Expr PullOutNonLocalAccessesIntoTemps(BigBlock result, Expr e, Implementation impl)
        {
            while (NonLocalAccessCollector.ContainsNonLocalAccess(e, KernelArrayInfo))
            {
                AssignCmd assignToTemp;
                LocalVariable tempDecl;
                e = ExtractLocalAccessToTemp(e, out assignToTemp, out tempDecl);
                result.simpleCmds.Add(assignToTemp);
                impl.LocVars.Add(tempDecl);
            }
            return e;
        }

        private Expr ExtractLocalAccessToTemp(Expr rhs, out AssignCmd tempAssignment, out LocalVariable tempDeclaration)
        {
            NonLocalAccessExtractor extractor = new NonLocalAccessExtractor(TempCounter, KernelArrayInfo);
            TempCounter++;
            rhs = extractor.VisitExpr(rhs);
            tempAssignment = extractor.Assignment;
            tempDeclaration = extractor.Declaration;
            return rhs;
        }

        private void MakeKernelDualised()
        {

            List<Declaration> NewTopLevelDeclarations = new List<Declaration>();

            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Procedure)
                {

                    new KernelDualiser(this).DualiseProcedure(d as Procedure);

                    NewTopLevelDeclarations.Add(d as Procedure);

                    continue;

                }

                if (d is Implementation)
                {

                    new KernelDualiser(this).DualiseImplementation(d as Implementation, CommandLineOptions.Unstructured);

                    NewTopLevelDeclarations.Add(d as Implementation);

                    continue;

                }

                if (d is Variable && ((d as Variable).IsMutable || 
                    IsThreadLocalIdConstant(d as Variable) || 
                    IsGroupIdConstant(d as Variable))) {
                  var v = d as Variable;

                  if (KernelArrayInfo.getGlobalArrays().Contains(v)) {
                    NewTopLevelDeclarations.Add(v);
                    continue;
                  }

                  if (KernelArrayInfo.getGroupSharedArrays().Contains(v)) {
                    Variable newV = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken,
                        v.Name, new MapType(Token.NoToken, new TypeVariableSeq(), 
                        new TypeSeq(new Microsoft.Boogie.Type[] { Microsoft.Boogie.Type.Bool }),
                        v.TypedIdent.Type)));
                    newV.Attributes = v.Attributes;
                    NewTopLevelDeclarations.Add(newV);
                    continue;
                  }

                  NewTopLevelDeclarations.Add(new VariableDualiser(1, null, null).VisitVariable((Variable)v.Clone()));
                  if (!QKeyValue.FindBoolAttribute(v.Attributes, "race_checking")) {
                    NewTopLevelDeclarations.Add(new VariableDualiser(2, null, null).VisitVariable((Variable)v.Clone()));
                  }

                  continue;
                }

                NewTopLevelDeclarations.Add(d);

            }

            Program.TopLevelDeclarations = NewTopLevelDeclarations;

        }

        private void MakeKernelPredicated()
        {
            if (CommandLineOptions.Unstructured)
            {
                if (CommandLineOptions.SmartPredication)
                {
                    SmartBlockPredicator.Predicate(Program);
                }
                else
                {
                    BlockPredicator.Predicate(Program, /*createCandidateInvariants=*/CommandLineOptions.Inference);
                }
                return;
            }

            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Procedure)
                {
                    Procedure proc = d as Procedure;
                    IdentifierExpr enabled = new IdentifierExpr(proc.tok,
                        new LocalVariable(proc.tok, new TypedIdent(proc.tok, "_P", Microsoft.Boogie.Type.Bool)));
                    Expr predicateExpr;
                    if (!uniformityAnalyser.IsUniform(proc.Name))
                    {
                        // Add predicate to start of parameter list
                        VariableSeq NewIns = new VariableSeq();
                        NewIns.Add(enabled.Decl);
                        foreach (Variable v in proc.InParams)
                        {
                            NewIns.Add(v);
                        }
                        proc.InParams = NewIns;
                        predicateExpr = enabled;
                    }
                    else
                    {
                        predicateExpr = Expr.True;
                    }

                    RequiresSeq newRequires = new RequiresSeq();
                    foreach (Requires r in proc.Requires)
                    {
                        newRequires.Add(new Requires(r.Free, Predicator.ProcessEnabledIntrinsics(r.Condition, predicateExpr)));
                    }
                    proc.Requires = newRequires;

                    EnsuresSeq newEnsures = new EnsuresSeq();
                    foreach (Ensures e in proc.Ensures)
                    {
                        newEnsures.Add(new Ensures(e.Free, Predicator.ProcessEnabledIntrinsics(e.Condition, predicateExpr)));
                    }
                    proc.Ensures = newEnsures;

                }
                else if (d is Implementation)
                {
                    Implementation impl = d as Implementation;
                    new Predicator(this, !uniformityAnalyser.IsUniform(impl.Name)).transform
                        (impl);
                }
            }

        }

        private void CheckKernelParameters()
        {
            if (KernelProcedure.OutParams.Length != 0)
            {
                Error(KernelProcedure.tok, "Kernel should not take return anything");
            }
        }


        private int Check()
        {
            BarrierProcedure = FindOrCreateBarrierProcedure();
            KernelProcedure = CheckExactlyOneKernelProcedure();

            if (ErrorCount > 0)
            {
                return ErrorCount;
            }

            if (BarrierProcedure.InParams.Length != 2)
            {
                Error(BarrierProcedure, "Barrier procedure must take exactly two arguments");
            }
            else if (!BarrierProcedure.InParams[0].TypedIdent.Type.Equals(new BvType(1)))
            {
                Error(BarrierProcedure, "First argument to barrier procedure must have type bv1");
            }
            else if (!BarrierProcedure.InParams[1].TypedIdent.Type.Equals(new BvType(1))) {
              Error(BarrierProcedure, "Second argument to barrier procedure must have type bv1");
            }

            if (BarrierProcedure.OutParams.Length != 0)
            {
                Error(BarrierProcedure, "Barrier procedure must not return any results");
            }

            if (!FindNonLocalVariables())
            {
                return ErrorCount;
            }

            CheckKernelImplementation();
            return ErrorCount;
        }

        public static bool IsThreadLocalIdConstant(Variable variable)
        {
            return variable.Name.Equals(_X.Name) || variable.Name.Equals(_Y.Name) || variable.Name.Equals(_Z.Name);
        }

        public static bool IsGroupIdConstant(Variable variable)
        {
            return variable.Name.Equals(_GROUP_X.Name) || variable.Name.Equals(_GROUP_Y.Name) || variable.Name.Equals(_GROUP_Z.Name);
        }

        internal void AddCandidateInvariant(IRegion region, Expr e, string tag)
        {
            region.AddInvariant(Program.CreateCandidateInvariant(e, tag));
        }

        internal Implementation GetImplementation(string procedureName)
        {
            foreach (Declaration D in Program.TopLevelDeclarations)
            {
                if (D is Implementation && ((D as Implementation).Name == procedureName))
                {
                    return D as Implementation;
                }
            }
            Debug.Assert(false);
            return null;
        }


        internal bool ContainsBarrierCall(IRegion loop)
        {
            foreach (Cmd c in loop.Cmds())
            {
                if (c is CallCmd && ((c as CallCmd).Proc == BarrierProcedure))
                {
                    return true;
                }
            }

            return false;
        }



        internal bool ArrayModelledAdversarially(Variable v)
        {
            if (CommandLineOptions.AdversarialAbstraction)
            {
                return true;
            }
            if (CommandLineOptions.EqualityAbstraction)
            {
                return false;
            }
            return !arrayControlFlowAnalyser.MayAffectControlFlow(v.Name);
        }

        internal Expr GlobalIdExpr(string dimension)
        {
            return MakeBVAdd(MakeBVMul(
                            new IdentifierExpr(Token.NoToken, GetGroupId(dimension)), new IdentifierExpr(Token.NoToken, GetGroupSize(dimension))),
                                new IdentifierExpr(Token.NoToken, MakeThreadId(Token.NoToken, dimension)));
        }

        internal IRegion RootRegion(Implementation Impl)
        {
          if (CommandLineOptions.Unstructured)
              return new UnstructuredRegion(Program, Impl);
          else
              return new StructuredRegion(Impl);
        }


        public static bool IsGivenConstant(Expr e, Constant c)
        {
            if (!(e is IdentifierExpr))
                return false;

            var varName = ((IdentifierExpr)e).Decl.Name;
            return (StripThreadIdentifier(varName) == StripThreadIdentifier(c.Name));
        }

        public bool SubstIsGivenConstant(Implementation impl, Expr e, Constant c)
        {
            if (!(e is IdentifierExpr))
                return false;
            e = varDefAnalyses[impl].SubstDefinitions(e, impl.Name);
            return IsGivenConstant(e, c);
        }

        public Constant GetLocalIdConst(int dim)
        {
            switch (dim)
            {
                case 0:  return _X;
                case 1:  return _Y;
                case 2:  return _Z;
                default: Debug.Assert(false);
                         return null;
            }
        }

        public Constant GetGroupIdConst(int dim)
        {
            switch (dim)
            {
                case 0:  return _GROUP_X;
                case 1:  return _GROUP_Y;
                case 2:  return _GROUP_Z;
                default: Debug.Assert(false);
                         return null;
            }
        }

        public Constant GetGroupSizeConst(int dim)
        {
            switch (dim)
            {
                case 0:  return _GROUP_SIZE_X;
                case 1:  return _GROUP_SIZE_Y;
                case 2:  return _GROUP_SIZE_Z;
                default: Debug.Assert(false);
                         return null;
            }
        }

        public bool IsLocalId(Expr e, int dim, Implementation impl)
        {
            return SubstIsGivenConstant(impl, e, GetLocalIdConst(dim));
        }

        public bool IsGlobalId(Expr e, int dim, Implementation impl)
        {
            e = varDefAnalyses[impl].SubstDefinitions(e, impl.Name);

            if (e is NAryExpr && (e as NAryExpr).Fun.FunctionName.Equals("BV32_ADD"))
            {
                NAryExpr nary = e as NAryExpr;
                Constant localId = GetLocalIdConst(dim);

                if (IsGivenConstant(nary.Args[1], localId))
                {
                    return IsGroupIdTimesGroupSize(nary.Args[0], dim);
                }

                if (IsGivenConstant(nary.Args[0], localId))
                {
                    return IsGroupIdTimesGroupSize(nary.Args[1], dim);
                }
            }

            return false;
        }

        private bool IsGroupIdTimesGroupSize(Expr expr, int dim)
        {
            if (expr is NAryExpr && (expr as NAryExpr).Fun.FunctionName.Equals("BV32_MUL"))
            {
                NAryExpr innerNary = expr as NAryExpr;

                if (IsGroupIdAndSize(dim, innerNary.Args[0], innerNary.Args[1]))
                {
                    return true;
                }

                if (IsGroupIdAndSize(dim, innerNary.Args[1], innerNary.Args[0]))
                {
                    return true;
                }
            }
            return false;
        }

        private bool IsGroupIdAndSize(int dim, Expr maybeGroupId, Expr maybeGroupSize)
        {
            return IsGivenConstant(maybeGroupId, GetGroupIdConst(dim)) &&
                   IsGivenConstant(maybeGroupSize, GetGroupSizeConst(dim));
        }

        internal Expr MaybeDualise(Expr e, int id, string procName)
        {
            if (id == 0)
                return e;
            else
                return (Expr)new VariableDualiser(id, uniformityAnalyser, procName).Visit(e.Clone());
        }

        internal static bool IsConstantInCurrentRegion(IdentifierExpr expr) {
          return (expr.Decl is Constant) ||
                 (expr.Decl is Formal && ((Formal)expr.Decl).InComing);
        }
    
    }


}
