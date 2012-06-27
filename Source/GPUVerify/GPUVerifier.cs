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

        public INonLocalState NonLocalState = new NonLocalStateLists();

        private HashSet<string> ReservedNames = new HashSet<string>();

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
        public MayBeLocalIdPlusConstantAnalyser mayBeTidPlusConstantAnalyser;
        public MayBeGlobalIdPlusConstantAnalyser mayBeGidPlusConstantAnalyser;
        public MayBePowerOfTwoAnalyser mayBePowerOfTwoAnalyser;
        public LiveVariableAnalyser liveVariableAnalyser;
        public ArrayControlFlowAnalyser arrayControlFlowAnalyser;
        public Dictionary<Implementation, VariableDefinitionAnalysis> varDefAnalyses;

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
                                  new VariableSeq(), new VariableSeq(),
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
                if (D is Variable && (D as Variable).IsMutable)
                {
                    if (!ReservedNames.Contains((D as Variable).Name))
                    {
                        if (QKeyValue.FindBoolAttribute(D.Attributes, "group_shared"))
                        {
                            NonLocalState.getGroupSharedVariables().Add(D as Variable);
                        }
                        else if(QKeyValue.FindBoolAttribute(D.Attributes, "global"))
                        {
                            NonLocalState.getGlobalVariables().Add(D as Variable);
                        }
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

            AddStartAndEndBarriers();

            PullOutNonLocalAccesses();
        }

        

        

        internal void doit()
        {
            if (CommandLineOptions.Unstructured)
            {
                Microsoft.Boogie.CommandLineOptions.Clo.PrintUnstructured = 2;
            }

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_original");
            }

            preProcess();

            DoLiveVariableAnalysis();

            DoUniformityAnalysis();

            DoVariableDefinitionAnalysis();

            DoMayBeIdPlusConstantAnalysis();

            DoMayBePowerOfTwoAnalysis();

            DoArrayControlFlowAnalysis();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_preprocessed");
            }

            if (RaceInstrumenter.AddRaceCheckingInstrumentation() == false)
            {
                return;
            }

            ProcessAccessInvariants();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_instrumented");
            }

            AbstractSharedState();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_abstracted");
            }

            MakeKernelPredicated();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_predicated");
            }

            MakeKernelDualised();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_dualised");
            }

            ProcessCrossThreadInvariants();

            if (CommandLineOptions.ShowStages)
            {
                emitProgram(outputFilename + "_cross_thread_invariants");
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


            if (CommandLineOptions.DividedAccesses)
            {

                Program p = GPUVerify.ParseBoogieProgram(new List<string>(new string[] { outputFilename + ".bpl" }), true);
                ResolutionContext rc = new ResolutionContext(null);
                p.Resolve(rc);
                p.Typecheck();

                Contract.Assert(p != null);

                Implementation impl = null;

                {
                    GPUVerifier tempGPUV = new GPUVerifier("not_used", p, rc, new NullRaceInstrumenter(), true);
                    tempGPUV.KernelProcedure = tempGPUV.CheckExactlyOneKernelProcedure();
                    tempGPUV.GetKernelImplementation();
                    impl = tempGPUV.KernelImplementation;
                }

                Contract.Assert(impl != null);

                NoConflictingAccessOptimiser opt = new NoConflictingAccessOptimiser(impl);
                Contract.Assert(opt.NumLogCalls() <= 2);
                if (opt.NumLogCalls() == 2 && !opt.HasConflicting())
                {
                    FileInfo f = new FileInfo(outputFilename);
                    
                    string newName = f.Directory.FullName + "\\" + "NO_CONFLICTS_" + f.Name + ".bpl";
                    //File.Delete(newName);
                    if (File.Exists(newName))
                    {
                        File.Delete(newName);
                    }
                    File.Move(outputFilename + ".bpl", newName);
                    //Console.WriteLine("Renamed " + ouputFilename + "; no conflicting accesses (that are not already tested by other output files).");
                }

               
            }

        }

        private void DoMayBePowerOfTwoAnalysis()
        {
            mayBePowerOfTwoAnalyser = new MayBePowerOfTwoAnalyser(this);
            mayBePowerOfTwoAnalyser.Analyse();
        }

        private void DoMayBeIdPlusConstantAnalysis()
        {
            mayBeTidPlusConstantAnalyser = new MayBeLocalIdPlusConstantAnalyser(this);
            mayBeTidPlusConstantAnalyser.Analyse();
            mayBeGidPlusConstantAnalyser = new MayBeGlobalIdPlusConstantAnalyser(this);
            mayBeGidPlusConstantAnalyser.Analyse();
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

        private void ProcessAccessInvariants()
        {
            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Procedure)
                {
                    Procedure p = d as Procedure;
                    p.Requires = ProcessAccessInvariants(p.Requires);
                    p.Ensures = ProcessAccessInvariants(p.Ensures);
                }

                if (d is Implementation)
                {
                    Implementation i = d as Implementation;
                    ProcessAccessInvariants(i.StructuredStmts);
                }
            }
        }

        private void ProcessAccessInvariants(StmtList stmtList)
        {
            
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                ProcessAccessInvariants(bb);
            }
        }

        private void ProcessAccessInvariants(BigBlock bb)
        {
            CmdSeq newCommands = new CmdSeq();

            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is AssertCmd)
                {
                    newCommands.Add(new AssertCmd(c.tok, new AccessInvariantProcessor().VisitExpr((c as AssertCmd).Expr.Clone() as Expr)));
                }
                else if (c is AssumeCmd)
                {
                    newCommands.Add(new AssumeCmd(c.tok, new AccessInvariantProcessor().VisitExpr((c as AssumeCmd).Expr.Clone() as Expr)));
                }
                else
                {
                    newCommands.Add(c);
                }
            }

            bb.simpleCmds = newCommands;

            if (bb.ec is WhileCmd)
            {
                WhileCmd whileCmd = bb.ec as WhileCmd;
                whileCmd.Invariants = ProcessAccessInvariants(whileCmd.Invariants);
                ProcessAccessInvariants(whileCmd.Body);
            }
            else if (bb.ec is IfCmd)
            {
                ProcessAccessInvariants((bb.ec as IfCmd).thn);
                if ((bb.ec as IfCmd).elseBlock != null)
                {
                    ProcessAccessInvariants((bb.ec as IfCmd).elseBlock);
                }
            }
        }

        private List<PredicateCmd> ProcessAccessInvariants(List<PredicateCmd> invariants)
        {
            List<PredicateCmd> result = new List<PredicateCmd>();

            foreach (PredicateCmd p in invariants)
            {
                PredicateCmd newP = new AssertCmd(p.tok, new AccessInvariantProcessor().VisitExpr(p.Expr.Clone() as Expr));
                newP.Attributes = p.Attributes;
                result.Add(newP);
            }

            return result;
        }

        private EnsuresSeq ProcessAccessInvariants(EnsuresSeq ensuresSeq)
        {
            EnsuresSeq result = new EnsuresSeq();
            foreach (Ensures e in ensuresSeq)
            {
                result.Add(new Ensures(e.Free, new AccessInvariantProcessor().VisitExpr(e.Condition.Clone() as Expr)));
            }
            return result;
        }

        private RequiresSeq ProcessAccessInvariants(RequiresSeq requiresSeq)
        {
            RequiresSeq result = new RequiresSeq();
            foreach (Requires r in requiresSeq)
            {
                result.Add(new Requires(r.Free, new AccessInvariantProcessor().VisitExpr(r.Condition.Clone() as Expr)));
            }
            return result;
        }

        private void ProcessCrossThreadInvariants()
        {
            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Procedure)
                {
                    Procedure p = d as Procedure;
                    p.Requires = new CrossThreadInvariantProcessor(this, p.Name).ProcessCrossThreadInvariants(p.Requires);
                    p.Ensures = new CrossThreadInvariantProcessor(this, p.Name).ProcessCrossThreadInvariants(p.Ensures);
                }
                if (d is Implementation)
                {
                    Implementation i = d as Implementation;
                    new CrossThreadInvariantProcessor(this, i.Name).ProcessCrossThreadInvariants(i.StructuredStmts);
                }

            }
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

                    new LoopInvariantGenerator(this, Impl).instrument(UserSuppliedInvariants);

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


        internal static bool IsPredicateOrTemp(string lv)
        {
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

        

        public Microsoft.Boogie.Type GetTypeOfIdX()
        {
            Contract.Requires(_X != null);
            return _X.TypedIdent.Type;
        }

        public Microsoft.Boogie.Type GetTypeOfIdY()
        {
            Contract.Requires(_Y != null);
            return _Y.TypedIdent.Type;
        }

        public Microsoft.Boogie.Type GetTypeOfIdZ()
        {
            Contract.Requires(_Z != null);
            return _Z.TypedIdent.Type;
        }

        public Microsoft.Boogie.Type GetTypeOfId(string dimension)
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

        private void AddStartAndEndBarriers()
        {
            CallCmd FirstBarrier = new CallCmd(KernelImplementation.tok, BarrierProcedure.Name, new ExprSeq(), new IdentifierExprSeq());
            CallCmd LastBarrier = new CallCmd(KernelImplementation.tok, BarrierProcedure.Name, new ExprSeq(), new IdentifierExprSeq());

            FirstBarrier.Proc = KernelProcedure;
            LastBarrier.Proc = KernelProcedure;

            CmdSeq newCommands = new CmdSeq();
            newCommands.Add(FirstBarrier);
            foreach (Cmd c in KernelImplementation.StructuredStmts.BigBlocks[0].simpleCmds)
            {
                newCommands.Add(c);
            }
            KernelImplementation.StructuredStmts.BigBlocks[0].simpleCmds = newCommands;

        }

        private void GenerateStandardKernelContract()
        {
            RaceInstrumenter.AddKernelPrecondition();

            IToken tok = KernelImplementation.tok;

            GeneratePreconditionsForDimension(tok, "X");
            GeneratePreconditionsForDimension(tok, "Y");
            GeneratePreconditionsForDimension(tok, "Z");

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

                if (CommandLineOptions.InterGroupRaceChecking)
                {
                    Proc.Requires.Add(new Requires(false, Expr.Imp(ThreadsInSameGroup(), DistinctLocalIds)));

                }
                else
                {
                    Proc.Requires.Add(new Requires(false, DistinctLocalIds));
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

        internal Expr ThreadsInSameGroup()
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
                    GroupSizePositive = MakeBVSgt(new IdentifierExpr(tok, GetGroupSize(dimension)), ZeroBV(tok));
                    NumGroupsPositive = MakeBVSgt(new IdentifierExpr(tok, GetNumGroups(dimension)), ZeroBV(tok));
                    GroupIdNonNegative = MakeBVSge(new IdentifierExpr(tok, GetGroupId(dimension)), ZeroBV(tok));
                    GroupIdLessThanNumGroups = MakeBVSlt(new IdentifierExpr(tok, GetGroupId(dimension)), new IdentifierExpr(tok, GetNumGroups(dimension)));
                }
                else
                {
                    GroupSizePositive = Expr.Gt(new IdentifierExpr(tok, GetGroupSize(dimension)), Zero(tok));
                    NumGroupsPositive = Expr.Gt(new IdentifierExpr(tok, GetNumGroups(dimension)), Zero(tok));
                    GroupIdNonNegative = Expr.Ge(new IdentifierExpr(tok, GetGroupId(dimension)), Zero(tok));
                    GroupIdLessThanNumGroups = Expr.Lt(new IdentifierExpr(tok, GetGroupId(dimension)), new IdentifierExpr(tok, GetNumGroups(dimension)));
                }

                Proc.Requires.Add(new Requires(false, GroupSizePositive));
                Proc.Requires.Add(new Requires(false, NumGroupsPositive));
                if (CommandLineOptions.InterGroupRaceChecking)
                {
                    Proc.Requires.Add(new Requires(false, new VariableDualiser(1, null, null).VisitExpr(GroupIdNonNegative)));
                    Proc.Requires.Add(new Requires(false, new VariableDualiser(2, null, null).VisitExpr(GroupIdNonNegative)));
                    Proc.Requires.Add(new Requires(false, new VariableDualiser(1, null, null).VisitExpr(GroupIdLessThanNumGroups)));
                    Proc.Requires.Add(new Requires(false, new VariableDualiser(2, null, null).VisitExpr(GroupIdLessThanNumGroups)));
                }
                else
                {
                    Proc.Requires.Add(new Requires(false, GroupIdNonNegative));
                    Proc.Requires.Add(new Requires(false, GroupIdLessThanNumGroups));
                }

                Expr ThreadIdNonNegative =
                    GetTypeOfId(dimension).Equals(Microsoft.Boogie.Type.GetBvType(32)) ?
                            MakeBVSge(new IdentifierExpr(tok, MakeThreadId(tok, dimension)), ZeroBV(tok))
                    :
                            Expr.Ge(new IdentifierExpr(tok, MakeThreadId(tok, dimension)), Zero(tok));
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

        internal Constant GetGroupId(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return _GROUP_X;
            if (dimension.Equals("Y")) return _GROUP_Y;
            if (dimension.Equals("Z")) return _GROUP_Z;
            Debug.Assert(false);
            return null;
        }

        internal Constant MakeGroupId(string dimension, int number)
        {
            Constant resultWithoutThreadId = GetGroupId(dimension);
            return new Constant(Token.NoToken, new TypedIdent(Token.NoToken, resultWithoutThreadId.Name + "$" + number, GetTypeOfId(dimension)));
        }

        private static LiteralExpr Zero(IToken tok)
        {
            return new LiteralExpr(tok, BigNum.FromInt(0));
        }

        private static LiteralExpr ZeroBV(IToken tok)
        {
            return new LiteralExpr(tok, BigNum.FromInt(0), 32);
        }

        

        private void GenerateBarrierImplementation()
        {
            IToken tok = BarrierProcedure.tok;

            List<BigBlock> bigblocks = new List<BigBlock>();
            BigBlock checkNonDivergence = new BigBlock(tok, "__BarrierImpl", new CmdSeq(), null, null);
            bigblocks.Add(checkNonDivergence);

            IdentifierExpr P1 = new IdentifierExpr(tok, new LocalVariable(tok, BarrierProcedure.InParams[0].TypedIdent));
            IdentifierExpr P2 = new IdentifierExpr(tok, new LocalVariable(tok, BarrierProcedure.InParams[1].TypedIdent));

            Expr DivergenceCondition = Expr.Eq(P1, P2);
            if (CommandLineOptions.InterGroupRaceChecking)
            {
                DivergenceCondition = Expr.Imp(ThreadsInSameGroup(), DivergenceCondition);
            }

            checkNonDivergence.simpleCmds.Add(new AssertCmd(tok, DivergenceCondition));

            if (!CommandLineOptions.OnlyDivergence)
            {
                List<BigBlock> returnbigblocks = new List<BigBlock>();
                returnbigblocks.Add(new BigBlock(tok, "__Disabled", new CmdSeq(), null, new ReturnCmd(tok)));
                StmtList returnstatement = new StmtList(returnbigblocks, BarrierProcedure.tok);
                // We make this an "Or", not an "And", because "And" is implied by the assertion that the variables
                // are equal, together with the "Or".  The weaker "Or" ensures that many auxiliary assertions will not
                // fail if divergence has not been proved.
                checkNonDivergence.ec = new IfCmd(tok, Expr.Or(Expr.Not(P1), Expr.Not(P2)), returnstatement, null, null);
            }

            if (CommandLineOptions.InterGroupRaceChecking)
            {
                bigblocks.Add(new BigBlock(Token.NoToken, null, new CmdSeq(),
                    new IfCmd(Token.NoToken, P1, new StmtList(MakeResetAndHavocBlocks(1), Token.NoToken), null, null),
                    null));
                bigblocks.Add(new BigBlock(Token.NoToken, null, new CmdSeq(),
                    new IfCmd(Token.NoToken, P2, new StmtList(MakeResetAndHavocBlocks(2), Token.NoToken), null, null),
                    null));
            }
            else
            {
                foreach (BigBlock bb in MakeResetAndHavocBlocks(1))
                {
                    bigblocks.Add(bb);
                }
                foreach (BigBlock bb in MakeResetAndHavocBlocks(2))
                {
                    bigblocks.Add(bb);
                }
            }

            foreach (Variable v in NonLocalState.getAllNonLocalVariables())
            {
                if (!ArrayModelledAdversarially(v))
                {
                    bigblocks.Add(AssumeEqualityBetweenSharedArrays(v, P1, P2));
                }
            }

            StmtList statements = new StmtList(bigblocks, BarrierProcedure.tok);
            Implementation BarrierImplementation = new Implementation(BarrierProcedure.tok, BarrierProcedure.Name, new TypeVariableSeq(), BarrierProcedure.InParams, BarrierProcedure.OutParams, new VariableSeq(), statements);

            if (CommandLineOptions.Unstructured)
                BarrierImplementation.Resolve(ResContext);

            BarrierImplementation.AddAttribute("inline", new object[] { new LiteralExpr(tok, BigNum.FromInt(1)) });
            BarrierProcedure.AddAttribute("inline", new object[] { new LiteralExpr(tok, BigNum.FromInt(1)) });

            BarrierImplementation.Proc = BarrierProcedure;

            Program.TopLevelDeclarations.Add(BarrierImplementation);
        }

        private List<BigBlock> MakeResetAndHavocBlocks(int Thread)
        {
            List<BigBlock> ResetAndHavocBlocks = new List<BigBlock>();
            foreach (Variable v in NonLocalState.getAllNonLocalVariables())
            {
                ResetAndHavocBlocks.Add(RaceInstrumenter.MakeResetReadWriteSetStatements(v, Thread));
                if (!ArrayModelledAdversarially(v))
                {
                    ResetAndHavocBlocks.Add(HavocSharedArray(v, Thread));
                }
            }
            return ResetAndHavocBlocks;
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

        public static bool HasYDimension(Variable v)
        {
            return v.TypedIdent.Type is MapType && (v.TypedIdent.Type as MapType).Result is MapType;
        }

        public static bool HasXDimension(Variable v)
        {
            return v.TypedIdent.Type is MapType;
        }

        private BigBlock HavocSharedArray(Variable v, int thread)
        {
            IdentifierExpr vForThread = new IdentifierExpr(Token.NoToken, new VariableDualiser(thread, null, null).VisitVariable(v.Clone() as Variable));
            return new BigBlock(Token.NoToken, null, new CmdSeq(new Cmd[] { new HavocCmd(Token.NoToken, new IdentifierExprSeq(new IdentifierExpr[] { vForThread })) }), null, null);
        }

        private BigBlock AssumeEqualityBetweenSharedArrays(Variable v, Expr P1, Expr P2)
        {
            IdentifierExpr v1 = new IdentifierExpr(Token.NoToken, new VariableDualiser(1, null, null).VisitVariable(v.Clone() as Variable));
            IdentifierExpr v2 = new IdentifierExpr(Token.NoToken, new VariableDualiser(2, null, null).VisitVariable(v.Clone() as Variable));

            Expr AssumeGuard = Expr.Eq(v1, v2);

            if (CommandLineOptions.InterGroupRaceChecking)
            {
                AssumeGuard = Expr.Imp(ThreadsInSameGroup(), AssumeGuard);
            }

            return new BigBlock(Token.NoToken, null, new CmdSeq(new Cmd[] { new AssumeCmd(Token.NoToken, AssumeGuard) }), null, null);
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
            List<Declaration> NewTopLevelDeclarations = new List<Declaration>();

            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Variable && NonLocalState.Contains(d as Variable) && ArrayModelledAdversarially(d as Variable))
                {
                    continue;
                }

                if (d is Implementation)
                {
                    PerformFullSharedStateAbstraction(d as Implementation);
                }

                if (d is Procedure)
                {
                    PerformFullSharedStateAbstraction(d as Procedure);
                }

                NewTopLevelDeclarations.Add(d);

            }

            Program.TopLevelDeclarations = NewTopLevelDeclarations;

        }

        private void PerformFullSharedStateAbstraction(Procedure proc)
        {
            IdentifierExprSeq NewModifies = new IdentifierExprSeq();

            foreach (IdentifierExpr e in proc.Modifies)
            {
                if (!NonLocalState.Contains(e.Decl) || !ArrayModelledAdversarially(e.Decl))
                {
                    NewModifies.Add(e);
                }
            }

            proc.Modifies = NewModifies;

        }

        private void PerformFullSharedStateAbstraction(Implementation impl)
        {
            VariableSeq NewLocVars = new VariableSeq();

            foreach (Variable v in impl.LocVars)
            {
                Debug.Assert(!NonLocalState.getGroupSharedVariables().Contains(v));
                NewLocVars.Add(v);
            }

            impl.LocVars = NewLocVars;

            if (CommandLineOptions.Unstructured)
                impl.Blocks = impl.Blocks.Select(PerformFullSharedStateAbstraction).ToList();
            else
                impl.StructuredStmts = PerformFullSharedStateAbstraction(impl.StructuredStmts);
        }


        private StmtList PerformFullSharedStateAbstraction(StmtList stmtList)
        {
            Contract.Requires(stmtList != null);

            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(PerformFullSharedStateAbstraction(bodyBlock));
            }
            return result;
        }

        private CmdSeq PerformFullSharedStateAbstraction(CmdSeq cs)
        {
            var result = new CmdSeq();

            foreach (Cmd c in cs)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;

                    var lhss = new List<AssignLhs>(); 
                    var rhss = new List<Expr>(); 

                    for (int i = 0; i != assign.Lhss.Count; i++)
                    {
                        AssignLhs lhs = assign.Lhss[i];
                        Expr rhs = assign.Rhss[i];
                        ReadCollector rc = new ReadCollector(NonLocalState);
                        rc.Visit(rhs);

                        bool foundAdversarial = false;
                        foreach (AccessRecord ar in rc.accesses)
                        {
                            if (ArrayModelledAdversarially(ar.v))
                            {
                                foundAdversarial = true;
                                break;
                            }
                        }

                        if (foundAdversarial)
                        {
                            Debug.Assert(lhs is SimpleAssignLhs);
                            result.Add(new HavocCmd(c.tok, new IdentifierExprSeq(new IdentifierExpr[] { (lhs as SimpleAssignLhs).AssignedVariable })));
                            continue;
                        }

                        WriteCollector wc = new WriteCollector(NonLocalState);
                        wc.Visit(lhs);
                        if (wc.GetAccess() != null && ArrayModelledAdversarially(wc.GetAccess().v))
                        {
                            continue; // Just remove the write
                        }

                        lhss.Add(lhs);
                        rhss.Add(rhs);
                    }

                    if (lhss.Count != 0)
                    {
                        result.Add(new AssignCmd(assign.tok, lhss, rhss));
                    }
                    continue;
                }
                result.Add(c);
            }

            return result;
        }

        private Block PerformFullSharedStateAbstraction(Block b)
        {
            b.Cmds = PerformFullSharedStateAbstraction(b.Cmds);
            return b;
        }

        private BigBlock PerformFullSharedStateAbstraction(BigBlock bb)
        {
            BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            result.simpleCmds = PerformFullSharedStateAbstraction(bb.simpleCmds);

            if (bb.ec is WhileCmd)
            {
                WhileCmd WhileCommand = bb.ec as WhileCmd;
                result.ec = 
                    new WhileCmd(WhileCommand.tok, WhileCommand.Guard, WhileCommand.Invariants, PerformFullSharedStateAbstraction(WhileCommand.Body));
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;
                Debug.Assert(IfCommand.elseIf == null);
                result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, PerformFullSharedStateAbstraction(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? PerformFullSharedStateAbstraction(IfCommand.elseBlock) : null);
            }
            else
            {
                Debug.Assert(bb.ec == null || bb.ec is BreakCmd);
            }

            return result;

        }






        internal static GlobalVariable MakeOffsetZVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_OFFSET_Z_" + v.Name, IndexTypeOfZDimension(v)));
        }

        internal static GlobalVariable MakeOffsetYVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_OFFSET_Y_" + v.Name, IndexTypeOfYDimension(v)));
        }

        internal static GlobalVariable MakeOffsetXVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_OFFSET_X_" + v.Name, IndexTypeOfXDimension(v)));
        }

        public static Microsoft.Boogie.Type IndexTypeOfZDimension(Variable v)
        {
            Contract.Requires(HasZDimension(v));
            MapType mt = v.TypedIdent.Type as MapType;
            MapType mt2 = mt.Result as MapType;
            MapType mt3 = mt2.Result as MapType;
            return mt3.Arguments[0];
        }

        public static Microsoft.Boogie.Type IndexTypeOfYDimension(Variable v)
        {
            Contract.Requires(HasYDimension(v));
            MapType mt = v.TypedIdent.Type as MapType;
            MapType mt2 = mt.Result as MapType;
            return mt2.Arguments[0];
        }

        public static Microsoft.Boogie.Type IndexTypeOfXDimension(Variable v)
        {
            Contract.Requires(HasXDimension(v));
            MapType mt = v.TypedIdent.Type as MapType;
            return mt.Arguments[0];
        }

        private void AddRaceCheckingDeclarations(Variable v)
        {
            IdentifierExprSeq newVars = new IdentifierExprSeq();

            Variable ReadHasOccurred = MakeAccessHasOccurredVariable(v.Name, "READ");
            Variable WriteHasOccurred = MakeAccessHasOccurredVariable(v.Name, "WRITE");

            newVars.Add(new IdentifierExpr(v.tok, ReadHasOccurred));
            newVars.Add(new IdentifierExpr(v.tok, WriteHasOccurred));

            Program.TopLevelDeclarations.Add(ReadHasOccurred);
            Program.TopLevelDeclarations.Add(WriteHasOccurred);
            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);
                Debug.Assert(IsIntOrBv32(mt.Arguments[0]));

                Variable ReadOffsetX = MakeOffsetXVariable(v, "READ");
                Variable WriteOffsetX = MakeOffsetXVariable(v, "WRITE");
                newVars.Add(new IdentifierExpr(v.tok, ReadOffsetX));
                newVars.Add(new IdentifierExpr(v.tok, WriteOffsetX));
                Program.TopLevelDeclarations.Add(ReadOffsetX);
                Program.TopLevelDeclarations.Add(WriteOffsetX);

                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(IsIntOrBv32(mt2.Arguments[0]));

                    Variable ReadOffsetY = MakeOffsetYVariable(v, "READ");
                    Variable WriteOffsetY = MakeOffsetYVariable(v, "WRITE");
                    newVars.Add(new IdentifierExpr(v.tok, ReadOffsetY));
                    newVars.Add(new IdentifierExpr(v.tok, WriteOffsetY));
                    Program.TopLevelDeclarations.Add(ReadOffsetY);
                    Program.TopLevelDeclarations.Add(WriteOffsetY);

                    if (mt2.Result is MapType)
                    {
                        MapType mt3 = mt2.Arguments[0] as MapType;
                        Debug.Assert(mt3.Arguments.Length == 1);
                        Debug.Assert(IsIntOrBv32(mt3.Arguments[0]));
                        Debug.Assert(!(mt3.Result is MapType));

                        Variable ReadOffsetZ = MakeOffsetZVariable(v, "READ");
                        Variable WriteOffsetZ = MakeOffsetZVariable(v, "WRITE");
                        newVars.Add(new IdentifierExpr(v.tok, ReadOffsetZ));
                        newVars.Add(new IdentifierExpr(v.tok, WriteOffsetZ));
                        Program.TopLevelDeclarations.Add(ReadOffsetZ);
                        Program.TopLevelDeclarations.Add(WriteOffsetZ);

                    }
                }
            }

            foreach (IdentifierExpr e in newVars)
            {
                KernelProcedure.Modifies.Add(e);
            }
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

                        while (NonLocalAccessCollector.ContainsNonLocalAccess(e, NonLocalState))
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
                            !NonLocalAccessCollector.ContainsNonLocalAccess(rhs, NonLocalState) || 
                              (!NonLocalAccessCollector.ContainsNonLocalAccess(lhs, NonLocalState) && 
                                NonLocalAccessCollector.IsNonLocalAccess(rhs, NonLocalState))).All(b => b))
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
                while (NonLocalAccessCollector.ContainsNonLocalAccess(WhileCommand.Guard, NonLocalState))
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
                while (NonLocalAccessCollector.ContainsNonLocalAccess(IfCommand.Guard, NonLocalState))
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
            while (NonLocalAccessCollector.ContainsNonLocalAccess(e, NonLocalState))
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
            NonLocalAccessExtractor extractor = new NonLocalAccessExtractor(TempCounter, NonLocalState);
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

                if (d is Variable && ((d as Variable).IsMutable || IsThreadLocalIdConstant(d as Variable)
                    || (CommandLineOptions.InterGroupRaceChecking && IsGroupIdConstant(d as Variable) ) ))
                {
                    NewTopLevelDeclarations.Add(new VariableDualiser(1, null, null).VisitVariable((Variable)d.Clone()));
                    NewTopLevelDeclarations.Add(new VariableDualiser(2, null, null).VisitVariable((Variable)d.Clone()));

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
                BlockPredicator.Predicate(Program, /*createCandidateInvariants=*/CommandLineOptions.Inference);
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

            if (BarrierProcedure.InParams.Length != 0)
            {
                Error(BarrierProcedure, "Barrier procedure must not take any arguments");
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
    }

}
