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
        private Program Program;

        private Procedure KernelProcedure;
        private Implementation KernelImplementation;
        private Procedure BarrierProcedure;

        private List<Variable> TileStaticVariables = new List<Variable>();
        private List<Variable> GlobalVariables = new List<Variable>();

        private HashSet<string> ReservedNames = new HashSet<string>();

        private static int WhileLoopCounter;
        private static int IfCounter;
        private static HashSet<Microsoft.Boogie.Type> RequiredHavocVariables;

        private int TempCounter = 0;
        private int invariantGenerationCounter;

        private Constant _X = null;
        private Constant _Y = null;
        private Constant _Z = null;

        private const string _X_name = "_X";
        private const string _Y_name = "_Y";
        private const string _Z_name = "_Z";

        private Constant _TILE_SIZE_X = null;
        private Constant _TILE_SIZE_Y = null;
        private Constant _TILE_SIZE_Z = null;

        private const string _TILE_SIZE_X_name = "_TILE_SIZE_X";
        private const string _TILE_SIZE_Y_name = "_TILE_SIZE_Y";
        private const string _TILE_SIZE_Z_name = "_TILE_SIZE_Z";

        private Constant _TILE_X = null;
        private Constant _TILE_Y = null;
        private Constant _TILE_Z = null;

        private const string _TILE_X_name = "_TILE_X";
        private const string _TILE_Y_name = "_TILE_Y";
        private const string _TILE_Z_name = "_TILE_Z";

        private Constant _NUM_TILES_X = null;
        private Constant _NUM_TILES_Y = null;
        private Constant _NUM_TILES_Z = null;

        private const string _NUM_TILES_X_name = "_NUM_TILES_X";
        private const string _NUM_TILES_Y_name = "_NUM_TILES_Y";
        private const string _NUM_TILES_Z_name = "_NUM_TILES_Z";

        public GPUVerifier(Program program)
            : base((IErrorSink)null)
        {
            this.Program = program;
            CheckWellFormedness();
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
            return CheckSingleInstanceOfAttributedProcedure(Program, "kernel");
        }

        private Procedure CheckExactlyOneBarrierProcedure()
        {
            return CheckSingleInstanceOfAttributedProcedure(Program, "barrier");
        }

        private Procedure CheckSingleInstanceOfAttributedProcedure(Program program, string attribute)
        {
            Procedure attributedProcedure = null;

            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                if (!QKeyValue.FindBoolAttribute(decl.Attributes, attribute))
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

            if (attributedProcedure == null)
            {
                Error(program, "\"{0}\" attribute has not been specified for any procedure.  You must mark exactly one procedure with this attribute", attribute);
            }

            return attributedProcedure;
        }

        private void CheckLocalVariables()
        {
            foreach (LocalVariable LV in KernelImplementation.LocVars)
            {
                if (QKeyValue.FindBoolAttribute(LV.Attributes, "tile_static"))
                {
                    Error(LV.tok, "Local variable must not be marked 'tile_static' -- promote the variable to global scope");
                }
            }
        }

        private void FindNonLocalVariables(Program program)
        {
            foreach (Declaration D in program.TopLevelDeclarations)
            {
                if (D is Variable && (D as Variable).IsMutable)
                {
                    if (!ReservedNames.Contains((D as Variable).Name))
                    {
                        if (QKeyValue.FindBoolAttribute(D.Attributes, "tile_static"))
                        {
                            TileStaticVariables.Add(D as Variable);
                        }
                        else
                        {
                            GlobalVariables.Add(D as Variable);
                        }
                    }
                }
                else if (D is Constant)
                {
                    Constant C = D as Constant;
                    if (C.Name.Equals(_X_name))
                    {
                        CheckSpecialConstantType(C);
                        _X = C;
                    }
                    if (C.Name.Equals(_Y_name))
                    {
                        CheckSpecialConstantType(C);
                        _Y = C;
                    }
                    if (C.Name.Equals(_Z_name))
                    {
                        CheckSpecialConstantType(C);
                        _Z = C;
                    }
                    if (C.Name.Equals(_TILE_SIZE_X_name))
                    {
                        CheckSpecialConstantType(C);
                        _TILE_SIZE_X = C;
                    }
                    if (C.Name.Equals(_TILE_SIZE_Y_name))
                    {
                        CheckSpecialConstantType(C);
                        _TILE_SIZE_Y = C;
                    }
                    if (C.Name.Equals(_TILE_SIZE_Z_name))
                    {
                        CheckSpecialConstantType(C);
                        _TILE_SIZE_Z = C;
                    }
                    if (C.Name.Equals(_TILE_X_name))
                    {
                        CheckSpecialConstantType(C);
                        _TILE_X = C;
                    }
                    if (C.Name.Equals(_TILE_Y_name))
                    {
                        CheckSpecialConstantType(C);
                        _TILE_Y = C;
                    }
                    if (C.Name.Equals(_TILE_Z_name))
                    {
                        CheckSpecialConstantType(C);
                        _TILE_Z = C;
                    }
                    if (C.Name.Equals(_NUM_TILES_X_name))
                    {
                        CheckSpecialConstantType(C);
                        _NUM_TILES_X = C;
                    }
                    if (C.Name.Equals(_NUM_TILES_Y_name))
                    {
                        CheckSpecialConstantType(C);
                        _NUM_TILES_Y = C;
                    }
                    if (C.Name.Equals(_NUM_TILES_Z_name))
                    {
                        CheckSpecialConstantType(C);
                        _NUM_TILES_Z = C;
                    }

                }
            }
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

        internal List<Variable> GetTileStaticVariables()
        {
            return TileStaticVariables;
        }

        internal List<Variable> GetGlobalVariables()
        {
            return GlobalVariables;
        }

        internal void doit()
        {

            AddStartAndEndBarriers();

            PullOutNonLocalAccesses();

            if (!CommandLineOptions.OnlyDivergence)
            {
                AddRaceCheckingInstrumentation();
            }

            AbstractSharedState();

            MakeKerenelPredicated();

            MakeKernelDualised();

            GenerateBarrierImplementation();

            GenerateKernelPrecondition();

            if (CommandLineOptions.Inference)
            {
                ComputeInvariant();
            }

            if (CommandLineOptions.outputFile == null)
            {
                CommandLineOptions.outputFile = "temp_ready_to_verify.bpl";
            }

            using (TokenTextWriter writer = new TokenTextWriter(CommandLineOptions.outputFile))
            {
                Program.Emit(writer);
            }



        }

        private void ComputeInvariant()
        {
            List<Expr> UserSuppliedInvariants = GetUserSuppliedInvariants();
            
            invariantGenerationCounter = 0;

            for (int i = 0; i < Program.TopLevelDeclarations.Count; i++)
            {
                if (Program.TopLevelDeclarations[i] is Implementation)
                {
                    Implementation Impl = Program.TopLevelDeclarations[i] as Implementation;

                    if (QKeyValue.FindIntAttribute(Impl.Attributes, "inline", -1) == 1)
                    {
                        continue;
                    }

                    HashSet<string> LocalNames = new HashSet<string>();
                    foreach (Variable v in Impl.LocVars)
                    {
                        string basicName = StripThreadIdentifier(v.Name);
                        LocalNames.Add(basicName);
                    }
                    foreach (Variable v in Impl.InParams)
                    {
                        string basicName = StripThreadIdentifier(v.Name);
                        LocalNames.Add(basicName);
                    }
                    foreach (Variable v in Impl.OutParams)
                    {
                        string basicName = StripThreadIdentifier(v.Name);
                        LocalNames.Add(basicName);
                    }

                    AddCandidateInvariants(Impl.StructuredStmts, LocalNames, UserSuppliedInvariants);
                }

                if (Program.TopLevelDeclarations[i] is Procedure)
                {
                    Procedure Proc = Program.TopLevelDeclarations[i] as Procedure;

                    if (QKeyValue.FindIntAttribute(Proc.Attributes, "inline", -1) == 1)
                    {
                        continue;
                    }

                    if (Proc == KernelProcedure)
                    {
                        continue;
                    }

                    HashSet<string> InParamNames = new HashSet<string>();
                    foreach (Variable v in Proc.InParams)
                    {
                        string basicName = StripThreadIdentifier(v.Name);
                        InParamNames.Add(basicName);
                    }
                    AddCandidateRequires(Proc, InParamNames); // TODO - add support for user-supplied invariants

                    HashSet<string> OutParamNames = new HashSet<string>();
                    foreach (Variable v in Proc.OutParams)
                    {
                        string basicName = StripThreadIdentifier(v.Name);
                        OutParamNames.Add(basicName);
                    }
                    AddCandidateEnsures(Proc, OutParamNames); // TODO - add support for user-supplied invariants
                }

            }

        }

        private void AddCandidateEnsures(Procedure Proc, HashSet<string> LocalNames)
        {
            foreach (string lv in LocalNames)
            {
                AddCandidateEnsures(Proc, Expr.Eq(
                    // Int type used here, but it doesn't matter as we will print and then re-parse the program
                    new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, lv + "$1", Microsoft.Boogie.Type.Int))),
                    new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, lv + "$2", Microsoft.Boogie.Type.Int)))
                ));
            }
        }

        private void AddCandidateRequires(Procedure Proc, HashSet<string> LocalNames)
        {
            foreach (string lv in LocalNames)
            {
                AddCandidateRequires(Proc, Expr.Eq(
                    // Int type used here, but it doesn't matter as we will print and then re-parse the program
                    new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, lv + "$1", Microsoft.Boogie.Type.Int))),
                    new IdentifierExpr(Proc.tok, new LocalVariable(Proc.tok, new TypedIdent(Proc.tok, lv + "$2", Microsoft.Boogie.Type.Int)))
                ));
            }
        }

        private void AddCandidateRequires(Procedure Proc, Expr e)
        {
            Constant ExistentialBooleanConstant = MakeExistentialBoolean(Proc.tok);
            IdentifierExpr ExistentialBoolean = new IdentifierExpr(Proc.tok, ExistentialBooleanConstant);
            Proc.Requires.Add(new Requires(false, Expr.Imp(ExistentialBoolean, e)));
            Program.TopLevelDeclarations.Add(ExistentialBooleanConstant);
        }

        private void AddCandidateEnsures(Procedure Proc, Expr e)
        {
            Constant ExistentialBooleanConstant = MakeExistentialBoolean(Proc.tok);
            IdentifierExpr ExistentialBoolean = new IdentifierExpr(Proc.tok, ExistentialBooleanConstant);
            Proc.Ensures.Add(new Ensures(false, Expr.Imp(ExistentialBoolean, e)));
            Program.TopLevelDeclarations.Add(ExistentialBooleanConstant);
        }

        private List<Expr> GetUserSuppliedInvariants()
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

        private void AddCandidateInvariants(StmtList stmtList, HashSet<string> LocalNames, List<Expr> UserSuppliedInvariants)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                AddCandidateInvariants(bb, LocalNames, UserSuppliedInvariants);
            }
        }

        private void AddCandidateInvariants(BigBlock bb, HashSet<string> LocalNames, List<Expr> UserSuppliedInvariants)
        {
            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;

                foreach(string lv in LocalNames)
                {
                    AddCandidateInvariant(wc, Expr.Eq(
                        // Int type used here, but it doesn't matter as we will print and then re-parse the program
                        new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, lv + "$1", Microsoft.Boogie.Type.Int))),
                        new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, lv + "$2", Microsoft.Boogie.Type.Int)))
                    ));
                }

                if (!CommandLineOptions.OnlyDivergence)
                {
                    AddRaceCheckingCandidateInvariants(wc);
                }

                AddUserSuppliedInvariants(wc, UserSuppliedInvariants);

                AddCandidateInvariants(wc.Body, LocalNames, UserSuppliedInvariants);
            }
            else if (bb.ec is IfCmd)
            {
                // We should have done predicated execution by now, so we won't have any if statements
                Debug.Assert(false);
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }
        }

        private void AddRaceCheckingCandidateInvariants(WhileCmd wc)
        {
            foreach (Variable v in GlobalVariables)
            {
                AddNoReadOrWriteCandidateInvariants(wc, v);
                AddReadOrWrittenOffsetIsThreadId(wc, v, "READ");
                AddReadOrWrittenOffsetIsThreadId(wc, v, "WRITE");
            }

            foreach (Variable v in TileStaticVariables)
            {
                AddNoReadOrWriteCandidateInvariants(wc, v);
                AddReadOrWrittenOffsetIsThreadId(wc, v, "READ");
                AddReadOrWrittenOffsetIsThreadId(wc, v, "WRITE");
            }
        }

        private void AddUserSuppliedInvariants(WhileCmd wc, List<Expr> UserSuppliedInvariants)
        {
            foreach (Expr e in UserSuppliedInvariants)
            {
                wc.Invariants.Add(new AssertCmd(wc.tok, e));
                TokenTextWriter writer = new TokenTextWriter("temp_out.bpl");
                Program.Emit(writer);
                writer.Close();
                wc.Invariants.RemoveAt(wc.Invariants.Count - 1);

                Program temp_program = GPUVerify.ParseBoogieProgram(new List<string>(new string[] { "temp_out.bpl" }), false);

                if(IsOK(temp_program))
                {
                    AddCandidateInvariant(wc, e);
                }
            }
        }

        private bool IsOK(Microsoft.Boogie.Program temp_program)
        {
            if(temp_program == null)
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

        private void AddReadOrWrittenOffsetIsThreadId(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            if (HasXDimension(v) && IndexTypeOfXDimension(v).Equals(GetTypeOfIdX()))
            {
                AddCandidateInvariant(wc,
                    Expr.Imp(
                        new IdentifierExpr(wc.tok, new VariableDualiser(1).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(new IdentifierExpr(wc.tok, new VariableDualiser(1).VisitVariable(MakeOffsetXVariable(v, ReadOrWrite))), new IdentifierExpr(wc.tok, MakeThreadId(wc.tok, "X", 1))))
                );
                AddCandidateInvariant(wc,
                    Expr.Imp(
                        new IdentifierExpr(wc.tok, new VariableDualiser(2).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(new IdentifierExpr(wc.tok, new VariableDualiser(2).VisitVariable(MakeOffsetXVariable(v, ReadOrWrite))), new IdentifierExpr(wc.tok, MakeThreadId(wc.tok, "X", 2))))
                );
            }

            if (HasYDimension(v) && KernelHasIdY() && IndexTypeOfYDimension(v).Equals(GetTypeOfIdY()))
            {
                AddCandidateInvariant(wc,
                    Expr.Imp(
                        new IdentifierExpr(wc.tok, new VariableDualiser(1).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(new IdentifierExpr(wc.tok, new VariableDualiser(1).VisitVariable(MakeOffsetYVariable(v, ReadOrWrite))), new IdentifierExpr(wc.tok, MakeThreadId(wc.tok, "Y", 1))))
                );
                AddCandidateInvariant(wc,
                    Expr.Imp(
                        new IdentifierExpr(wc.tok, new VariableDualiser(2).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(new IdentifierExpr(wc.tok, new VariableDualiser(2).VisitVariable(MakeOffsetYVariable(v, ReadOrWrite))), new IdentifierExpr(wc.tok, MakeThreadId(wc.tok, "Y", 2))))
                );
            }

            if (HasZDimension(v) && KernelHasIdZ() && IndexTypeOfZDimension(v).Equals(GetTypeOfIdZ()))
            {
                AddCandidateInvariant(wc,
                    Expr.Imp(
                        new IdentifierExpr(wc.tok, new VariableDualiser(1).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(new IdentifierExpr(wc.tok, new VariableDualiser(1).VisitVariable(MakeOffsetZVariable(v, ReadOrWrite))), new IdentifierExpr(wc.tok, MakeThreadId(wc.tok, "Z", 1))))
                );
                AddCandidateInvariant(wc,
                    Expr.Imp(
                        new IdentifierExpr(wc.tok, new VariableDualiser(2).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(new IdentifierExpr(wc.tok, new VariableDualiser(2).VisitVariable(MakeOffsetZVariable(v, ReadOrWrite))), new IdentifierExpr(wc.tok, MakeThreadId(wc.tok, "Z", 2))))
                );
            }
            
        }

        private Microsoft.Boogie.Type GetTypeOfIdX()
        {
            Contract.Requires(_X != null);
            return _X.TypedIdent.Type;
        }

        private Microsoft.Boogie.Type GetTypeOfIdY()
        {
            Contract.Requires(_Y != null);
            return _Y.TypedIdent.Type;
        }

        private Microsoft.Boogie.Type GetTypeOfIdZ()
        {
            Contract.Requires(_Z != null);
            return _Z.TypedIdent.Type;
        }

        private Microsoft.Boogie.Type GetTypeOfId(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return GetTypeOfIdX();
            if (dimension.Equals("Y")) return GetTypeOfIdY();
            if (dimension.Equals("Z")) return GetTypeOfIdZ();
            Debug.Assert(false);
            return null;
        }

        private bool KernelHasIdX()
        {
            return _X != null;
        }

        private bool KernelHasIdY()
        {
            return _Y != null;
        }

        private bool KernelHasIdZ()
        {
            return _Z != null;
        }

        private bool KernelHasTileIdX()
        {
            return _TILE_X != null;
        }

        private bool KernelHasTileIdY()
        {
            return _TILE_Y != null;
        }

        private bool KernelHasTileIdZ()
        {
            return _TILE_Z != null;
        }

        private bool KernelHasNumTilesX()
        {
            return _NUM_TILES_X != null;
        }

        private bool KernelHasNumTilesY()
        {
            return _NUM_TILES_Y != null;
        }

        private bool KernelHasNumTilesZ()
        {
            return _NUM_TILES_Z != null;
        }

        private bool KernelHasTileSizeX()
        {
            return _TILE_SIZE_X != null;
        }

        private bool KernelHasTileSizeY()
        {
            return _TILE_SIZE_Y != null;
        }

        private bool KernelHasTileSizeZ()
        {
            return _TILE_SIZE_Z != null;
        }

        private bool KernelHasId(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return KernelHasIdX();
            if (dimension.Equals("Y")) return KernelHasIdY();
            if (dimension.Equals("Z")) return KernelHasIdZ();
            Debug.Assert(false);
            return false;
        }

        private void AddNoReadOrWriteCandidateInvariants(WhileCmd wc, Variable v)
        {
            AddNoReadOrWriteCandidateInvariant(wc, v, "READ", "1");
            AddNoReadOrWriteCandidateInvariant(wc, v, "WRITE", "1");
            AddNoReadOrWriteCandidateInvariant(wc, v, "READ", "2");
            AddNoReadOrWriteCandidateInvariant(wc, v, "WRITE", "2");
        }

        private void AddNoReadOrWriteCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
                            Variable ReadHasOccurred1 = MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite);
                            ReadHasOccurred1.Name = ReadHasOccurred1.Name + "$" + OneOrTwo;
                            ReadHasOccurred1.TypedIdent.Name = ReadHasOccurred1.TypedIdent.Name + "$" + OneOrTwo;
                            AddCandidateInvariant(wc, Expr.Not(new IdentifierExpr(wc.tok, ReadHasOccurred1)));
        }

        private void AddCandidateInvariant(WhileCmd wc, Expr e)
        {
            Constant ExistentialBooleanConstant = MakeExistentialBoolean(wc.tok);
            IdentifierExpr ExistentialBoolean = new IdentifierExpr(wc.tok, ExistentialBooleanConstant);
            wc.Invariants.Add(new AssertCmd(wc.tok, Expr.Imp(ExistentialBoolean, e)));
            Program.TopLevelDeclarations.Add(ExistentialBooleanConstant);
        }

        private Constant MakeExistentialBoolean(IToken tok)
        {
            Constant ExistentialBooleanConstant = new Constant(tok, new TypedIdent(tok, "_b" + invariantGenerationCounter, Microsoft.Boogie.Type.Bool), false);
            invariantGenerationCounter++;
            ExistentialBooleanConstant.AddAttribute("existential", new object[] { Expr.True });
            return ExistentialBooleanConstant;
        }

        private string StripThreadIdentifier(string p)
        {
            return p.Substring(0, p.IndexOf("$"));
        }

        private void AddStartAndEndBarriers()
        {
            CallCmd FirstBarrier = new CallCmd(KernelImplementation.tok, "BARRIER", new ExprSeq(), new IdentifierExprSeq());
            CallCmd LastBarrier = new CallCmd(KernelImplementation.tok, "BARRIER", new ExprSeq(), new IdentifierExprSeq());

            CmdSeq newCommands = new CmdSeq();
            newCommands.Add(FirstBarrier);
            foreach(Cmd c in KernelImplementation.StructuredStmts.BigBlocks[0].simpleCmds)
            {
                newCommands.Add(c);
            }
            KernelImplementation.StructuredStmts.BigBlocks[0].simpleCmds = newCommands;

            CmdSeq lastCommand = new CmdSeq();
            lastCommand.Add(LastBarrier);
            BigBlock bb = new BigBlock(KernelProcedure.tok, "__lastBarrier", lastCommand, null, null);

            KernelImplementation.StructuredStmts.BigBlocks.Add(bb);
        }

        private void GenerateKernelPrecondition()
        {

            if (!CommandLineOptions.OnlyDivergence)
            {
                foreach (Variable v in GlobalVariables)
                {
                    AddRequiresNoPendingAccess(v);
                }
                foreach (Variable v in TileStaticVariables)
                {
                    AddRequiresNoPendingAccess(v);
                }
            }

            Expr AssumeDistinctThreads = null;
            Expr AssumeThreadIdsInRange = null;
            IToken tok = KernelImplementation.tok;

            GeneratePreconditionsForDimension(ref AssumeDistinctThreads, ref AssumeThreadIdsInRange, tok, "X");
            GeneratePreconditionsForDimension(ref AssumeDistinctThreads, ref AssumeThreadIdsInRange, tok, "Y");
            GeneratePreconditionsForDimension(ref AssumeDistinctThreads, ref AssumeThreadIdsInRange, tok, "Z");

            if (AssumeDistinctThreads != null)
            {
                Debug.Assert(AssumeThreadIdsInRange != null);

                KernelProcedure.Requires.Add(new Requires(false, AssumeDistinctThreads));
                KernelProcedure.Requires.Add(new Requires(false, AssumeThreadIdsInRange));

                //Program.TopLevelDeclarations.Add(new Axiom(tok, AssumeDistinctThreads));
                //Program.TopLevelDeclarations.Add(new Axiom(tok, AssumeThreadIdsInRange));
            }
            else
            {
                Debug.Assert(AssumeThreadIdsInRange == null);
            }


        }

        private void GeneratePreconditionsForDimension(ref Expr AssumeDistinctThreads, ref Expr AssumeThreadIdsInRange, IToken tok, String dimension)
        {
            if (KernelHasId(dimension))
            {
                if (GetTypeOfId(dimension).Equals(Microsoft.Boogie.Type.GetBvType(32)))
                {
                    KernelProcedure.Requires.Add(new Requires(false, MakeBitVectorBinaryBoolean("BV32_GT", new IdentifierExpr(tok, GetTileSize(dimension)), ZeroBV(tok))));
                    KernelProcedure.Requires.Add(new Requires(false, MakeBitVectorBinaryBoolean("BV32_GT", new IdentifierExpr(tok, GetNumTiles(dimension)), ZeroBV(tok))));
                    KernelProcedure.Requires.Add(new Requires(false, MakeBitVectorBinaryBoolean("BV32_GEQ", new IdentifierExpr(tok, GetTileId(dimension)), ZeroBV(tok))));
                    KernelProcedure.Requires.Add(new Requires(false, MakeBitVectorBinaryBoolean("BV32_LT", new IdentifierExpr(tok, GetTileId(dimension)), new IdentifierExpr(tok, GetNumTiles(dimension)))));

                    //Program.TopLevelDeclarations.Add(new Axiom(tok, MakeBitVectorBinaryBoolean("BV32_GT", new IdentifierExpr(tok, GetTileSize(dimension)), ZeroBV(tok))));
                    //Program.TopLevelDeclarations.Add(new Axiom(tok, MakeBitVectorBinaryBoolean("BV32_GT", new IdentifierExpr(tok, GetNumTiles(dimension)), ZeroBV(tok))));
                    //Program.TopLevelDeclarations.Add(new Axiom(tok, MakeBitVectorBinaryBoolean("BV32_GEQ", new IdentifierExpr(tok, GetTileId(dimension)), ZeroBV(tok))));
                    //Program.TopLevelDeclarations.Add(new Axiom(tok, MakeBitVectorBinaryBoolean("BV32_LT", new IdentifierExpr(tok, GetTileId(dimension)), new IdentifierExpr(tok, GetNumTiles(dimension)))));
                }
                else
                {
                    KernelProcedure.Requires.Add(new Requires(false, Expr.Gt(new IdentifierExpr(tok, GetTileSize(dimension)), Zero(tok))));
                    KernelProcedure.Requires.Add(new Requires(false, Expr.Gt(new IdentifierExpr(tok, GetNumTiles(dimension)), Zero(tok))));
                    KernelProcedure.Requires.Add(new Requires(false, Expr.Ge(new IdentifierExpr(tok, GetTileId(dimension)), Zero(tok))));
                    KernelProcedure.Requires.Add(new Requires(false, Expr.Lt(new IdentifierExpr(tok, GetTileId(dimension)), new IdentifierExpr(tok, GetNumTiles(dimension)))));

                    //Program.TopLevelDeclarations.Add(new Axiom(tok, Expr.Gt(new IdentifierExpr(tok, GetTileSize(dimension)), Zero(tok))));
                    //Program.TopLevelDeclarations.Add(new Axiom(tok, Expr.Gt(new IdentifierExpr(tok, GetNumTiles(dimension)), Zero(tok))));
                    //Program.TopLevelDeclarations.Add(new Axiom(tok, Expr.Ge(new IdentifierExpr(tok, GetTileId(dimension)), Zero(tok))));
                    //Program.TopLevelDeclarations.Add(new Axiom(tok, Expr.Lt(new IdentifierExpr(tok, GetTileId(dimension)), new IdentifierExpr(tok, GetNumTiles(dimension)))));

                }
                Expr AssumeThreadsDistinctInDimension =
                        Expr.Neq(
                        new IdentifierExpr(tok, MakeThreadId(tok, dimension, 1)),
                        new IdentifierExpr(tok, MakeThreadId(tok, dimension, 2))
                        );

                AssumeDistinctThreads = (null == AssumeDistinctThreads) ? AssumeThreadsDistinctInDimension : Expr.Or(AssumeDistinctThreads, AssumeThreadsDistinctInDimension);

                Expr AssumeThreadIdsInRangeInDimension =
                    GetTypeOfId(dimension).Equals(Microsoft.Boogie.Type.GetBvType(32)) ?
                        Expr.And(
                            Expr.And(
                            MakeBitVectorBinaryBoolean("BV32_GEQ", new IdentifierExpr(tok, MakeThreadId(tok, dimension, 1)), ZeroBV(tok)),
                            MakeBitVectorBinaryBoolean("BV32_GEQ", new IdentifierExpr(tok, MakeThreadId(tok, dimension, 2)), ZeroBV(tok))
                            ),
                            Expr.And(
                            MakeBitVectorBinaryBoolean("BV32_LT", new IdentifierExpr(tok, MakeThreadId(tok, dimension, 1)), new IdentifierExpr(tok, GetTileSize(dimension))),
                            MakeBitVectorBinaryBoolean("BV32_LT", new IdentifierExpr(tok, MakeThreadId(tok, dimension, 2)), new IdentifierExpr(tok, GetTileSize(dimension)))
                            ))
                    :
                        Expr.And(
                            Expr.And(
                            Expr.Ge(new IdentifierExpr(tok, MakeThreadId(tok, dimension, 1)), Zero(tok)),
                            Expr.Ge(new IdentifierExpr(tok, MakeThreadId(tok, dimension, 2)), Zero(tok))
                            ),
                            Expr.And(
                            Expr.Lt(new IdentifierExpr(tok, MakeThreadId(tok, dimension, 1)), new IdentifierExpr(tok, GetTileSize(dimension))),
                            Expr.Lt(new IdentifierExpr(tok, MakeThreadId(tok, dimension, 2)), new IdentifierExpr(tok, GetTileSize(dimension)))
                            ));

                AssumeThreadIdsInRange = (null == AssumeThreadIdsInRange) ? AssumeThreadIdsInRangeInDimension : Expr.And(AssumeThreadIdsInRange, AssumeThreadIdsInRangeInDimension);
            }
        }

        private Expr MakeBitVectorBinaryBoolean(string functionName, Expr lhs, Expr rhs)
        {
            return new NAryExpr(lhs.tok, new FunctionCall(new Function(lhs.tok, functionName, new VariableSeq(new Variable[] { 
                new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "arg1", Microsoft.Boogie.Type.GetBvType(32))),
                new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "arg2", Microsoft.Boogie.Type.GetBvType(32)))
            }), new LocalVariable(lhs.tok, new TypedIdent(lhs.tok, "result", Microsoft.Boogie.Type.Bool)))), new ExprSeq(new Expr[] { lhs, rhs }));
        }

        private Constant GetTileSize(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if(dimension.Equals("X")) return _TILE_SIZE_X;
            if(dimension.Equals("Y")) return _TILE_SIZE_Y;
            if(dimension.Equals("Z")) return _TILE_SIZE_Z;
            Debug.Assert(false);
            return null;
        }

        private Constant GetNumTiles(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return _NUM_TILES_X;
            if (dimension.Equals("Y")) return _NUM_TILES_Y;
            if (dimension.Equals("Z")) return _NUM_TILES_Z;
            Debug.Assert(false);
            return null;
        }

        private Constant MakeThreadId(IToken tok, string dimension, int number)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            string name = null;
            if (dimension.Equals("X")) name = _X_name;
            if (dimension.Equals("Y")) name = _Y_name;
            if (dimension.Equals("Z")) name = _Z_name;
            Debug.Assert(name != null);
            name = name + "$" + number;
            return new Constant(tok, new TypedIdent(tok, "_" + dimension + "$" + number, GetTypeOfId(dimension)));
        }

        private Constant GetTileId(string dimension)
        {
            Contract.Requires(dimension.Equals("X") || dimension.Equals("Y") || dimension.Equals("Z"));
            if (dimension.Equals("X")) return _TILE_X;
            if (dimension.Equals("Y")) return _TILE_Y;
            if (dimension.Equals("Z")) return _TILE_Z;
            Debug.Assert(false);
            return null;
        }

        private static LiteralExpr Zero(IToken tok)
        {
            return new LiteralExpr(tok, BigNum.FromInt(0));
        }

        private static LiteralExpr ZeroBV(IToken tok)
        {
            return new LiteralExpr(tok, BigNum.FromInt(0), 32);
        }

        private void AddRequiresNoPendingAccess(Variable v)
        {
            IdentifierExpr ReadAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, "READ")));
            IdentifierExpr ReadAccessOccurred2 = new IdentifierExpr(v.tok, new VariableDualiser(2).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, "READ")));
            IdentifierExpr WriteAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, "WRITE")));
            IdentifierExpr WriteAccessOccurred2 = new IdentifierExpr(v.tok, new VariableDualiser(2).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, "WRITE")));
            KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.And(Expr.Not(ReadAccessOccurred2), Expr.And(Expr.Not(WriteAccessOccurred1), Expr.Not(WriteAccessOccurred2))))));
        }

        private void GenerateBarrierImplementation()
        {
            IToken tok = BarrierProcedure.tok;

            List<BigBlock> bigblocks = new List<BigBlock>();
            BigBlock checkNonDivergence = new BigBlock(tok, "__BarrierImpl", new CmdSeq(), null, null);
            bigblocks.Add(checkNonDivergence);

            IdentifierExpr P1 = new IdentifierExpr(tok, new LocalVariable(tok, BarrierProcedure.InParams[0].TypedIdent));
            IdentifierExpr P2 = new IdentifierExpr(tok, new LocalVariable(tok, BarrierProcedure.InParams[1].TypedIdent));

            checkNonDivergence.simpleCmds.Add(new AssertCmd(tok, Expr.Eq(P1, P2)));

            if (!CommandLineOptions.OnlyDivergence || !CommandLineOptions.FullAbstraction)
            {
                List<BigBlock> returnbigblocks = new List<BigBlock>();
                returnbigblocks.Add(new BigBlock(tok, "__Disabled", new CmdSeq(), null, new ReturnCmd(tok)));
                StmtList returnstatement = new StmtList(returnbigblocks, BarrierProcedure.tok);
                checkNonDivergence.ec = new IfCmd(tok, Expr.And(Expr.Not(P1), Expr.Not(P2)), returnstatement, null, null);
            }

            if (!CommandLineOptions.OnlyDivergence)
            {
                BigBlock checkForRaces = new BigBlock(tok, "__CheckForRaces", new CmdSeq(), null, null);
                bigblocks.Add(checkForRaces);
                foreach (Variable v in GlobalVariables)
                {
                    CheckForRaces(tok, checkForRaces, v);
                }
                foreach (Variable v in TileStaticVariables)
                {
                    CheckForRaces(tok, checkForRaces, v);
                }

                foreach (Variable v in GlobalVariables)
                {
                    SetNoAccessOccurred(tok, checkForRaces, v);
                }
                foreach (Variable v in TileStaticVariables)
                {
                    SetNoAccessOccurred(tok, checkForRaces, v);
                }

            }

            if (!CommandLineOptions.FullAbstraction)
            {
                BigBlock havocSharedState = new BigBlock(tok, "__HavocSharedState", new CmdSeq(), null, null);
                bigblocks.Add(havocSharedState);
                foreach (Variable v in GlobalVariables)
                {
                    HavocAndAssumeEquality(tok, havocSharedState, v);
                }
                foreach (Variable v in TileStaticVariables)
                {
                    HavocAndAssumeEquality(tok, havocSharedState, v);
                }

            }

            StmtList statements = new StmtList(bigblocks, BarrierProcedure.tok);
            Implementation BarrierImplementation = new Implementation(BarrierProcedure.tok, BarrierProcedure.Name, new TypeVariableSeq(), BarrierProcedure.InParams, BarrierProcedure.OutParams, new VariableSeq(), statements);

            BarrierImplementation.AddAttribute("inline", new object[] { new LiteralExpr(tok, BigNum.FromInt(1)) });
            BarrierProcedure.AddAttribute("inline", new object[] { new LiteralExpr(tok, BigNum.FromInt(1)) });

            Program.TopLevelDeclarations.Add(BarrierImplementation);
        }

        private void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v)
        {
            SetNoAccessOccurred(tok, bb, v, "READ");
            SetNoAccessOccurred(tok, bb, v, "WRITE");
        }

        private void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v, string AccessType)
        {
            IdentifierExpr AccessOccurred1 = new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, AccessType)));
            IdentifierExpr AccessOccurred2 = new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, AccessType)));

            BarrierProcedure.Modifies.Add(AccessOccurred1);
            BarrierProcedure.Modifies.Add(AccessOccurred2);

            List<AssignLhs> lhss = new List<AssignLhs>();
            lhss.Add(new SimpleAssignLhs(tok, AccessOccurred1));
            lhss.Add(new SimpleAssignLhs(tok, AccessOccurred2));
            List<Expr> rhss = new List<Expr>();
            rhss.Add(Expr.False);
            rhss.Add(Expr.False);
            bb.simpleCmds.Add(new AssignCmd(tok, lhss, rhss));
        }

        private void CheckForRaces(IToken tok, BigBlock bb, Variable v)
        {
            bb.simpleCmds.Add(new AssertCmd(tok, Expr.Not(GenerateRaceCondition(tok, v, "WRITE", "WRITE"))));
            bb.simpleCmds.Add(new AssertCmd(tok, Expr.Not(GenerateRaceCondition(tok, v, "READ", "WRITE"))));
        }

        private static Expr GenerateRaceCondition(IToken tok, Variable v, string FirstAccessType, string SecondAccessType)
        {
            Expr RaceCondition = Expr.And(
                new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, FirstAccessType))),
                new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, SecondAccessType))));

            if (HasXDimension(v))
            {
                RaceCondition = Expr.And(RaceCondition, Expr.Eq(
                    new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeOffsetXVariable(v, FirstAccessType))),
                    new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeOffsetXVariable(v, SecondAccessType)))
                ));
            }

            if (HasYDimension(v))
            {
                RaceCondition = Expr.And(RaceCondition, Expr.Eq(
                    new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeOffsetYVariable(v, FirstAccessType))),
                    new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeOffsetYVariable(v, SecondAccessType)))
                    ));
            }

            if (HasZDimension(v))
            {
                RaceCondition = Expr.And(RaceCondition, Expr.Eq(
                    new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeOffsetZVariable(v, FirstAccessType))),
                    new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeOffsetZVariable(v, SecondAccessType)))
                    ));
            }

            return RaceCondition;
        }

        private static bool HasZDimension(Variable v)
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

        private static bool HasYDimension(Variable v)
        {
            return v.TypedIdent.Type is MapType && (v.TypedIdent.Type as MapType).Result is MapType;
        }

        private static bool HasXDimension(Variable v)
        {
            return v.TypedIdent.Type is MapType;
        }

        private void HavocAndAssumeEquality(IToken tok, BigBlock bb, Variable v)
        {
            IdentifierExpr v1 = new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(v.Clone() as Variable));
            IdentifierExpr v2 = new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(v.Clone() as Variable));

            bb.simpleCmds.Add(new HavocCmd(tok, new IdentifierExprSeq(new IdentifierExpr[] { v1, v2 })));
            bb.simpleCmds.Add(new AssumeCmd(tok, Expr.Eq(v1, v2)));
            BarrierProcedure.Modifies.Add(v1);
            BarrierProcedure.Modifies.Add(v2);

            if (!KernelProcedure.Modifies.Has(v1))
            {
                Debug.Assert(!KernelProcedure.Modifies.Has(v2));
                KernelProcedure.Modifies.Add(v1);
                KernelProcedure.Modifies.Add(v2);
            }

        }

        private void AbstractSharedState()
        {
            if (!CommandLineOptions.FullAbstraction)
            {
                return; // There's actually nothing to do here
            }

            List<Declaration> NewTopLevelDeclarations = new List<Declaration>();

            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Variable && GlobalVariables.Contains(d as Variable))
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
                if (!(GlobalVariables.Contains(e.Decl)))
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
                if (!TileStaticVariables.Contains(v))
                {
                    NewLocVars.Add(v);
                }
            }

            impl.LocVars = NewLocVars;

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

        private BigBlock PerformFullSharedStateAbstraction(BigBlock bb)
        {
            BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;
                    Debug.Assert(assign.Lhss.Count == 1);
                    Debug.Assert(assign.Rhss.Count == 1);
                    AssignLhs lhs = assign.Lhss[0];
                    Expr rhs = assign.Rhss[0];
                    ReadCollector rc = new ReadCollector(GlobalVariables, TileStaticVariables);
                    rc.Visit(rhs);
                    if (rc.accesses.Count > 0)
                    {
                        Debug.Assert(lhs is SimpleAssignLhs);
                        result.simpleCmds.Add(new HavocCmd(c.tok, new IdentifierExprSeq(new IdentifierExpr[] { (lhs as SimpleAssignLhs).AssignedVariable })));
                        continue;
                    }

                    WriteCollector wc = new WriteCollector(GlobalVariables, TileStaticVariables);
                    wc.Visit(lhs);
                    if (wc.GetAccess() != null)
                    {
                        continue; // Just remove the write
                    }

                }
                result.simpleCmds.Add(c);
            }

            if (bb.ec is WhileCmd)
            {
                WhileCmd WhileCommand = bb.ec as WhileCmd;
                result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard, WhileCommand.Invariants, PerformFullSharedStateAbstraction(WhileCommand.Body));
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;
                Debug.Assert(IfCommand.elseIf == null); // We don't handle else if yet
                result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, PerformFullSharedStateAbstraction(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? PerformFullSharedStateAbstraction(IfCommand.elseBlock) : null);
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }

            return result;

        }





        private void AddRaceCheckingInstrumentation()
        {
            foreach(Variable v in GlobalVariables)
            {
                AddRaceCheckingInstrumentation(v);
            }
            foreach (Variable v in TileStaticVariables)
            {
                AddRaceCheckingInstrumentation(v);
            }

            AddRaceCheckCalls(KernelImplementation);

        }

        private void AddRaceCheckingInstrumentation(Variable v)
        {
            IdentifierExprSeq vars = AddRaceCheckingDeclarations(v);
            foreach (IdentifierExpr e in vars)
            {
                KernelProcedure.Modifies.Add(e);
            }
            AddRaceCheckingProcedures(v);
        }

        private void AddRaceCheckCalls(Implementation impl)
        {
            impl.StructuredStmts = AddRaceCheckCalls(impl.StructuredStmts);
        }

        private StmtList AddRaceCheckCalls(StmtList stmtList)
        {
            Contract.Requires(stmtList != null);
            
            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(AddRaceCheckCalls(bodyBlock));
            }
            return result;
        }

        private BigBlock AddRaceCheckCalls(BigBlock bb)
        {
            BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;
                    Debug.Assert(assign.Lhss.Count == 1);
                    Debug.Assert(assign.Rhss.Count == 1);
                    AssignLhs lhs = assign.Lhss[0];
                    Expr rhs = assign.Rhss[0];

                    ReadCollector rc = new ReadCollector(GlobalVariables, TileStaticVariables);
                    rc.Visit(rhs);
                    if (rc.accesses.Count > 0)
                    {
                        Debug.Assert(rc.accesses.Count == 1);
                        AccessRecord ar = rc.accesses.ToList()[0];
                        ExprSeq inParams = new ExprSeq();
                        if (ar.IndexZ != null)
                        {
                            inParams.Add(ar.IndexZ);
                        }
                        if (ar.IndexY != null)
                        {
                            inParams.Add(ar.IndexY);
                        }
                        if (ar.IndexX != null)
                        {
                            inParams.Add(ar.IndexX);
                        }

                        result.simpleCmds.Add(new CallCmd(c.tok, "_LOG_READ_" + ar.v.Name, inParams, new IdentifierExprSeq()));
                    }

                    WriteCollector wc = new WriteCollector(GlobalVariables, TileStaticVariables);
                    wc.Visit(lhs);
                    if (wc.GetAccess() != null)
                    {
                        AccessRecord ar = wc.GetAccess();
                        ExprSeq inParams = new ExprSeq();
                        if (ar.IndexZ != null)
                        {
                            inParams.Add(ar.IndexZ);
                        }
                        if (ar.IndexY != null)
                        {
                            inParams.Add(ar.IndexY);
                        }
                        if (ar.IndexX != null)
                        {
                            inParams.Add(ar.IndexX);
                        }

                        result.simpleCmds.Add(new CallCmd(c.tok, "_LOG_WRITE_" + ar.v.Name, inParams, new IdentifierExprSeq()));
                    }



                }
                result.simpleCmds.Add(c);
            }

            if (bb.ec is WhileCmd)
            {
                WhileCmd WhileCommand = bb.ec as WhileCmd;
                result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard, WhileCommand.Invariants, AddRaceCheckCalls(WhileCommand.Body));
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;
                Debug.Assert(IfCommand.elseIf == null); // We don't handle else if yet
                result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, AddRaceCheckCalls(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? AddRaceCheckCalls(IfCommand.elseBlock) : null);
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }

            return result;

        }

        private void AddRaceCheckingProcedures(Variable v)
        {
            AddLogAccessProcedure(v, "READ");
            AddLogAccessProcedure(v, "WRITE");
        }

        private void AddLogAccessProcedure(Variable v, string ReadOrWrite)
        {
            VariableSeq inParams = new VariableSeq();
            IdentifierExprSeq modifies = new IdentifierExprSeq();
            Variable ReadOrWriteHasOccurredVariable = MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite);
            Variable ReadOrWriteOffsetXVariable = null;
            Variable ReadOrWriteOffsetYVariable = null;
            Variable ReadOrWriteOffsetZVariable = null;
            Variable XParameterVariable = null;
            Variable YParameterVariable = null;
            Variable ZParameterVariable = null;

            modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteHasOccurredVariable));

            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);
                Debug.Assert(IsIntOrBv32(mt.Arguments[0]));

                ReadOrWriteOffsetXVariable = MakeOffsetXVariable(v, ReadOrWrite);
                modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteOffsetXVariable));
                XParameterVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "_X_index", mt.Arguments[0]));
                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(IsIntOrBv32(mt2.Arguments[0]));
                    ReadOrWriteOffsetYVariable = MakeOffsetYVariable(v, ReadOrWrite);
                    modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteOffsetYVariable));
                    YParameterVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "_Y_index", mt2.Arguments[0]));
                    if (mt2.Result is MapType)
                    {
                        MapType mt3 = mt2.Arguments[0] as MapType;
                        Debug.Assert(mt3.Arguments.Length == 1);
                        Debug.Assert(IsIntOrBv32(mt3.Arguments[0]));
                        Debug.Assert(!(mt3.Result is MapType));
                        ReadOrWriteOffsetZVariable = MakeOffsetZVariable(v, ReadOrWrite);
                        modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteOffsetZVariable));
                        ZParameterVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "_Z_index", mt3.Arguments[0]));
                    }
                }
            }

            if (ZParameterVariable != null)
            {
                inParams.Add(ZParameterVariable);
            }

            if (YParameterVariable != null)
            {
                inParams.Add(YParameterVariable);
            }

            if (XParameterVariable != null)
            {
                inParams.Add(XParameterVariable);
            }

            Procedure LogReadOrWriteProcedure = new Procedure(v.tok, "_LOG_" + ReadOrWrite + "_" + v.Name, new TypeVariableSeq(), inParams, new VariableSeq(), new RequiresSeq(), modifies, new EnsuresSeq());
            LogReadOrWriteProcedure.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });


            VariableSeq locals = new VariableSeq();
            Variable TrackVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "track", Microsoft.Boogie.Type.Bool));
            locals.Add(TrackVariable);

            List<BigBlock> bigblocks = new List<BigBlock>();

            CmdSeq simpleCmds = new CmdSeq();

            simpleCmds.Add(new HavocCmd(v.tok, new IdentifierExprSeq(new IdentifierExpr[] { new IdentifierExpr(v.tok, TrackVariable) })));
            simpleCmds.Add(MakeConditionalAssignment(ReadOrWriteHasOccurredVariable, new IdentifierExpr(v.tok, TrackVariable), Expr.True));
            if (ReadOrWriteOffsetXVariable != null)
            {
                simpleCmds.Add(MakeConditionalAssignment(ReadOrWriteOffsetXVariable, new IdentifierExpr(v.tok, TrackVariable), new IdentifierExpr(v.tok, XParameterVariable)));
            }
            if (ReadOrWriteOffsetYVariable != null)
            {
                simpleCmds.Add(MakeConditionalAssignment(ReadOrWriteOffsetYVariable, new IdentifierExpr(v.tok, TrackVariable), new IdentifierExpr(v.tok, YParameterVariable)));
            }
            if (ReadOrWriteOffsetZVariable != null)
            {
                simpleCmds.Add(MakeConditionalAssignment(ReadOrWriteOffsetZVariable, new IdentifierExpr(v.tok, TrackVariable), new IdentifierExpr(v.tok, ZParameterVariable)));
            }


            bigblocks.Add(new BigBlock(v.tok, "_LOG_" + ReadOrWrite + "", simpleCmds, null, null));

            StmtList statements = new StmtList(bigblocks, v.tok);

            Implementation LogReadOrWriteImplementation = new Implementation(v.tok, "_LOG_" + ReadOrWrite + "_" + v.Name, new TypeVariableSeq(), inParams, new VariableSeq(), locals, statements);
            LogReadOrWriteImplementation.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

            Program.TopLevelDeclarations.Add(LogReadOrWriteProcedure);
            Program.TopLevelDeclarations.Add(LogReadOrWriteImplementation);
        }

        private static GlobalVariable MakeOffsetZVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_OFFSET_Z_" + v.Name, IndexTypeOfZDimension(v)));
        }

        private static GlobalVariable MakeOffsetYVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_OFFSET_Y_" + v.Name, IndexTypeOfYDimension(v)));
        }

        private static GlobalVariable MakeOffsetXVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_OFFSET_X_" + v.Name, IndexTypeOfXDimension(v)));
        }

        private static GlobalVariable MakeReadOrWriteHasOccurredVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_HAS_OCCURRED_" + v.Name, Microsoft.Boogie.Type.Bool));
        }

        private static Microsoft.Boogie.Type IndexTypeOfZDimension(Variable v)
        {
            Contract.Requires(HasZDimension(v));
            MapType mt = v.TypedIdent.Type as MapType;
            MapType mt2 = mt.Result as MapType;
            MapType mt3 = mt2.Result as MapType;
            return mt3.Arguments[0];
        }

        private static Microsoft.Boogie.Type IndexTypeOfYDimension(Variable v)
        {
            Contract.Requires(HasYDimension(v));
            MapType mt = v.TypedIdent.Type as MapType;
            MapType mt2 = mt.Result as MapType;
            return mt2.Arguments[0];
        }

        private static Microsoft.Boogie.Type IndexTypeOfXDimension(Variable v)
        {
            Contract.Requires(HasXDimension(v));
            MapType mt = v.TypedIdent.Type as MapType;
            return mt.Arguments[0];
        }

        private AssignCmd MakeConditionalAssignment(Variable lhs, Expr condition, Expr rhs)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            lhss.Add(new SimpleAssignLhs(lhs.tok, new IdentifierExpr(lhs.tok, lhs)));
            rhss.Add(new NAryExpr(rhs.tok, new IfThenElse(rhs.tok), new ExprSeq(new Expr[] { condition, rhs, new IdentifierExpr(lhs.tok, lhs) })));
            return new AssignCmd(lhs.tok, lhss, rhss);
        }

        private IdentifierExprSeq AddRaceCheckingDeclarations(Variable v)
        {
            IdentifierExprSeq result = new IdentifierExprSeq();

            Variable ReadHasOccurred = new GlobalVariable(v.tok, new TypedIdent(v.tok, "_READ_HAS_OCCURRED_" + v.Name, Microsoft.Boogie.Type.Bool));
            Variable WriteHasOccurred = new GlobalVariable(v.tok, new TypedIdent(v.tok, "_WRITE_HAS_OCCURRED_" + v.Name, Microsoft.Boogie.Type.Bool));

            result.Add(new IdentifierExpr(v.tok, ReadHasOccurred));
            result.Add(new IdentifierExpr(v.tok, WriteHasOccurred));

            Program.TopLevelDeclarations.Add(ReadHasOccurred);
            Program.TopLevelDeclarations.Add(WriteHasOccurred);
            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);
                Debug.Assert(IsIntOrBv32(mt.Arguments[0]));

                Variable ReadOffsetX = MakeOffsetXVariable(v, "READ");
                Variable WriteOffsetX = MakeOffsetXVariable(v, "WRITE");
                result.Add(new IdentifierExpr(v.tok, ReadOffsetX));
                result.Add(new IdentifierExpr(v.tok, WriteOffsetX));
                Program.TopLevelDeclarations.Add(ReadOffsetX);
                Program.TopLevelDeclarations.Add(WriteOffsetX);

                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(IsIntOrBv32(mt2.Arguments[0]));

                    Variable ReadOffsetY = MakeOffsetYVariable(v, "READ");
                    Variable WriteOffsetY = MakeOffsetYVariable(v, "WRITE");
                    result.Add(new IdentifierExpr(v.tok, ReadOffsetY));
                    result.Add(new IdentifierExpr(v.tok, WriteOffsetY));
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
                        result.Add(new IdentifierExpr(v.tok, ReadOffsetZ));
                        result.Add(new IdentifierExpr(v.tok, WriteOffsetZ));
                        Program.TopLevelDeclarations.Add(ReadOffsetZ);
                        Program.TopLevelDeclarations.Add(WriteOffsetZ);

                    }
                }
            }

            return result;
        }

        private bool IsIntOrBv32(Microsoft.Boogie.Type type)
        {
            return type.Equals(Microsoft.Boogie.Type.Int) || type.Equals(Microsoft.Boogie.Type.GetBvType(32));
        }

        private void PullOutNonLocalAccesses()
        {
            KernelImplementation.StructuredStmts = PullOutNonLocalAccesses(KernelImplementation.StructuredStmts);
        }

        private StmtList PullOutNonLocalAccesses(StmtList stmtList)
        {
            Contract.Requires(stmtList != null);            

            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(PullOutNonLocalAccesses(bodyBlock));
            }

            return result;
        }

        private BigBlock PullOutNonLocalAccesses(BigBlock bb)
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

                        while (NonLocalAccessCollector.ContainsNonLocalAccess(e, GlobalVariables, TileStaticVariables))
                        {
                            AssignCmd assignToTemp;
                            LocalVariable tempDecl;
                            e = ExtractLocalAccessToTemp(e, out assignToTemp, out tempDecl);
                            result.simpleCmds.Add(assignToTemp);
                            KernelImplementation.LocVars.Add(tempDecl);
                        }

                        newIns.Add(e);

                    }

                    result.simpleCmds.Add(new CallCmd(call.tok, call.callee, newIns, call.Outs));
                }
                else if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;

                    Debug.Assert(assign.Lhss.Count == 1 && assign.Rhss.Count == 1);

                    AssignLhs lhs = assign.Lhss.ElementAt(0);
                    Expr rhs = assign.Rhss.ElementAt(0);

                    if (!NonLocalAccessCollector.ContainsNonLocalAccess(rhs, GlobalVariables, TileStaticVariables) || (!NonLocalAccessCollector.ContainsNonLocalAccess(lhs, GlobalVariables, TileStaticVariables) && NonLocalAccessCollector.IsNonLocalAccess(rhs, GlobalVariables, TileStaticVariables)))
                    {
                        result.simpleCmds.Add(c);
                    }
                    else
                    {
                        rhs = PullOutNonLocalAccessesIntoTemps(result, rhs);
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
                    result.simpleCmds.Add(new AssertCmd(c.tok, PullOutNonLocalAccessesIntoTemps(result, (c as AssertCmd).Expr)));
                }
                else if (c is AssumeCmd)
                {
                    result.simpleCmds.Add(new AssumeCmd(c.tok, PullOutNonLocalAccessesIntoTemps(result, (c as AssumeCmd).Expr)));
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
                while (NonLocalAccessCollector.ContainsNonLocalAccess(WhileCommand.Guard, GlobalVariables, TileStaticVariables))
                {
                    AssignCmd assignToTemp;
                    LocalVariable tempDecl;
                    WhileCommand.Guard = ExtractLocalAccessToTemp(WhileCommand.Guard, out assignToTemp, out tempDecl);
                    result.simpleCmds.Add(assignToTemp);
                    KernelImplementation.LocVars.Add(tempDecl);
                }
                result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard, WhileCommand.Invariants, PullOutNonLocalAccesses(WhileCommand.Body));
            }
            else if(bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;
                Debug.Assert(IfCommand.elseIf == null); // We don't handle else if yet
                while (NonLocalAccessCollector.ContainsNonLocalAccess(IfCommand.Guard, GlobalVariables, TileStaticVariables))
                {
                    AssignCmd assignToTemp;
                    LocalVariable tempDecl;
                    IfCommand.Guard = ExtractLocalAccessToTemp(IfCommand.Guard, out assignToTemp, out tempDecl);
                    result.simpleCmds.Add(assignToTemp);
                    KernelImplementation.LocVars.Add(tempDecl);
                }
                result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, PullOutNonLocalAccesses(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? PullOutNonLocalAccesses(IfCommand.elseBlock) : null);
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }

            return result;

        }

        private Expr PullOutNonLocalAccessesIntoTemps(BigBlock result, Expr e)
        {
            while (NonLocalAccessCollector.ContainsNonLocalAccess(e, GlobalVariables, TileStaticVariables))
            {
                AssignCmd assignToTemp;
                LocalVariable tempDecl;
                e = ExtractLocalAccessToTemp(e, out assignToTemp, out tempDecl);
                result.simpleCmds.Add(assignToTemp);
                KernelImplementation.LocVars.Add(tempDecl);
            }
            return e;
        }

        private Expr ExtractLocalAccessToTemp(Expr rhs, out AssignCmd tempAssignment, out LocalVariable tempDeclaration)
        {
            NonLocalAccessExtractor extractor = new NonLocalAccessExtractor(TempCounter, GlobalVariables, TileStaticVariables);
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
                    // DuplicateParameters
                    Procedure proc = d as Procedure;
                    proc.InParams = DualiseVariableSequence(proc.InParams);
                    proc.OutParams = DualiseVariableSequence(proc.OutParams);
                    IdentifierExprSeq NewModifies = new IdentifierExprSeq();
                    foreach (IdentifierExpr v in proc.Modifies)
                    {
                        NewModifies.Add(new VariableDualiser(1).VisitIdentifierExpr((IdentifierExpr)v.Clone()));
                    }
                    foreach (IdentifierExpr v in proc.Modifies)
                    {
                        NewModifies.Add(new VariableDualiser(2).VisitIdentifierExpr((IdentifierExpr)v.Clone()));
                    }
                    proc.Modifies = NewModifies;

                    NewTopLevelDeclarations.Add(proc);

                    continue;

                }

                if (d is Implementation)
                {
                    // DuplicateParameters
                    Implementation impl = d as Implementation;
                    impl.InParams = DualiseVariableSequence(impl.InParams);
                    impl.OutParams = DualiseVariableSequence(impl.OutParams);
                    MakeDualLocalVariables(impl);
                    impl.StructuredStmts = MakeDual(impl.StructuredStmts);

                    NewTopLevelDeclarations.Add(impl);

                    continue;

                }

                if (d is Variable && ((d as Variable).IsMutable || IsThreadLocalIdConstant(d as Variable)))
                {
                    NewTopLevelDeclarations.Add(new VariableDualiser(1).VisitVariable((Variable)d.Clone()));
                    NewTopLevelDeclarations.Add(new VariableDualiser(2).VisitVariable((Variable)d.Clone()));

                    continue;
                }

                NewTopLevelDeclarations.Add(d);

            }

            Program.TopLevelDeclarations = NewTopLevelDeclarations;

        }

        private static VariableSeq DualiseVariableSequence(VariableSeq seq)
        {
            VariableSeq result = new VariableSeq();
            foreach (Variable v in seq)
            {
                result.Add(new VariableDualiser(1).VisitVariable((Variable)v.Clone()));
            }
            foreach (Variable v in seq)
            {
                result.Add(new VariableDualiser(2).VisitVariable((Variable)v.Clone()));
            }
            return result;
        }

        private void MakeKerenelPredicated()
        {
            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Procedure)
                {
                    if (d != KernelProcedure)
                    {
                        // Add predicate to start of parameter list
                        Procedure proc = d as Procedure;
                        VariableSeq NewIns = new VariableSeq();
                        NewIns.Add(new LocalVariable(proc.tok, new TypedIdent(proc.tok, "_P", Microsoft.Boogie.Type.Bool)));
                        foreach (Variable v in proc.InParams)
                        {
                            NewIns.Add(v);
                        }
                        proc.InParams = NewIns;
                    }

                }
                else if (d is Implementation)
                {
                    MakePredicated(d as Implementation, d != KernelImplementation);
                }
            }

        }

        private void MakePredicated(Implementation impl, bool AddPredicateParameter)
        {
            Expr Predicate;

            if (AddPredicateParameter)
            {
                VariableSeq NewIns = new VariableSeq();
                Variable PredicateVariable = new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_P", Microsoft.Boogie.Type.Bool));
                NewIns.Add(PredicateVariable);
                foreach (Variable v in impl.InParams)
                {
                    NewIns.Add(v);
                }
                impl.InParams = NewIns;
                Predicate = new IdentifierExpr(impl.tok, PredicateVariable);
            }
            else
            {
                Predicate = Expr.True;
            }

            WhileLoopCounter = 0;
            IfCounter = 0;
            RequiredHavocVariables = new HashSet<Microsoft.Boogie.Type>();
            impl.StructuredStmts = MakePredicated(impl.StructuredStmts, Predicate);
            AddPredicateLocalVariables(impl);
        }

        private StmtList MakeDual(StmtList stmtList)
        {
            Contract.Requires(stmtList != null);

            StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

            foreach (BigBlock bodyBlock in stmtList.BigBlocks)
            {
                result.BigBlocks.Add(MakeDual(bodyBlock));
            }

            return result;
        }

        private BigBlock MakeDual(BigBlock bb)
        {
            // Not sure what to do about the transfer command

            BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is CallCmd)
                {
                    CallCmd Call = c as CallCmd;

                    List<Expr> newIns = new List<Expr>();
                    foreach (Expr e in Call.Ins)
                    {
                        newIns.Add(new VariableDualiser(1).VisitExpr(e));
                    }
                    foreach (Expr e in Call.Ins)
                    {
                        newIns.Add(new VariableDualiser(2).VisitExpr(e));
                    }

                    List<IdentifierExpr> newOuts = new List<IdentifierExpr>();
                    foreach (IdentifierExpr ie in Call.Outs)
                    {
                        newOuts.Add(new VariableDualiser(1).VisitIdentifierExpr(ie.Clone() as IdentifierExpr) as IdentifierExpr);
                    }
                    foreach (IdentifierExpr ie in Call.Outs)
                    {
                        newOuts.Add(new VariableDualiser(2).VisitIdentifierExpr(ie.Clone() as IdentifierExpr) as IdentifierExpr);
                    }

                    CallCmd NewCallCmd = new CallCmd(Call.tok, Call.callee, newIns, newOuts);

                    result.simpleCmds.Add(NewCallCmd);
                }
                else if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;

                    Debug.Assert(assign.Lhss.Count == 1 && assign.Rhss.Count == 1);

                    List<AssignLhs> newLhss = new List<AssignLhs>();

                    newLhss.Add(new VariableDualiser(1).Visit(assign.Lhss.ElementAt(0).Clone() as AssignLhs) as AssignLhs);
                    newLhss.Add(new VariableDualiser(2).Visit(assign.Lhss.ElementAt(0).Clone() as AssignLhs) as AssignLhs);

                    List<Expr> newRhss = new List<Expr>();

                    newRhss.Add(new VariableDualiser(1).VisitExpr(assign.Rhss.ElementAt(0).Clone() as Expr));
                    newRhss.Add(new VariableDualiser(2).VisitExpr(assign.Rhss.ElementAt(0).Clone() as Expr));

                    AssignCmd newAssign = new AssignCmd(assign.tok, newLhss, newRhss);

                    result.simpleCmds.Add(newAssign);
                }
                else if (c is HavocCmd)
                {
                    HavocCmd havoc = c as HavocCmd;
                    Debug.Assert(havoc.Vars.Length == 1);
                    HavocCmd newHavoc = new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                        (IdentifierExpr)(new VariableDualiser(1).VisitIdentifierExpr(havoc.Vars[0].Clone() as IdentifierExpr)), 
                        (IdentifierExpr)(new VariableDualiser(2).VisitIdentifierExpr(havoc.Vars[0].Clone() as IdentifierExpr))
                    }));
                    result.simpleCmds.Add(newHavoc);
                }
                else if (c is AssertCmd)
                {
                    AssertCmd ass = c as AssertCmd;
                    result.simpleCmds.Add(new AssertCmd(c.tok, Expr.And(new VariableDualiser(1).VisitExpr(ass.Expr.Clone() as Expr), new VariableDualiser(2).VisitExpr(ass.Expr.Clone() as Expr))));
                }
                else if (c is AssumeCmd)
                {
                    AssumeCmd ass = c as AssumeCmd;
                    result.simpleCmds.Add(new AssumeCmd(c.tok, Expr.And(new VariableDualiser(1).VisitExpr(ass.Expr.Clone() as Expr), new VariableDualiser(2).VisitExpr(ass.Expr.Clone() as Expr))));
                }
                else
                {
                    Debug.Assert(false);
                }
            }

            if (bb.ec is WhileCmd)
            {
                result.ec = new WhileCmd(bb.ec.tok, Expr.Or(new VariableDualiser(1).VisitExpr((bb.ec as WhileCmd).Guard), new VariableDualiser(2).VisitExpr((bb.ec as WhileCmd).Guard)), (bb.ec as WhileCmd).Invariants, MakeDual((bb.ec as WhileCmd).Body));
            }
            else
            {
                Debug.Assert(bb.ec == null);
            }

            return result;

        }

        private void MakeDualLocalVariables(Implementation impl)
        {
            VariableSeq NewLocalVars = new VariableSeq();

            foreach (LocalVariable v in impl.LocVars)
            {
                NewLocalVars.Add(new LocalVariable(v.tok, new TypedIdent(v.tok, v.Name + "$1", v.TypedIdent.Type)));
                NewLocalVars.Add(new LocalVariable(v.tok, new TypedIdent(v.tok, v.Name + "$2", v.TypedIdent.Type)));
            }

            impl.LocVars = NewLocalVars;
        }

        private void AddPredicateLocalVariables(Implementation impl)
        {
            for (int i = 0; i < IfCounter; i++)
            {
                impl.LocVars.Add(new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_P" + i, Microsoft.Boogie.Type.Bool)));
            }
            for (int i = 0; i < WhileLoopCounter; i++)
            {
                impl.LocVars.Add(new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_LC" + i, Microsoft.Boogie.Type.Bool)));
            }
            foreach (Microsoft.Boogie.Type t in RequiredHavocVariables)
            {
                impl.LocVars.Add(new LocalVariable(impl.tok, new TypedIdent(impl.tok, "_HAVOC_" + t.ToString(), t)));
            }

        }

        private StmtList MakePredicated(StmtList sl, Expr predicate)
        {
            StmtList result = new StmtList(new List<BigBlock>(), sl.EndCurly);

            foreach (BigBlock bodyBlock in sl.BigBlocks)
            {
                List<BigBlock> newBigBlocks = MakePredicated(bodyBlock, predicate);
                foreach (BigBlock newBigBlock in newBigBlocks)
                {
                    result.BigBlocks.Add(newBigBlock);
                }
            }

            return result;

        }

        private List<BigBlock> MakePredicated(BigBlock b, Expr IncomingPredicate)
        {
            // Not sure what to do about the transfer command

            List<BigBlock> result = new List<BigBlock>();

            BigBlock firstBigBlock = new BigBlock(b.tok, b.LabelName, new CmdSeq(), null, b.tc);
            result.Add(firstBigBlock);

            foreach (Cmd c in b.simpleCmds)
            {
                if (c is CallCmd)
                {

                    CallCmd Call = c as CallCmd;

                    List<Expr> NewIns = new List<Expr>();
                    NewIns.Add(IncomingPredicate);

                    foreach (Expr e in Call.Ins)
                    {
                        NewIns.Add(e);
                    }

                    CallCmd NewCallCmd = new CallCmd(Call.tok, Call.callee, NewIns, Call.Outs);

                    firstBigBlock.simpleCmds.Add(NewCallCmd);
                } 
                else if (IncomingPredicate.Equals(Expr.True))
                {
                    firstBigBlock.simpleCmds.Add(c);
                }
                else if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;
                    Debug.Assert(assign.Lhss.Count == 1 && assign.Rhss.Count == 1);

                    ExprSeq iteArgs = new ExprSeq();
                    iteArgs.Add(IncomingPredicate);
                    iteArgs.Add(assign.Rhss.ElementAt(0));
                    iteArgs.Add(assign.Lhss.ElementAt(0).AsExpr);
                    NAryExpr ite = new NAryExpr(assign.tok, new IfThenElse(assign.tok), iteArgs);

                    List<Expr> newRhs = new List<Expr>();
                    newRhs.Add(ite);

                    AssignCmd newAssign = new AssignCmd(assign.tok, assign.Lhss, newRhs);

                    firstBigBlock.simpleCmds.Add(newAssign);
                }
                else if (c is HavocCmd)
                {
                    HavocCmd havoc = c as HavocCmd;
                    Debug.Assert(havoc.Vars.Length == 1);

                    Microsoft.Boogie.Type type = havoc.Vars[0].Decl.TypedIdent.Type;
                    Debug.Assert(type != null);

                    RequiredHavocVariables.Add(type);

                    IdentifierExpr HavocTempExpr = new IdentifierExpr(havoc.tok, new LocalVariable(havoc.tok, new TypedIdent(havoc.tok, "_HAVOC_" + type.ToString(), type)));
                    firstBigBlock.simpleCmds.Add(new HavocCmd(havoc.tok, new IdentifierExprSeq(new IdentifierExpr[] { 
                        HavocTempExpr 
                    })));

                    List<AssignLhs> lhss = new List<AssignLhs>();
                    lhss.Add(new SimpleAssignLhs(havoc.tok, havoc.Vars[0]));

                    List<Expr> rhss = new List<Expr>();
                    rhss.Add(new NAryExpr(havoc.tok, new IfThenElse(havoc.tok), new ExprSeq(new Expr[] { IncomingPredicate, HavocTempExpr, havoc.Vars[0] })));

                    firstBigBlock.simpleCmds.Add(new AssignCmd(havoc.tok, lhss, rhss));

                }
                else
                {
                    Debug.Assert(false);
                }
            }

            if (b.ec is WhileCmd)
            {
                string LoopPredicate = "_LC" + WhileLoopCounter;
                WhileLoopCounter++;

                IdentifierExpr PredicateExpr = new IdentifierExpr(b.ec.tok, new LocalVariable(b.ec.tok, new TypedIdent(b.ec.tok, LoopPredicate, Microsoft.Boogie.Type.Bool)));
                Expr GuardExpr = (b.ec as WhileCmd).Guard;

                List<AssignLhs> WhilePredicateLhss = new List<AssignLhs>();
                WhilePredicateLhss.Add(new SimpleAssignLhs(b.ec.tok, PredicateExpr));

                List<Expr> WhilePredicateRhss = new List<Expr>();
                WhilePredicateRhss.Add(IncomingPredicate.Equals(Expr.True) ? GuardExpr : Expr.And(IncomingPredicate, GuardExpr));

                firstBigBlock.simpleCmds.Add(new AssignCmd(b.ec.tok, WhilePredicateLhss, WhilePredicateRhss));

                WhileCmd NewWhile = new WhileCmd(b.ec.tok, PredicateExpr, (b.ec as WhileCmd).Invariants, MakePredicated((b.ec as WhileCmd).Body, PredicateExpr));

                List<Expr> UpdatePredicateRhss = new List<Expr>();
                UpdatePredicateRhss.Add(Expr.And(PredicateExpr, GuardExpr));

                CmdSeq updateCmd = new CmdSeq();
                updateCmd.Add(new AssignCmd(b.ec.tok, WhilePredicateLhss, UpdatePredicateRhss));

                NewWhile.Body.BigBlocks.Add(new BigBlock(b.ec.tok, "update_" + LoopPredicate, updateCmd, null, null));

                firstBigBlock.ec = NewWhile;

            }
            else if (b.ec is IfCmd)
            {
                IfCmd IfCommand = b.ec as IfCmd;

                string IfPredicate = "_P" + IfCounter;
                IfCounter++;

                IdentifierExpr PredicateExpr = new IdentifierExpr(b.ec.tok, new LocalVariable(b.ec.tok, new TypedIdent(b.ec.tok, IfPredicate, Microsoft.Boogie.Type.Bool)));
                Expr GuardExpr = IfCommand.Guard;

                List<AssignLhs> IfPredicateLhss = new List<AssignLhs>();
                IfPredicateLhss.Add(new SimpleAssignLhs(b.ec.tok, PredicateExpr));

                List<Expr> IfPredicateRhss = new List<Expr>();
                IfPredicateRhss.Add(GuardExpr);

                firstBigBlock.simpleCmds.Add(new AssignCmd(b.ec.tok, IfPredicateLhss, IfPredicateRhss));

                Debug.Assert(IfCommand.elseIf == null); // We need to preprocess these away

                StmtList PredicatedThen = MakePredicated(IfCommand.thn, Expr.And(IncomingPredicate, PredicateExpr));

                foreach (BigBlock bb in PredicatedThen.BigBlocks)
                {
                    result.Add(bb);
                }

                if (IfCommand.elseBlock != null)
                {
                    StmtList PredicatedElse = MakePredicated(IfCommand.elseBlock, Expr.And(IncomingPredicate, Expr.Not(PredicateExpr)));

                    foreach (BigBlock bb in PredicatedElse.BigBlocks)
                    {
                        result.Add(bb);
                    }
                }




            }
            else
            {
                Debug.Assert(b.ec == null);
            }

            return result;
        }

        private void CheckKernelParameters()
        {
            if (KernelProcedure.InParams.Length != 0)
            {
                Error(KernelProcedure.tok, "Kernel should not take any parameters");
            }
            if (KernelProcedure.OutParams.Length != 0)
            {
                Error(KernelProcedure.tok, "Kernel should not take return anything");
            }
        }


        private int Check()
        {
            BarrierProcedure = CheckExactlyOneBarrierProcedure();
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

            FindNonLocalVariables(Program);

            CheckKernelImplementation();

            if (!KernelHasIdX())
            {
                Error(KernelProcedure.tok, "Kernel must declare global constant '" + _X_name + "'");
            }

            if (!KernelHasTileSizeX())
            {
                Error(KernelProcedure.tok, "Kernel must declare global constant '" + _TILE_SIZE_X_name + "'");
            }

            if (!KernelHasNumTilesX())
            {
                Error(KernelProcedure.tok, "Kernel must declare global constant '" + _NUM_TILES_X_name + "'");
            }

            if (!KernelHasTileIdX())
            {
                Error(KernelProcedure.tok, "Kernel must declare global constant '" + _TILE_X_name + "'");
            }

            if (KernelHasIdY() || KernelHasTileSizeY() || KernelHasNumTilesY() || KernelHasTileIdY())
            {

                if (!KernelHasIdY())
                {
                    Error(KernelProcedure.tok, "2D kernel must declare global constant '" + _Y_name + "'");
                }

                if (!KernelHasTileSizeY())
                {
                    Error(KernelProcedure.tok, "2D kernel must declare global constant '" + _TILE_SIZE_Y_name + "'");
                }

                if (!KernelHasNumTilesY())
                {
                    Error(KernelProcedure.tok, "2D kernel must declare global constant '" + _NUM_TILES_Y_name + "'");
                }

                if (!KernelHasTileIdY())
                {
                    Error(KernelProcedure.tok, "2D kernel must declare global constant '" + _TILE_Y_name + "'");
                }

            }

            if (KernelHasIdZ() || KernelHasTileSizeZ() || KernelHasNumTilesZ() || KernelHasTileIdZ())
            {

                if (!KernelHasIdY())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _Y_name + "'");
                }

                if (!KernelHasTileSizeY())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _TILE_SIZE_Y_name + "'");
                }

                if (!KernelHasNumTilesY())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _NUM_TILES_Y_name + "'");
                }

                if (!KernelHasTileIdY())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _TILE_Y_name + "'");
                }

                if (!KernelHasIdZ())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _Z_name + "'");
                }

                if (!KernelHasTileSizeZ())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _TILE_SIZE_Z_name + "'");
                }

                if (!KernelHasNumTilesZ())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _NUM_TILES_Z_name + "'");
                }

                if (!KernelHasTileIdZ())
                {
                    Error(KernelProcedure.tok, "3D kernel must declare global constant '" + _TILE_Z_name + "'");
                }

            }

            return ErrorCount;
        }

        private bool HasNamedConstant(string dimension, string Name)
        {
            foreach (Declaration d in Program.TopLevelDeclarations)
            {
                if (d is Variable && (d as Variable).Name.Equals(Name + dimension))
                {
                    Variable v = d as Variable;
                    if (v is Constant && IsIntOrBv32(v.TypedIdent.Type))
                    {
                        return true;
                    }
                    else
                    {
                        Error(v.tok, "Declaration '" + Name + dimension + "' must be a constant integer");
                    }
                }
            }
            return false;
        }

        private bool HasTileId(string dimension)
        {
            return HasNamedConstant(dimension, "_tile_");
        }

        private bool HasNumTiles(string dimension)
        {
            return HasNamedConstant(dimension, "NUM_TILES_");
        }

        private bool HasTileSize(string dimension)
        {
            return HasNamedConstant(dimension, "TILE_SIZE_");
        }

        public static bool IsThreadLocalIdConstant(Variable variable)
        {
            return variable is Constant && (variable.Name.Equals(_X_name) || variable.Name.Equals(_Y_name) || variable.Name.Equals(_Z_name));
        }

    }
}
