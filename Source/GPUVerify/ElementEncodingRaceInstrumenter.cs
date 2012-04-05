using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify
{
    class ElementEncodingRaceInstrumenter : RaceInstrumenterBase
    {

        public ElementEncodingRaceInstrumenter() : base()
        {
        }



        protected override void AddLogAccessProcedure(Variable v, string ReadOrWrite)
        {
            Variable XParameterVariable;
            Variable YParameterVariable;
            Variable ZParameterVariable;
            Procedure LogReadOrWriteProcedure;

            MakeLogAccessProcedureHeader(v, ReadOrWrite, out XParameterVariable, out YParameterVariable, out ZParameterVariable, out LogReadOrWriteProcedure);

            IdentifierExprSeq modifies = LogReadOrWriteProcedure.Modifies;
            Variable ReadOrWriteHasOccurredVariable = MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite);
            Variable ReadOrWriteOffsetXVariable = null;
            Variable ReadOrWriteOffsetYVariable = null;
            Variable ReadOrWriteOffsetZVariable = null;

            if (XParameterVariable != null)
            {
                ReadOrWriteOffsetXVariable = GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite);
                modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteOffsetXVariable));
            }
            if (YParameterVariable != null)
            {
                Debug.Assert(XParameterVariable != null);
                ReadOrWriteOffsetYVariable = GPUVerifier.MakeOffsetYVariable(v, ReadOrWrite);
                modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteOffsetYVariable));
            }
            if (ZParameterVariable != null)
            {
                Debug.Assert(XParameterVariable != null);
                Debug.Assert(YParameterVariable != null);
                ReadOrWriteOffsetZVariable = GPUVerifier.MakeOffsetZVariable(v, ReadOrWrite);
                modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteOffsetZVariable));
            }

            modifies.Add(new IdentifierExpr(v.tok, ReadOrWriteHasOccurredVariable));

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

            Implementation LogReadOrWriteImplementation = new Implementation(v.tok, "_LOG_" + ReadOrWrite + "_" + v.Name, new TypeVariableSeq(), LogReadOrWriteProcedure.InParams, new VariableSeq(), locals, statements);
            LogReadOrWriteImplementation.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

            LogReadOrWriteImplementation.Proc = LogReadOrWriteProcedure;

            verifier.Program.TopLevelDeclarations.Add(LogReadOrWriteProcedure);
            verifier.Program.TopLevelDeclarations.Add(LogReadOrWriteImplementation);
        }

        protected override void AddLogRaceDeclarations(Variable v, String ReadOrWrite, out IdentifierExprSeq ResetAtBarrier, out IdentifierExprSeq ModifiedAtLog)
        {
            ModifiedAtLog = new IdentifierExprSeq();
            ResetAtBarrier = new IdentifierExprSeq();

            Variable AccessHasOccurred = new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_HAS_OCCURRED_" + v.Name, Microsoft.Boogie.Type.Bool));

            if (CommandLineOptions.Symmetry && ReadOrWrite.Equals("READ"))
            {
                verifier.HalfDualisedVariableNames.Add(AccessHasOccurred.Name);
            }

            ModifiedAtLog.Add(new IdentifierExpr(v.tok, AccessHasOccurred));
            ResetAtBarrier.Add(new IdentifierExpr(v.tok, AccessHasOccurred));

            verifier.Program.TopLevelDeclarations.Add(AccessHasOccurred);
            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);

                Variable AccessOffsetX = GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite);

                if (CommandLineOptions.Symmetry && ReadOrWrite.Equals("READ"))
                {
                    verifier.HalfDualisedVariableNames.Add(AccessOffsetX.Name);
                }

                ModifiedAtLog.Add(new IdentifierExpr(v.tok, AccessOffsetX));
                verifier.Program.TopLevelDeclarations.Add(AccessOffsetX);

                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(GPUVerifier.IsIntOrBv32(mt2.Arguments[0]));

                    Variable AccessOffsetY = GPUVerifier.MakeOffsetYVariable(v, ReadOrWrite);

                    if (CommandLineOptions.Symmetry && ReadOrWrite.Equals("READ"))
                    {
                        verifier.HalfDualisedVariableNames.Add(AccessOffsetY.Name);
                    }

                    ModifiedAtLog.Add(new IdentifierExpr(v.tok, AccessOffsetY));
                    verifier.Program.TopLevelDeclarations.Add(AccessOffsetY);

                    if (mt2.Result is MapType)
                    {
                        MapType mt3 = mt2.Arguments[0] as MapType;
                        Debug.Assert(mt3.Arguments.Length == 1);
                        Debug.Assert(GPUVerifier.IsIntOrBv32(mt3.Arguments[0]));
                        Debug.Assert(!(mt3.Result is MapType));

                        Variable AccessOffsetZ = GPUVerifier.MakeOffsetZVariable(v, ReadOrWrite);

                        if (CommandLineOptions.Symmetry && ReadOrWrite.Equals("READ"))
                        {
                            verifier.HalfDualisedVariableNames.Add(AccessOffsetZ.Name);
                        }

                        ModifiedAtLog.Add(new IdentifierExpr(v.tok, AccessOffsetZ));
                        verifier.Program.TopLevelDeclarations.Add(AccessOffsetZ);
                    }
                }
            }

        }


        private static AssignCmd MakeConditionalAssignment(Variable lhs, Expr condition, Expr rhs)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            lhss.Add(new SimpleAssignLhs(lhs.tok, new IdentifierExpr(lhs.tok, lhs)));
            rhss.Add(new NAryExpr(rhs.tok, new IfThenElse(rhs.tok), new ExprSeq(new Expr[] { condition, rhs, new IdentifierExpr(lhs.tok, lhs) })));
            return new AssignCmd(lhs.tok, lhss, rhss);
        }

        protected override void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v, string AccessType)
        {
            IdentifierExpr AccessOccurred1 = new IdentifierExpr(tok, 
                new VariableDualiser(1, null, null).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, AccessType)));
            IdentifierExpr AccessOccurred2 = new IdentifierExpr(tok,
                new VariableDualiser(2, null, null).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, AccessType)));

            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();

            lhss.Add(new SimpleAssignLhs(tok, AccessOccurred1));
            rhss.Add(Expr.False);

            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                lhss.Add(new SimpleAssignLhs(tok, AccessOccurred2));
                rhss.Add(Expr.False);
            }

            bb.simpleCmds.Add(new AssignCmd(tok, lhss, rhss));
        }

        public override void CheckForRaces(BigBlock bb, Variable v, bool ReadWriteOnly)
        {
            if (!ReadWriteOnly)
            {
                bb.simpleCmds.Add(new AssertCmd(v.tok, Expr.Not(GenerateRaceCondition(v, "WRITE", "WRITE"))));
            }
            bb.simpleCmds.Add(new AssertCmd(v.tok, Expr.Not(GenerateRaceCondition(v, "READ", "WRITE"))));
            if (!CommandLineOptions.Symmetry)
            {
                bb.simpleCmds.Add(new AssertCmd(v.tok, Expr.Not(GenerateRaceCondition(v, "WRITE", "READ"))));
            }
        }

        protected override Expr GenerateRaceCondition(Variable v, string FirstAccessType, string SecondAccessType)
        {
            Expr RaceCondition = Expr.And(
                new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, FirstAccessType))),
                new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(MakeReadOrWriteHasOccurredVariable(v, SecondAccessType))));

            if (GPUVerifier.HasXDimension(v))
            {
                RaceCondition = Expr.And(RaceCondition, Expr.Eq(
                    new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, FirstAccessType))),
                    new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, SecondAccessType)))
                ));
            }

            if (GPUVerifier.HasYDimension(v))
            {
                RaceCondition = Expr.And(RaceCondition, Expr.Eq(
                    new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeOffsetYVariable(v, FirstAccessType))),
                    new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(GPUVerifier.MakeOffsetYVariable(v, SecondAccessType)))
                    ));
            }

            if (GPUVerifier.HasZDimension(v))
            {
                RaceCondition = Expr.And(RaceCondition, Expr.Eq(
                    new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeOffsetZVariable(v, FirstAccessType))),
                    new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(GPUVerifier.MakeOffsetZVariable(v, SecondAccessType)))
                    ));
            }

            if (FirstAccessType.Equals("WRITE") && SecondAccessType.Equals("WRITE") && !verifier.ArrayModelledAdversarially(v))
            {
                RaceCondition = Expr.And(RaceCondition, Expr.Neq(
                    MakeWrittenIndex(v, 1),
                    MakeWrittenIndex(v, 2)
                    ));
            }

            return RaceCondition;
        }

        private static Expr MakeWrittenIndex(Variable v, int OneOrTwo)
        {
            Expr result = new IdentifierExpr(v.tok, new VariableDualiser(OneOrTwo, null, null).VisitVariable(v.Clone() as Variable));

            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);

                result = Expr.Select(result,
                    new Expr[] { new IdentifierExpr(v.tok, new VariableDualiser(OneOrTwo, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, "WRITE"))) });

                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(GPUVerifier.IsIntOrBv32(mt2.Arguments[0]));

                    result = Expr.Select(result,
                        new Expr[] { new IdentifierExpr(v.tok, new VariableDualiser(OneOrTwo, null, null).VisitVariable(GPUVerifier.MakeOffsetYVariable(v, "WRITE"))) });

                    if (mt2.Result is MapType)
                    {
                        MapType mt3 = mt2.Arguments[0] as MapType;
                        Debug.Assert(mt3.Arguments.Length == 1);
                        Debug.Assert(GPUVerifier.IsIntOrBv32(mt3.Arguments[0]));
                        Debug.Assert(!(mt3.Result is MapType));

                        result = Expr.Select(result,
                            new Expr[] { new IdentifierExpr(v.tok, new VariableDualiser(OneOrTwo, null, null).VisitVariable(GPUVerifier.MakeOffsetZVariable(v, "WRITE"))) });

                    }
                }
            }

            return result;

        }

        internal static GlobalVariable MakeReadOrWriteHasOccurredVariable(Variable v, string ReadOrWrite)
        {
            return new GlobalVariable(v.tok, new TypedIdent(v.tok, "_" + ReadOrWrite + "_HAS_OCCURRED_" + v.Name, Microsoft.Boogie.Type.Bool));
        }

        protected override void AddRequiresNoPendingAccess(Variable v)
        {
            IdentifierExpr ReadAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, "READ")));
            IdentifierExpr ReadAccessOccurred2 = new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, "READ")));
            IdentifierExpr WriteAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, "WRITE")));
            IdentifierExpr WriteAccessOccurred2 = new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, "WRITE")));

            if (CommandLineOptions.Symmetry)
            {
                verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.And(Expr.Not(WriteAccessOccurred1), Expr.Not(WriteAccessOccurred2)))));
            }
            else
            {
                verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.And(Expr.Not(ReadAccessOccurred2), Expr.And(Expr.Not(WriteAccessOccurred1), Expr.Not(WriteAccessOccurred2))))));
            }
        }



        protected override void AddNoReadOrWriteCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            verifier.AddCandidateInvariant(wc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
        }

        protected override Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwo)
        {
            Variable ReadOrWriteHasOccurred = ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite);
            ReadOrWriteHasOccurred.Name = ReadOrWriteHasOccurred.Name + "$" + OneOrTwo;
            ReadOrWriteHasOccurred.TypedIdent.Name = ReadOrWriteHasOccurred.TypedIdent.Name + "$" + OneOrTwo;
            Expr expr = Expr.Not(new IdentifierExpr(v.tok, ReadOrWriteHasOccurred));
            return expr;
        }


        protected override void AddAccessedOffsetIsThreadGlobalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadGlobalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateInvariant(wc, expr);
            }
        }

        protected override void AddAccessedOffsetIsThreadLocalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateInvariant(wc, expr);
            }
        }

        private Expr AccessedOffsetIsThreadLocalIdExpr(Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = null;
            if (GPUVerifier.HasXDimension(v) && GPUVerifier.IndexTypeOfXDimension(v).Equals(verifier.GetTypeOfIdX()))
            {
                expr = Expr.Imp(
                        new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite))), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread))));
            }
            return expr;
        }

        private Expr AccessedOffsetIsThreadGlobalIdExpr(Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = null;
            if (GPUVerifier.HasXDimension(v) && GPUVerifier.IndexTypeOfXDimension(v).Equals(verifier.GetTypeOfIdX()))
            {
                expr = Expr.Imp(
                        new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(
                            new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite))),
                            GlobalIdExpr("X", Thread)
                            )
                            );
            }
            return expr;
        }

        private Expr GlobalIdExpr(string dimension, int Thread)
        {
            return GPUVerifier.MakeBitVectorBinaryBitVector("BV32_ADD", GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL",
                            new IdentifierExpr(Token.NoToken, verifier.GetGroupId(dimension)), new IdentifierExpr(Token.NoToken, verifier.GetGroupSize(dimension))),
                                new IdentifierExpr(Token.NoToken, verifier.MakeThreadId(Token.NoToken, dimension, Thread)));
        }

        private Expr GlobalSizeExpr(string dimension)
        {
            return GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL",
                            new IdentifierExpr(Token.NoToken, verifier.GetNumGroups(dimension)), 
                            new IdentifierExpr(Token.NoToken, verifier.GetGroupSize(dimension)));
        }

        protected override void AddAccessedOffsetIsThreadFlattened2DLocalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadFlattened2DLocalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateInvariant(wc, expr);
            }
        }

        private Expr AccessedOffsetIsThreadFlattened2DLocalIdExpr(Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = null;
            if (GPUVerifier.HasXDimension(v) && GPUVerifier.IndexTypeOfXDimension(v).Equals(verifier.GetTypeOfIdX()))
            {
                expr = Expr.Imp(
                        new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(
                            new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite))),
                            GPUVerifier.MakeBitVectorBinaryBitVector("BV32_ADD", GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL",
                            new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "Y", Thread)), new IdentifierExpr(v.tok, verifier.GetGroupSize("X"))),
                                new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread)))
                            )
                            );
            }
            return expr;
        }

        protected override void AddAccessedOffsetIsThreadFlattened2DGlobalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadFlattened2DGlobalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateInvariant(wc, expr);
            }
        }

        private Expr AccessedOffsetIsThreadFlattened2DGlobalIdExpr(Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = null;
            if (GPUVerifier.HasXDimension(v) && GPUVerifier.IndexTypeOfXDimension(v).Equals(verifier.GetTypeOfIdX()))
            {
                expr = Expr.Imp(
                        new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(ElementEncodingRaceInstrumenter.MakeReadOrWriteHasOccurredVariable(v, ReadOrWrite))),
                        Expr.Eq(
                            new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite))),
                            GPUVerifier.MakeBitVectorBinaryBitVector("BV32_ADD", GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL",
                            GlobalIdExpr("Y", Thread), GlobalSizeExpr("X")),
                                GlobalIdExpr("X", Thread))
                            )
                            );
            }
            return expr;
        }


        protected override void AddAccessedOffsetIsThreadLocalIdCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateRequires(Proc, expr);
            }
        }

        protected override void AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateEnsures(Proc, expr);
            }
        }


    }
}
