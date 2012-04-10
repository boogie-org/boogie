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
            Variable ReadOrWriteHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite);
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

            Variable AccessHasOccurred = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite);

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
                new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, AccessType)));
            IdentifierExpr AccessOccurred2 = new IdentifierExpr(tok,
                new VariableDualiser(2, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, AccessType)));

            if (CommandLineOptions.AssignAtBarriers)
            {

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
            else
            {
                bb.simpleCmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(AccessOccurred1)));
                if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
                {
                    bb.simpleCmds.Add(new AssumeCmd(Token.NoToken, Expr.Not(AccessOccurred2)));
                }
            }
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
                new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, FirstAccessType))),
                new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, SecondAccessType))));

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

        protected override void AddRequiresNoPendingAccess(Variable v)
        {
            IdentifierExpr ReadAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ")));
            IdentifierExpr ReadAccessOccurred2 = new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ")));
            IdentifierExpr WriteAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE")));
            IdentifierExpr WriteAccessOccurred2 = new IdentifierExpr(v.tok, new VariableDualiser(2, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE")));

            if (CommandLineOptions.Symmetry)
            {
                verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.And(Expr.Not(WriteAccessOccurred1), Expr.Not(WriteAccessOccurred2)))));
            }
            else
            {
                verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.And(Expr.Not(ReadAccessOccurred2), Expr.And(Expr.Not(WriteAccessOccurred1), Expr.Not(WriteAccessOccurred2))))));
            }
        }

        protected override Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwo)
        {
            Variable ReadOrWriteHasOccurred = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite);
            ReadOrWriteHasOccurred.Name = ReadOrWriteHasOccurred.Name + "$" + OneOrTwo;
            ReadOrWriteHasOccurred.TypedIdent.Name = ReadOrWriteHasOccurred.TypedIdent.Name + "$" + OneOrTwo;
            Expr expr = Expr.Not(new IdentifierExpr(v.tok, ReadOrWriteHasOccurred));
            return expr;
        }


        protected override void AddAccessedOffsetIsThreadGlobalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            Expr expr = AccessedOffsetIsThreadGlobalIdExpr(v, ReadOrWrite, 1);

            if (ReadOrWrite.Equals("WRITE") || !CommandLineOptions.Symmetry)
            {
                expr = Expr.And(expr, AccessedOffsetIsThreadGlobalIdExpr(v, ReadOrWrite, 2));
            }

            verifier.AddCandidateInvariant(wc, expr, "accessed offset is global id");
        }

        protected override void AddAccessedOffsetIsThreadLocalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            Expr expr = AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, 1);

            if (ReadOrWrite.Equals("WRITE") || !CommandLineOptions.Symmetry)
            {
                expr = Expr.And(expr, AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, 2));
            }

            verifier.AddCandidateInvariant(wc, expr, "accessed offset is local id");
        }

        private Expr AccessedOffsetIsThreadLocalIdExpr(Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = null;
            if (GPUVerifier.HasXDimension(v) && GPUVerifier.IndexTypeOfXDimension(v).Equals(verifier.GetTypeOfIdX()))
            {
                expr = Expr.Imp(
                        new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite))),
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
                        new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite))),
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
            return new VariableDualiser(Thread, null, null).VisitExpr(verifier.GlobalIdExpr(dimension).Clone() as Expr);
        }

        private Expr GlobalSizeExpr(string dimension)
        {
            return GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL",
                            new IdentifierExpr(Token.NoToken, verifier.GetNumGroups(dimension)), 
                            new IdentifierExpr(Token.NoToken, verifier.GetGroupSize(dimension)));
        }

        protected override void AddAccessedOffsetIsThreadFlattened2DLocalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            Expr expr = AccessedOffsetIsThreadFlattened2DLocalIdExpr(v, ReadOrWrite, 1);
            if (ReadOrWrite.Equals("WRITE") || !CommandLineOptions.Symmetry)
            {
                expr = Expr.And(expr, AccessedOffsetIsThreadFlattened2DLocalIdExpr(v, ReadOrWrite, 2));
            }
            
            verifier.AddCandidateInvariant(wc, expr, "accessed offset is flattened 2D local id");
        }

        private Expr AccessedOffsetIsThreadFlattened2DLocalIdExpr(Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = null;
            if (GPUVerifier.HasXDimension(v) && GPUVerifier.IndexTypeOfXDimension(v).Equals(verifier.GetTypeOfIdX()))
            {
                expr = Expr.Imp(
                        AccessHasOccurred(v, ReadOrWrite, Thread),
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

        protected override void AddAccessedOffsetIsThreadFlattened2DGlobalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            Expr expr = AccessedOffsetIsThreadFlattened2DGlobalIdExpr(v, ReadOrWrite, 1);
            if (ReadOrWrite.Equals("WRITE") || !CommandLineOptions.Symmetry)
            {
                expr = Expr.And(expr, AccessedOffsetIsThreadFlattened2DGlobalIdExpr(v, ReadOrWrite, 2));
            }

            verifier.AddCandidateInvariant(wc, expr, "accessed offset is flattened 2D global id");
        }

        private Expr AccessedOffsetIsThreadFlattened2DGlobalIdExpr(Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = null;
            if (GPUVerifier.HasXDimension(v) && GPUVerifier.IndexTypeOfXDimension(v).Equals(verifier.GetTypeOfIdX()))
            {
                expr = Expr.Imp(
                        AccessHasOccurred(v, ReadOrWrite, Thread),
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

        protected override void AddAccessedOffsetInRangeCTimesLocalIdToCTimesLocalIdPlusC(WhileCmd wc, Variable v, Expr constant, string ReadOrWrite)
        {

            Expr expr = MakeCTimesLocalIdRangeExpression(v, constant, ReadOrWrite, 1);

            if (ReadOrWrite.Equals("WRITE") || !CommandLineOptions.Symmetry)
            {
                expr = Expr.And(expr, MakeCTimesLocalIdRangeExpression(v, constant, ReadOrWrite, 2));
            }

            verifier.AddCandidateInvariant(wc,
                expr, "accessed offset in range [ C*local_id, (C+1)*local_id )");
        }

        private Expr MakeCTimesLocalIdRangeExpression(Variable v, Expr constant, string ReadOrWrite, int Thread)
        {
            Expr CTimesLocalId = GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL", constant.Clone() as Expr, 
                new IdentifierExpr(Token.NoToken, verifier.MakeThreadId(Token.NoToken, "X", Thread)));

            Expr CTimesLocalIdPlusC = GPUVerifier.MakeBitVectorBinaryBitVector("BV32_ADD", GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL", constant.Clone() as Expr,
                new IdentifierExpr(Token.NoToken, verifier.MakeThreadId(Token.NoToken, "X", Thread))), constant.Clone() as Expr);

            Expr CTimesLocalIdLeqAccessedOffset = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LEQ", CTimesLocalId, OffsetXExpr(v, ReadOrWrite, Thread));

            Expr AccessedOffsetLtCTimesLocalIdPlusC = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LT", OffsetXExpr(v, ReadOrWrite, Thread), CTimesLocalIdPlusC);

            return Expr.Imp(
                    AccessHasOccurred(v, ReadOrWrite, Thread),
                    Expr.And(CTimesLocalIdLeqAccessedOffset, AccessedOffsetLtCTimesLocalIdPlusC));
        }

        private static IdentifierExpr AccessHasOccurred(Variable v, string ReadOrWrite, int Thread)
        {
            return new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite)));
        }

        private static IdentifierExpr OffsetXExpr(Variable v, string ReadOrWrite, int Thread)
        {
            return new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite)));
        }

        protected override void AddAccessedOffsetInRangeCTimesGlobalIdToCTimesGlobalIdPlusC(WhileCmd wc, Variable v, Expr constant, string ReadOrWrite)
        {
            Expr expr = MakeCTimesGloalIdRangeExpr(v, constant, ReadOrWrite, 1);

            if (ReadOrWrite.Equals("WRITE") || !CommandLineOptions.Symmetry)
            {
                expr = Expr.And(expr, MakeCTimesGloalIdRangeExpr(v, constant, ReadOrWrite, 2));
            }

            verifier.AddCandidateInvariant(wc,
                expr, "accessed offset in range [ C*global_id, (C+1)*global_id )");
        }

        private Expr MakeCTimesGloalIdRangeExpr(Variable v, Expr constant, string ReadOrWrite, int Thread)
        {
            Expr CTimesGlobalId = GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL", constant.Clone() as Expr,
                GlobalIdExpr("X", Thread));

            Expr CTimesGlobalIdPlusC = GPUVerifier.MakeBitVectorBinaryBitVector("BV32_ADD", GPUVerifier.MakeBitVectorBinaryBitVector("BV32_MUL", constant.Clone() as Expr,
                GlobalIdExpr("X", Thread)), constant.Clone() as Expr);

            Expr CTimesGlobalIdLeqAccessedOffset = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LEQ", CTimesGlobalId, OffsetXExpr(v, ReadOrWrite, Thread));

            Expr AccessedOffsetLtCTimesGlobalIdPlusC = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LT", OffsetXExpr(v, ReadOrWrite, Thread), CTimesGlobalIdPlusC);

            Expr implication = Expr.Imp(
                    AccessHasOccurred(v, ReadOrWrite, Thread),
                    Expr.And(CTimesGlobalIdLeqAccessedOffset, AccessedOffsetLtCTimesGlobalIdPlusC));
            return implication;
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
