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



        protected override void AddLogAccessProcedure(Variable v, string Access)
        {
            Procedure LogAccessProcedure = MakeLogAccessProcedureHeader(v, Access);

            Variable AccessHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, Access);
            Variable AccessOffsetXVariable = GPUVerifier.MakeOffsetXVariable(v, Access);

            Variable PredicateParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_P", Microsoft.Boogie.Type.Bool));

            Debug.Assert(v.TypedIdent.Type is MapType);
            MapType mt = v.TypedIdent.Type as MapType;
            Debug.Assert(mt.Arguments.Length == 1);
            Variable OffsetParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_offset", mt.Arguments[0]));
            Debug.Assert(!(mt.Result is MapType));

            VariableSeq locals = new VariableSeq();
            Variable TrackVariable = new LocalVariable(v.tok, new TypedIdent(v.tok, "track", Microsoft.Boogie.Type.Bool));
            locals.Add(TrackVariable);

            List<BigBlock> bigblocks = new List<BigBlock>();

            CmdSeq simpleCmds = new CmdSeq();

            simpleCmds.Add(new HavocCmd(v.tok, new IdentifierExprSeq(new IdentifierExpr[] { new IdentifierExpr(v.tok, TrackVariable) })));

            simpleCmds.Add(MakeConditionalAssignment(VariableForThread(1, AccessHasOccurredVariable), 
                Expr.And(new IdentifierExpr(v.tok, VariableForThread(1, PredicateParameter)), new IdentifierExpr(v.tok, TrackVariable)), Expr.True));
            simpleCmds.Add(MakeConditionalAssignment(VariableForThread(1, AccessOffsetXVariable), 
                Expr.And(new IdentifierExpr(v.tok, VariableForThread(1, PredicateParameter)), new IdentifierExpr(v.tok, TrackVariable)), 
                new IdentifierExpr(v.tok, VariableForThread(1, OffsetParameter))));

            if (Access.Equals("READ"))
            {
                // Check read by thread 2 does not conflict with write by thread 1
                Variable WriteHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE");
                Variable WriteOffsetXVariable = GPUVerifier.MakeOffsetXVariable(v, "WRITE");
                Expr WriteReadGuard = new IdentifierExpr(Token.NoToken, VariableForThread(2, PredicateParameter));
                WriteReadGuard = Expr.And(WriteReadGuard, new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteHasOccurredVariable)));
                WriteReadGuard = Expr.And(WriteReadGuard, Expr.Eq(new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteOffsetXVariable)), 
                                                new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter))));
                if (!verifier.ArrayModelledAdversarially(v))
                {
                    WriteReadGuard = Expr.And(WriteReadGuard, Expr.Neq(
                        MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteOffsetXVariable)), 1, "WRITE"),
                        MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter)), 2, "READ")
                        ));
                }

                if (verifier.NonLocalState.getGroupSharedVariables().Contains(v) && CommandLineOptions.InterGroupRaceChecking)
                {
                    WriteReadGuard = Expr.And(WriteReadGuard, verifier.ThreadsInSameGroup());
                }

                WriteReadGuard = Expr.Not(WriteReadGuard);
                simpleCmds.Add(new AssertCmd(Token.NoToken, WriteReadGuard));
            }
            else
            {
                Debug.Assert(Access.Equals("WRITE"));

                // Check write by thread 2 does not conflict with write by thread 1
                Variable WriteHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE");
                Variable WriteOffsetXVariable = GPUVerifier.MakeOffsetXVariable(v, "WRITE");

                Expr WriteWriteGuard = new IdentifierExpr(Token.NoToken, VariableForThread(2, PredicateParameter));
                WriteWriteGuard = Expr.And(WriteWriteGuard, new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteHasOccurredVariable)));
                WriteWriteGuard = Expr.And(WriteWriteGuard, Expr.Eq(new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteOffsetXVariable)),
                                                new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter))));
                if (!verifier.ArrayModelledAdversarially(v))
                {
                    WriteWriteGuard = Expr.And(WriteWriteGuard, Expr.Neq(
                        MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, VariableForThread(1, WriteOffsetXVariable)), 1, "WRITE"),
                        MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter)), 2, "WRITE")
                        ));
                }

                if (verifier.NonLocalState.getGroupSharedVariables().Contains(v) && CommandLineOptions.InterGroupRaceChecking)
                {
                    WriteWriteGuard = Expr.And(WriteWriteGuard, verifier.ThreadsInSameGroup());
                }

                WriteWriteGuard = Expr.Not(WriteWriteGuard);
                simpleCmds.Add(new AssertCmd(Token.NoToken, WriteWriteGuard));

                // Check write by thread 2 does not conflict with read by thread 1
                Variable ReadHasOccurredVariable = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ");
                Variable ReadOffsetXVariable = GPUVerifier.MakeOffsetXVariable(v, "READ");

                Expr ReadWriteGuard = new IdentifierExpr(Token.NoToken, VariableForThread(2, PredicateParameter));
                ReadWriteGuard = Expr.And(ReadWriteGuard, new IdentifierExpr(Token.NoToken, VariableForThread(1, ReadHasOccurredVariable)));
                ReadWriteGuard = Expr.And(ReadWriteGuard, Expr.Eq(new IdentifierExpr(Token.NoToken, VariableForThread(1, ReadOffsetXVariable)),
                                                new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter))));
                if (!verifier.ArrayModelledAdversarially(v))
                {
                    ReadWriteGuard = Expr.And(ReadWriteGuard, Expr.Neq(
                        MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, VariableForThread(1, ReadOffsetXVariable)), 1, "WRITE"),
                        MakeAccessedIndex(v, new IdentifierExpr(Token.NoToken, VariableForThread(2, OffsetParameter)), 2, "READ")
                        ));
                }

                if (verifier.NonLocalState.getGroupSharedVariables().Contains(v) && CommandLineOptions.InterGroupRaceChecking)
                {
                    ReadWriteGuard = Expr.And(ReadWriteGuard, verifier.ThreadsInSameGroup());
                }

                ReadWriteGuard = Expr.Not(ReadWriteGuard);
                simpleCmds.Add(new AssertCmd(Token.NoToken, ReadWriteGuard));

            }

            bigblocks.Add(new BigBlock(v.tok, "_LOG_" + Access + "", simpleCmds, null, null));

            LogAccessProcedure.Modifies.Add(new IdentifierExpr(Token.NoToken, VariableForThread(1, AccessHasOccurredVariable)));
            LogAccessProcedure.Modifies.Add(new IdentifierExpr(Token.NoToken, VariableForThread(1, AccessOffsetXVariable)));

            Implementation LogAccessImplementation = new Implementation(v.tok, "_LOG_" + Access + "_" + v.Name, new TypeVariableSeq(), LogAccessProcedure.InParams, new VariableSeq(), locals, new StmtList(bigblocks, v.tok));
            LogAccessImplementation.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

            LogAccessImplementation.Proc = LogAccessProcedure;

            verifier.Program.TopLevelDeclarations.Add(LogAccessProcedure);
            verifier.Program.TopLevelDeclarations.Add(LogAccessImplementation);
        }

        private Variable VariableForThread(int thread, Variable v)
        {
            return new VariableDualiser(thread, null, null).VisitVariable(v.Clone() as Variable);
        }

        protected override void AddLogRaceDeclarations(Variable v, String ReadOrWrite)
        {
            Variable AccessHasOccurred = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite);

            // Assumes full symmetry reduction

            verifier.Program.TopLevelDeclarations.Add(new VariableDualiser(1, null, null).VisitVariable(AccessHasOccurred.Clone() as Variable));

            Debug.Assert(v.TypedIdent.Type is MapType);
            MapType mt = v.TypedIdent.Type as MapType;
            Debug.Assert(mt.Arguments.Length == 1);

            Variable AccessOffsetX = GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite);
            verifier.Program.TopLevelDeclarations.Add(new VariableDualiser(1, null, null).VisitVariable(AccessOffsetX.Clone() as Variable));

        }
        

        private static AssignCmd MakeConditionalAssignment(Variable lhs, Expr condition, Expr rhs)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            lhss.Add(new SimpleAssignLhs(lhs.tok, new IdentifierExpr(lhs.tok, lhs)));
            rhss.Add(new NAryExpr(rhs.tok, new IfThenElse(rhs.tok), new ExprSeq(new Expr[] { condition, rhs, new IdentifierExpr(lhs.tok, lhs) })));
            return new AssignCmd(lhs.tok, lhss, rhss);
        }

        private Expr MakeAccessedIndex(Variable v, Expr offsetExpr, int Thread, string AccessType)
        {
            Expr result = new IdentifierExpr(v.tok, new VariableDualiser(Thread, null, null).VisitVariable(v.Clone() as Variable));
            Debug.Assert(v.TypedIdent.Type is MapType);
            MapType mt = v.TypedIdent.Type as MapType;
            Debug.Assert(mt.Arguments.Length == 1);

            result = Expr.Select(result,
                new Expr[] { offsetExpr });
            Debug.Assert(!(mt.Result is MapType));
            return result;
        }

        protected override void AddRequiresNoPendingAccess(Variable v)
        {
            IdentifierExpr ReadAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ")));
            IdentifierExpr WriteAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE")));

            verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.Not(WriteAccessOccurred1))));
        }

        protected override Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwo)
        {
            Variable ReadOrWriteHasOccurred = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite);
            ReadOrWriteHasOccurred.Name = ReadOrWriteHasOccurred.Name + "$" + OneOrTwo;
            ReadOrWriteHasOccurred.TypedIdent.Name = ReadOrWriteHasOccurred.TypedIdent.Name + "$" + OneOrTwo;
            Expr expr = Expr.Not(new IdentifierExpr(v.tok, ReadOrWriteHasOccurred));
            return expr;
        }


        protected override void AddAccessedOffsetsAreConstantCandidateInvariant(IRegion region, Variable v, IEnumerable<Expr> offsets, string ReadOrWrite)
        {
            Expr expr = AccessedOffsetsAreConstantExpr(v, offsets, ReadOrWrite, 1);
            verifier.AddCandidateInvariant(region, expr, "accessed offsets are constant");
        }

        private Expr AccessedOffsetsAreConstantExpr(Variable v, IEnumerable<Expr> offsets, string ReadOrWrite, int Thread) {
            return Expr.Imp(
                    new IdentifierExpr(Token.NoToken, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite))),
                    offsets.Select(ofs => (Expr)Expr.Eq(new IdentifierExpr(Token.NoToken, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, ReadOrWrite))), ofs)).Aggregate(Expr.Or));
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

        protected override void AddAccessedOffsetInRangeCTimesLocalIdToCTimesLocalIdPlusC(IRegion region, Variable v, Expr constant, string ReadOrWrite)
        {
            Expr expr = MakeCTimesLocalIdRangeExpression(v, constant, ReadOrWrite, 1);
            verifier.AddCandidateInvariant(region,
                expr, "accessed offset in range [ C*local_id, (C+1)*local_id )");
        }

        private Expr MakeCTimesLocalIdRangeExpression(Variable v, Expr constant, string ReadOrWrite, int Thread)
        {
            Expr CTimesLocalId = verifier.MakeBVMul(constant.Clone() as Expr, 
                new IdentifierExpr(Token.NoToken, verifier.MakeThreadId(Token.NoToken, "X", Thread)));

            Expr CTimesLocalIdPlusC = verifier.MakeBVAdd(verifier.MakeBVMul(constant.Clone() as Expr,
                new IdentifierExpr(Token.NoToken, verifier.MakeThreadId(Token.NoToken, "X", Thread))), constant.Clone() as Expr);

            Expr CTimesLocalIdLeqAccessedOffset = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LEQ", CTimesLocalId, OffsetXExpr(v, ReadOrWrite, Thread));

            Expr AccessedOffsetLtCTimesLocalIdPlusC = verifier.MakeBVSlt(OffsetXExpr(v, ReadOrWrite, Thread), CTimesLocalIdPlusC);

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

        protected override void AddAccessedOffsetInRangeCTimesGlobalIdToCTimesGlobalIdPlusC(IRegion region, Variable v, Expr constant, string ReadOrWrite)
        {
            Expr expr = MakeCTimesGloalIdRangeExpr(v, constant, ReadOrWrite, 1);
            verifier.AddCandidateInvariant(region,
                expr, "accessed offset in range [ C*global_id, (C+1)*global_id )");
        }

        private Expr MakeCTimesGloalIdRangeExpr(Variable v, Expr constant, string ReadOrWrite, int Thread)
        {
            Expr CTimesGlobalId = verifier.MakeBVMul(constant.Clone() as Expr,
                GlobalIdExpr("X", Thread));

            Expr CTimesGlobalIdPlusC = verifier.MakeBVAdd(verifier.MakeBVMul(constant.Clone() as Expr,
                GlobalIdExpr("X", Thread)), constant.Clone() as Expr);

            Expr CTimesGlobalIdLeqAccessedOffset = GPUVerifier.MakeBitVectorBinaryBoolean("BV32_LEQ", CTimesGlobalId, OffsetXExpr(v, ReadOrWrite, Thread));

            Expr AccessedOffsetLtCTimesGlobalIdPlusC = verifier.MakeBVSlt(OffsetXExpr(v, ReadOrWrite, Thread), CTimesGlobalIdPlusC);

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
