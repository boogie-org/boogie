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
    class RaceInstrumenter : IRaceInstrumenter
    {
        protected GPUVerifier verifier;

        public INonLocalState NonLocalStateToCheck;

        public int onlyLog1;
        public int onlyLog2;
        public bool failedToFindSecondAccess;
        public bool addedLogWrite;
        private int logAddCount;

        private Dictionary<string, Procedure> logAccessProcedures = new Dictionary<string, Procedure>();

        public RaceInstrumenter()
        {
            onlyLog1 = -1;
            onlyLog2 = -1;
            failedToFindSecondAccess = false;
            addedLogWrite = false;
            logAddCount = 0;
        }

        public void setVerifier(GPUVerifier verifier)
        {
            this.verifier = verifier;
            NonLocalStateToCheck = new NonLocalStateLists();
            foreach(Variable v in verifier.NonLocalState.getGlobalVariables())
            {
                NonLocalStateToCheck.getGlobalVariables().Add(v);
            }
            foreach(Variable v in verifier.NonLocalState.getGroupSharedVariables())
            {
                NonLocalStateToCheck.getGroupSharedVariables().Add(v);
            }
        }

        private void AddNoReadOrWriteCandidateInvariants(IRegion region, Variable v)
        {
            // Reasoning: if READ_HAS_OCCURRED_v is not in the modifies set for the
            // loop then there is no point adding an invariant
            //
            // If READ_HAS_OCCURRED_v is in the modifies set, but the loop does not
            // contain a barrier, then it is almost certain that a read CAN be
            // pending at the loop head, so the invariant will not hold
            //
            // If there is a barrier in the loop body then READ_HAS_OCCURRED_v will
            // be in the modifies set, but there may not be a live read at the loop
            // head, so it is worth adding the loop invariant candidate.
            //
            // The same reasoning applies for WRITE

            if (verifier.ContainsBarrierCall(region))
            {
                if (verifier.ContainsNamedVariable(
                    LoopInvariantGenerator.GetModifiedVariables(region), GPUVerifier.MakeAccessHasOccurredVariableName(v.Name, "READ")))
                {
                    AddNoReadOrWriteCandidateInvariant(region, v, "READ");
                }

                if (verifier.ContainsNamedVariable(
                    LoopInvariantGenerator.GetModifiedVariables(region), GPUVerifier.MakeAccessHasOccurredVariableName(v.Name, "WRITE")))
                {
                    AddNoReadOrWriteCandidateInvariant(region, v, "WRITE");
                }
            }
        }

        private void AddNoReadOrWriteCandidateRequires(Procedure Proc, Variable v)
        {
            AddNoReadOrWriteCandidateRequires(Proc, v, "READ", "1");
            AddNoReadOrWriteCandidateRequires(Proc, v, "WRITE", "1");
        }

        private void AddNoReadOrWriteCandidateEnsures(Procedure Proc, Variable v)
        {
            AddNoReadOrWriteCandidateEnsures(Proc, v, "READ", "1");
            AddNoReadOrWriteCandidateEnsures(Proc, v, "WRITE", "1");
        }

        private void AddNoReadOrWriteCandidateInvariant(IRegion region, Variable v, string ReadOrWrite)
        {
            Expr candidate = NoReadOrWriteExpr(v, ReadOrWrite, "1");
            verifier.AddCandidateInvariant(region, candidate, "no " + ReadOrWrite.ToLower());
        }

        public void AddRaceCheckingCandidateInvariants(Implementation impl, IRegion region)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddNoReadOrWriteCandidateInvariants(region, v);
                AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(impl, region, v, "READ");
                AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(impl, region, v, "WRITE");
                AddGroupStrideAccessCandidateInvariants(impl, region, v, "READ");
                AddGroupStrideAccessCandidateInvariants(impl, region, v, "WRITE");
                AddOffsetsSatisfyPredicatesCandidateInvariant(region, v, "READ", CollectOffsetPredicates(impl, region, v, "READ"));
                AddOffsetsSatisfyPredicatesCandidateInvariant(region, v, "WRITE", CollectOffsetPredicates(impl, region, v, "WRITE"));
            }
        }

        private void AddGroupStrideAccessCandidateInvariants(Implementation impl, IRegion region, Variable v, string accessKind)
        {
            foreach (Expr e in GetOffsetsAccessed(region, v, accessKind))
            {
                if (!TryGenerateCandidateForReducedStrengthStrideVariable(impl, region, v, e, accessKind))
                {
                    if (e is IdentifierExpr)
                    {
                        foreach(Expr f in GetExpressionsFromWhichVariableIsAssignedInLoop(region, (e as IdentifierExpr).Decl))
                        {
                            TryGenerateCandidateForReducedStrengthStrideVariable(impl, region, v, f, accessKind);
                        }
                    }
                }
            }
        }

        private class StrideConstraint {}
        private class EqStrideConstraint : StrideConstraint {
            public EqStrideConstraint(Expr eq) { this.eq = eq; }
            public Expr eq;
        }
        private class ModStrideConstraint : StrideConstraint {
            public ModStrideConstraint(Expr mod, Expr modEq) { this.mod = mod; this.modEq = modEq; }
            public Expr mod, modEq;
        }

        private StrideConstraint BuildBottomStrideConstraint(Expr e)
        {
            int width = e.Type.BvBits;
            return new ModStrideConstraint(new LiteralExpr(Token.NoToken, BigNum.FromInt(1), width),
                                           new LiteralExpr(Token.NoToken, BigNum.FromInt(0), width));
        }

        private bool IsBottomStrideConstraint(StrideConstraint sc)
        {
            var msc = sc as ModStrideConstraint;
            if (msc == null)
                return false;

            var le = msc.mod as LiteralExpr;
            if (le == null)
                return false;

            var bvc = le.Val as BvConst;
            if (bvc == null)
                return false;

            return bvc.Value.InInt32 && bvc.Value.ToInt == 1;
        }

        private StrideConstraint BuildAddStrideConstraint(Expr e, StrideConstraint lhsc, StrideConstraint rhsc)
        {
            if (lhsc is EqStrideConstraint && rhsc is EqStrideConstraint)
            {
                return new EqStrideConstraint(e);
            }

            if (lhsc is EqStrideConstraint && rhsc is ModStrideConstraint)
                return BuildAddStrideConstraint(e, rhsc, lhsc);

            if (lhsc is ModStrideConstraint && rhsc is EqStrideConstraint)
            {
                var lhsmc = (ModStrideConstraint)lhsc;
                var rhsec = (EqStrideConstraint)rhsc;

                return new ModStrideConstraint(lhsmc.mod, verifier.MakeBVAdd(lhsmc.modEq, rhsec.eq));
            }

            if (lhsc is ModStrideConstraint && rhsc is ModStrideConstraint)
            {
                var lhsmc = (ModStrideConstraint)lhsc;
                var rhsmc = (ModStrideConstraint)rhsc;

                if (lhsmc.mod == rhsmc.mod)
                    return new ModStrideConstraint(lhsmc.mod, verifier.MakeBVAdd(lhsmc.modEq, rhsmc.modEq));
            }

            return BuildBottomStrideConstraint(e);
        }

        private StrideConstraint BuildMulStrideConstraint(Expr e, StrideConstraint lhsc, StrideConstraint rhsc)
        {
            if (lhsc is EqStrideConstraint && rhsc is EqStrideConstraint)
            {
                return new EqStrideConstraint(e);
            }

            if (lhsc is EqStrideConstraint && rhsc is ModStrideConstraint)
                return BuildMulStrideConstraint(e, rhsc, lhsc);

            if (lhsc is ModStrideConstraint && rhsc is EqStrideConstraint)
            {
                var lhsmc = (ModStrideConstraint)lhsc;
                var rhsec = (EqStrideConstraint)rhsc;

                return new ModStrideConstraint(verifier.MakeBVMul(lhsmc.mod, rhsec.eq),
                                               verifier.MakeBVMul(lhsmc.modEq, rhsec.eq));
            }

            return BuildBottomStrideConstraint(e);
        }

        private StrideConstraint BuildStrideConstraint(Implementation impl, Expr e)
        {
            if (e is LiteralExpr || (e is IdentifierExpr && ((IdentifierExpr)e).Decl is Constant))
                return new EqStrideConstraint(e);

            Expr lhs, rhs;

            if (GPUVerifier.IsBVAdd(e, out lhs, out rhs))
            {
                var lhsc = BuildStrideConstraint(impl, lhs);
                var rhsc = BuildStrideConstraint(impl, rhs);
                return BuildAddStrideConstraint(e, lhsc, rhsc);
            }

            if (GPUVerifier.IsBVMul(e, out lhs, out rhs))
            {
                var lhsc = BuildStrideConstraint(impl, lhs);
                var rhsc = BuildStrideConstraint(impl, rhs);
                return BuildMulStrideConstraint(e, lhsc, rhsc);
            }

            return BuildBottomStrideConstraint(e);
        }

        private Expr MaybeBuildOffsetStridePredicate(StrideConstraint sc, Expr offset)
        {
            var msc = sc as ModStrideConstraint;
            if (msc != null && !IsBottomStrideConstraint(msc))
            {
                Expr modEqExpr = Expr.Eq(verifier.MakeBVURem(offset, msc.mod), verifier.MakeBVURem(msc.modEq, msc.mod));
                return modEqExpr;
            }

            return null;
        }

        private void AddAccessRelatedCandidateInvariant(IRegion region, string accessKind, Expr candidateInvariantExpr, string procName, string tag)
        {
            Expr candidate = new VariableDualiser(1, verifier.uniformityAnalyser, procName).VisitExpr(candidateInvariantExpr.Clone() as Expr);
            verifier.AddCandidateInvariant(region, candidate, tag);
        }

        private bool TryGenerateCandidateForReducedStrengthStrideVariable(Implementation impl, IRegion region, Variable v, Expr e, string accessKind)
        {
            foreach (string w in
                verifier.mayBeTidPlusConstantAnalyser.GetMayBeIdPlusConstantVars(impl.Name))
            {
                if (!verifier.ContainsNamedVariable(
                    LoopInvariantGenerator.GetModifiedVariables(region), w))
                {
                    continue;
                }

                // Check also live

                if (GenerateModIdInvariants(impl, region, v, e, accessKind, w, verifier.mayBeTidPlusConstantAnalyser))
                {
                    return true;
                }

            }

            foreach (string w in
                verifier.mayBeGidPlusConstantAnalyser.GetMayBeIdPlusConstantVars(impl.Name))
            {
                if (!verifier.ContainsNamedVariable(
                    LoopInvariantGenerator.GetModifiedVariables(region), w))
                {
                    continue;
                }

                // Check also live

                if (GenerateModIdInvariants(impl, region, v, e, accessKind, w, verifier.mayBeGidPlusConstantAnalyser))
                {
                    return true;
                }

            }
            
            
            return false;
        }

        private bool GenerateModIdInvariants(Implementation impl, IRegion region, Variable v, Expr e, string accessKind, 
            string w, MayBeIdPlusConstantAnalyser mayBeIdPlusConstantAnalyser)
        {
            if (!IsLinearFunctionOfVariable(e, w))
            {
                return false;
            }

            Debug.Assert(!verifier.uniformityAnalyser.IsUniform(impl.Name, w));

            Variable wVariable = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, w,
                    Microsoft.Boogie.Type.GetBvType(32)));

            Expr indexModPow2EqualsId = ExprModPow2EqualsId(
                new IdentifierExpr(Token.NoToken, wVariable),
                mayBeIdPlusConstantAnalyser.GetIncrement(impl.Name, w), mayBeIdPlusConstantAnalyser.MakeIdExpr());

            verifier.AddCandidateInvariant(region, 
                new VariableDualiser(1, verifier.uniformityAnalyser, impl.Name).VisitExpr(indexModPow2EqualsId.Clone() as Expr),
                "is " + mayBeIdPlusConstantAnalyser.idKind() + " plus constant multiple");
            verifier.AddCandidateInvariant(region, 
                new VariableDualiser(2, verifier.uniformityAnalyser, impl.Name).VisitExpr(indexModPow2EqualsId.Clone() as Expr),
                "is " + mayBeIdPlusConstantAnalyser.idKind() + " plus constant multiple");

            Expr offsetExpr = new IdentifierExpr(Token.NoToken, GPUVerifier.MakeOffsetXVariable(v, accessKind));
            Expr invertedOffset = InverseOfLinearFunctionOfVariable(e, w, offsetExpr);

            Expr invertedOffsetModPow2EqualsId = ExprModPow2EqualsId(
                invertedOffset,
                mayBeIdPlusConstantAnalyser.GetIncrement(impl.Name, w), mayBeIdPlusConstantAnalyser.MakeIdExpr());

            Expr candidateInvariantExpr = Expr.Imp(
                    new IdentifierExpr(Token.NoToken, GPUVerifier.MakeAccessHasOccurredVariable(v.Name, accessKind)),
                    invertedOffsetModPow2EqualsId);

            AddAccessRelatedCandidateInvariant(region, accessKind, candidateInvariantExpr, impl.Name, "accessed offset is "
                + mayBeIdPlusConstantAnalyser.idKind() + " plus constant multiple");

            return true;
        }

        private HashSet<Expr> GetExpressionsFromWhichVariableIsAssignedInLoop(IRegion region, Variable variable)
        {
            HashSet<Expr> result = new HashSet<Expr>();
            foreach (Cmd c in region.Cmds())
            {
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;
                    if (assign.Lhss[0] is SimpleAssignLhs)
                    {
                        if (GPUVerifier.StripThreadIdentifier((assign.Lhss[0] as SimpleAssignLhs).AssignedVariable.Name).Equals(
                            GPUVerifier.StripThreadIdentifier(variable.Name)))
                        {
                            if (assign.Rhss[0] is NAryExpr && ((assign.Rhss[0] as NAryExpr).Fun is IfThenElse))
                            {
                                result.Add((assign.Rhss[0] as NAryExpr).Args[1]);
                            }
                            else
                            {
                                result.Add(assign.Rhss[0]);
                            }
                        }
                    }
                }
            }

            return result;
        }

        private Expr InverseOfLinearFunctionOfVariable(Expr e, string v, Expr offsetExpr)
        {
            if (e is IdentifierExpr)
            {
                if (GPUVerifier.StripThreadIdentifier((e as IdentifierExpr).Name).Equals(
                    v))
                {
                    return offsetExpr;
                }
                return e;
            }

            if (e is NAryExpr)
            {
                NAryExpr nary = e as NAryExpr;
                if (nary.Fun.FunctionName.Equals("BV32_ADD"))
                {
                    if (DoesNotReferTo(nary.Args[0], v))
                    {
                        return verifier.MakeBVSub(
                            InverseOfLinearFunctionOfVariable(nary.Args[1], v, offsetExpr),
                            nary.Args[0]);
                    }
                    else
                    {
                        Debug.Assert(DoesNotReferTo(nary.Args[1], v));
                        return verifier.MakeBVSub(
                            InverseOfLinearFunctionOfVariable(nary.Args[0], v, offsetExpr),
                            nary.Args[1]);
                    }
                }
            }

            Debug.Assert(false);

            return null;
        }

        private Expr ExprModPow2EqualsId(Expr expr, Expr powerOfTwoExpr, Expr threadIdExpr)
        {
            Expr Pow2Minus1 = verifier.MakeBVSub(powerOfTwoExpr, 
                            new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 32));

            Expr Pow2Minus1BitAndExpr = verifier.MakeBVAnd(Pow2Minus1, expr);

            return Expr.Eq(Pow2Minus1BitAndExpr, threadIdExpr);

        }

        private bool IsLinearFunctionOfVariable(Expr e, string v)
        {
            // e is v
            if (e is IdentifierExpr)
            {
                return GPUVerifier.StripThreadIdentifier((e as IdentifierExpr).Name).Equals(v);
            }

            // e is v + f /* f only contains constants or literals */
            if (e is NAryExpr)
            {
                NAryExpr nary = e as NAryExpr;
                if (nary.Fun.FunctionName.Equals("BV32_ADD"))
                {
                    if (IsLinearFunctionOfVariable(nary.Args[0], v)
                        && DoesNotReferTo(nary.Args[1], v))
                    {
                        return true;
                    }

                    if (IsLinearFunctionOfVariable(nary.Args[1], v)
                        && DoesNotReferTo(nary.Args[0], v))
                    {
                        return true;
                    }
                }
            }

            // We can handle further cases if they prove useful

            return false;
        }

        private bool DoesNotReferTo(Expr expr, string v)
        {
            FindReferencesToNamedVariableVisitor visitor = new FindReferencesToNamedVariableVisitor(v);
            visitor.VisitExpr(expr);
            return !visitor.found;
        }

        private List<Expr> CollectOffsetPredicates(Implementation impl, IRegion region, Variable v, string accessType)
        {
            var offsetVar = new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeOffsetXVariable(v, accessType));
            var offsetExpr = new IdentifierExpr(Token.NoToken, offsetVar);
            var offsetPreds = new List<Expr>();

            foreach (var offset in GetOffsetsAccessed(region, v, accessType))
            {
                bool isConstant;
                var def = verifier.varDefAnalyses[impl].SubstDefinitions(offset, impl.Name, out isConstant);
                if (isConstant)
                {
                    offsetPreds.Add(Expr.Eq(offsetExpr, def));
                }
                else
                {
                    var sc = BuildStrideConstraint(impl, def);
                    var pred = MaybeBuildOffsetStridePredicate(sc, offsetExpr);
                    if (pred != null)
                        offsetPreds.Add(pred);
                }
            }

            return offsetPreds;
        }

        private void AddReadOrWrittenOffsetIsThreadIdCandidateInvariants(Implementation impl, IRegion region, Variable v, string accessType)
        {
            KeyValuePair<IdentifierExpr, Expr> iLessThanC = GetILessThanC(region.Guard());
            if (iLessThanC.Key != null)
            {
                foreach (Expr e in GetOffsetsAccessed(region, v, accessType))
                {
                    if(HasFormIPlusLocalIdTimesC(e, iLessThanC, impl))
                    {
                        AddAccessedOffsetInRangeCTimesLocalIdToCTimesLocalIdPlusC(region, v, iLessThanC.Value, accessType);
                        break;
                    }
                }

                foreach (Expr e in GetOffsetsAccessed(region, v, accessType))
                {
                    if (HasFormIPlusGlobalIdTimesC(e, iLessThanC, impl))
                    {
                        AddAccessedOffsetInRangeCTimesGlobalIdToCTimesGlobalIdPlusC(region, v, iLessThanC.Value, accessType);
                        break;
                    }
                }
            
            }

        
        }

        private bool HasFormIPlusLocalIdTimesC(Expr e, KeyValuePair<IdentifierExpr, Expr> iLessThanC, Implementation impl)
        {
            if (!(e is NAryExpr))
            {
                return false;
            }

            NAryExpr nary = e as NAryExpr;

            if (!nary.Fun.FunctionName.Equals("BV32_ADD"))
            {
                return false;
            }

            return (SameIdentifierExpression(nary.Args[0], iLessThanC.Key) &&
                IsLocalIdTimesConstant(nary.Args[1], iLessThanC.Value, impl)) ||
                (SameIdentifierExpression(nary.Args[1], iLessThanC.Key) &&
                IsLocalIdTimesConstant(nary.Args[0], iLessThanC.Value, impl));
        }

        private bool IsLocalIdTimesConstant(Expr maybeLocalIdTimesConstant, Expr constant, Implementation impl)
        {
            if (!(maybeLocalIdTimesConstant is NAryExpr))
            {
                return false;
            }
            NAryExpr nary = maybeLocalIdTimesConstant as NAryExpr;
            if(!nary.Fun.FunctionName.Equals("BV32_MUL"))
            {
                return false;
            }

            return
                (SameConstant(nary.Args[0], constant) && verifier.IsLocalId(nary.Args[1], 0, impl)) ||
                (SameConstant(nary.Args[1], constant) && verifier.IsLocalId(nary.Args[0], 0, impl));
        }


        private bool HasFormIPlusGlobalIdTimesC(Expr e, KeyValuePair<IdentifierExpr, Expr> iLessThanC, Implementation impl)
        {
            if (!(e is NAryExpr))
            {
                return false;
            }

            NAryExpr nary = e as NAryExpr;

            if (!nary.Fun.FunctionName.Equals("BV32_ADD"))
            {
                return false;
            }

            return (SameIdentifierExpression(nary.Args[0], iLessThanC.Key) &&
                IsGlobalIdTimesConstant(nary.Args[1], iLessThanC.Value, impl)) ||
                (SameIdentifierExpression(nary.Args[1], iLessThanC.Key) &&
                IsGlobalIdTimesConstant(nary.Args[0], iLessThanC.Value, impl));
        }

        private bool IsGlobalIdTimesConstant(Expr maybeGlobalIdTimesConstant, Expr constant, Implementation impl)
        {
            if (!(maybeGlobalIdTimesConstant is NAryExpr))
            {
                return false;
            }
            NAryExpr nary = maybeGlobalIdTimesConstant as NAryExpr;
            if (!nary.Fun.FunctionName.Equals("BV32_MUL"))
            {
                return false;
            }

            return
                (SameConstant(nary.Args[0], constant) && verifier.IsGlobalId(nary.Args[1], 0, impl)) ||
                (SameConstant(nary.Args[1], constant) && verifier.IsGlobalId(nary.Args[0], 0, impl));
        }


        private bool SameConstant(Expr expr, Expr constant)
        {
            if (constant is IdentifierExpr)
            {
                IdentifierExpr identifierExpr = constant as IdentifierExpr;
                Debug.Assert(identifierExpr.Decl is Constant);
                return expr is IdentifierExpr && (expr as IdentifierExpr).Decl is Constant && (expr as IdentifierExpr).Decl.Name.Equals(identifierExpr.Decl.Name);
            }
            else
            {
                Debug.Assert(constant is LiteralExpr);
                LiteralExpr literalExpr = constant as LiteralExpr;
                if (!(expr is LiteralExpr))
                {
                    return false;
                }
                if (!(literalExpr.Val is BvConst) || !((expr as LiteralExpr).Val is BvConst))
                {
                    return false;
                }

                return (literalExpr.Val as BvConst).Value.ToInt == ((expr as LiteralExpr).Val as BvConst).Value.ToInt;
            }
        }

        private bool SameIdentifierExpression(Expr expr, IdentifierExpr identifierExpr)
        {
            if (!(expr is IdentifierExpr))
            {
                return false;
            }
            return (expr as IdentifierExpr).Decl.Name.Equals(identifierExpr.Name);
        }

        private KeyValuePair<IdentifierExpr, Expr> GetILessThanC(Expr expr)
        {

            if (expr is NAryExpr && (expr as NAryExpr).Fun.FunctionName.Equals("bv32_to_bool"))
            {
                expr = (expr as NAryExpr).Args[0];
            }

            if (!(expr is NAryExpr))
            {
                return new KeyValuePair<IdentifierExpr, Expr>(null, null);
            }

            NAryExpr nary = expr as NAryExpr;

            if (!(nary.Fun.FunctionName.Equals("BV32_C_LT") || nary.Fun.FunctionName.Equals("BV32_LT")))
            {
                return new KeyValuePair<IdentifierExpr, Expr>(null, null);
            }

            if (!(nary.Args[0] is IdentifierExpr))
            {
                return new KeyValuePair<IdentifierExpr, Expr>(null, null);
            }

            if (!IsConstant(nary.Args[1]))
            {
                return new KeyValuePair<IdentifierExpr, Expr>(null, null);
            }

            return new KeyValuePair<IdentifierExpr, Expr>(nary.Args[0] as IdentifierExpr, nary.Args[1]);

        }

        private static bool IsConstant(Expr e)
        {
            return ((e is IdentifierExpr && (e as IdentifierExpr).Decl is Constant) || e is LiteralExpr);
        }

        private void AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Procedure Proc, Variable v)
        {
            AddAccessedOffsetIsThreadLocalIdCandidateRequires(Proc, v, "WRITE", 1);
            AddAccessedOffsetIsThreadLocalIdCandidateRequires(Proc, v, "READ", 1);
        }

        private void AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Procedure Proc, Variable v)
        {
            AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Proc, v, "WRITE", 1);
            AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Proc, v, "READ", 1);
        }

        public void AddKernelPrecondition()
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddRequiresNoPendingAccess(v);
            }
        }

        public bool AddRaceCheckingInstrumentation()
        {

            if (onlyLog1 != -1)
            {
                addedLogWrite = false;
                failedToFindSecondAccess = true;
            }
            else
            {
                addedLogWrite = true;
                failedToFindSecondAccess = false;
            }

            foreach (Declaration d in verifier.Program.TopLevelDeclarations)
            {
                if (d is Implementation)
                {
                    AddRaceCheckCalls(d as Implementation);
                }
            }

            if (failedToFindSecondAccess || !addedLogWrite)
                return false;

            return true;

        }

        private void AddRaceCheckingDecsAndProcsForVar(Variable v)
        {
            AddLogRaceDeclarations(v, "READ");
            AddLogRaceDeclarations(v, "WRITE");
            AddLogAccessProcedure(v, "READ");
            AddLogAccessProcedure(v, "WRITE");

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

        private Block AddRaceCheckCalls(Block b)
        {
            b.Cmds = AddRaceCheckCalls(b.Cmds);
            return b;
        }

        private void AddRaceCheckCalls(Implementation impl)
        {
            if (CommandLineOptions.Unstructured)
                impl.Blocks = impl.Blocks.Select(AddRaceCheckCalls).ToList();
            else
                impl.StructuredStmts = AddRaceCheckCalls(impl.StructuredStmts);
        }

        private bool shouldAddLogCallAndIncr()
        {
            Contract.Assert(onlyLog1 >= -1);
            int oldLogAddCount = logAddCount;
            ++logAddCount;

            if (onlyLog1 == -1)
            {
                return true;
            }

            if(onlyLog1 + onlyLog2 == oldLogAddCount)
            {
                failedToFindSecondAccess = false;
                return true;
            }

            if (onlyLog1 == oldLogAddCount)
            {
                return true;
            }

            return false;
        }

        private CmdSeq AddRaceCheckCalls(CmdSeq cs)
        {
            var result = new CmdSeq();
            foreach (Cmd c in cs)
            {
                result.Add(c);
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;

                    ReadCollector rc = new ReadCollector(NonLocalStateToCheck);
                    foreach (var rhs in assign.Rhss)
                        rc.Visit(rhs);
                    if (rc.accesses.Count > 0)
                    {
                        foreach (AccessRecord ar in rc.accesses)
                        {
                            if (shouldAddLogCallAndIncr())
                            {

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

                                Procedure logProcedure = GetLogAccessProcedure(c.tok, "_LOG_READ_" + ar.v.Name);

                                CallCmd logAccessCallCmd = new CallCmd(c.tok, logProcedure.Name, inParams, new IdentifierExprSeq());

                                logAccessCallCmd.Proc = logProcedure;

                                result.Add(logAccessCallCmd);

                            }
                        }
                    }

                    foreach (var lhs in assign.Lhss)
                    {
                        WriteCollector wc = new WriteCollector(NonLocalStateToCheck);
                        wc.Visit(lhs);
                        if (wc.GetAccess() != null)
                        {
                            AccessRecord ar = wc.GetAccess();

                            if (shouldAddLogCallAndIncr())
                            {

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

                                Procedure logProcedure = GetLogAccessProcedure(c.tok, "_LOG_WRITE_" + ar.v.Name);

                                CallCmd logAccessCallCmd = new CallCmd(c.tok, logProcedure.Name, inParams, new IdentifierExprSeq());

                                logAccessCallCmd.Proc = logProcedure;

                                result.Add(logAccessCallCmd);

                                addedLogWrite = true;

                            }
                        }
                    }
                }
            }
            return result;
        }

        private BigBlock AddRaceCheckCalls(BigBlock bb)
        {
            BigBlock result = new BigBlock(bb.tok, bb.LabelName, AddRaceCheckCalls(bb.simpleCmds), null, bb.tc);

            if (bb.ec is WhileCmd)
            {
                WhileCmd WhileCommand = bb.ec as WhileCmd;
                result.ec = new WhileCmd(WhileCommand.tok, WhileCommand.Guard, 
                        WhileCommand.Invariants, AddRaceCheckCalls(WhileCommand.Body));
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd IfCommand = bb.ec as IfCmd;
                Debug.Assert(IfCommand.elseIf == null); // We don't handle else if yet
                result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, AddRaceCheckCalls(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? AddRaceCheckCalls(IfCommand.elseBlock) : null);
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

        private Procedure GetLogAccessProcedure(IToken tok, string name)
        {
            if (logAccessProcedures.ContainsKey(name))
            {
                return logAccessProcedures[name];
            }
            Procedure newProcedure = new Procedure(tok, name, new TypeVariableSeq(), new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());
            logAccessProcedures[name] = newProcedure;
            return newProcedure;
        }


        public BigBlock MakeResetReadWriteSetStatements(Variable v, int Thread)
        {
            BigBlock result = new BigBlock(Token.NoToken, null, new CmdSeq(), null, null);
            if (Thread == 2)
            {
                return result;
            }

            Expr ResetReadAssumeGuard = Expr.Not(new IdentifierExpr(Token.NoToken,
                new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ"))));
            Expr ResetWriteAssumeGuard = Expr.Not(new IdentifierExpr(Token.NoToken,
                new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE"))));

            if (CommandLineOptions.InterGroupRaceChecking && verifier.NonLocalState.getGlobalVariables().Contains(v))
            {
                ResetReadAssumeGuard = Expr.Imp(verifier.ThreadsInSameGroup(), ResetReadAssumeGuard);
                ResetWriteAssumeGuard = Expr.Imp(verifier.ThreadsInSameGroup(), ResetWriteAssumeGuard);
            }

            result.simpleCmds.Add(new AssumeCmd(Token.NoToken, ResetReadAssumeGuard));
            result.simpleCmds.Add(new AssumeCmd(Token.NoToken, ResetWriteAssumeGuard));
            return result;
        }

        protected Procedure MakeLogAccessProcedureHeader(Variable v, string ReadOrWrite)
        {
            VariableSeq inParams = new VariableSeq();

            Variable PredicateParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_P", Microsoft.Boogie.Type.Bool));

            Debug.Assert(v.TypedIdent.Type is MapType);
            MapType mt = v.TypedIdent.Type as MapType;
            Debug.Assert(mt.Arguments.Length == 1);
            Variable OffsetParameter = new LocalVariable(v.tok, new TypedIdent(v.tok, "_offset", mt.Arguments[0]));
            Debug.Assert(!(mt.Result is MapType));

            inParams.Add(new VariableDualiser(1, null, null).VisitVariable(PredicateParameter.Clone() as Variable));
            inParams.Add(new VariableDualiser(1, null, null).VisitVariable(OffsetParameter.Clone() as Variable));

            inParams.Add(new VariableDualiser(2, null, null).VisitVariable(PredicateParameter.Clone() as Variable));
            inParams.Add(new VariableDualiser(2, null, null).VisitVariable(OffsetParameter.Clone() as Variable));

            string LogProcedureName = "_LOG_" + ReadOrWrite + "_" + v.Name;

            Procedure result = GetLogAccessProcedure(v.tok, LogProcedureName);

            result.InParams = inParams;

            result.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

            return result;
        }

        public void AddRaceCheckingCandidateRequires(Procedure Proc)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddNoReadOrWriteCandidateRequires(Proc, v);
                AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Proc, v);
            }
        }

        public void AddRaceCheckingCandidateEnsures(Procedure Proc)
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddNoReadOrWriteCandidateEnsures(Proc, v);
                AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Proc, v);
            }
        }

        private void AddNoReadOrWriteCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            verifier.AddCandidateRequires(Proc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
        }

        private void AddNoReadOrWriteCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            verifier.AddCandidateEnsures(Proc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
        }

        private HashSet<Expr> GetOffsetsAccessed(IRegion region, Variable v, string AccessType)
        {
            HashSet<Expr> result = new HashSet<Expr>();

            foreach (Cmd c in region.Cmds())
            {
                if (c is CallCmd)
                {
                    CallCmd call = c as CallCmd;

                    if (call.callee == "_LOG_" + AccessType + "_" + v.Name)
                    {
                        // Ins[0] is thread 1's predicate,
                        // Ins[1] is the offset to be read
                        // If Ins[1] has the form BV32_ADD(offset#construct...(P), offset),
                        // we are looking for the second parameter to this BV32_ADD
                        Expr offset = call.Ins[1];
                        if (offset is NAryExpr)
                        {
                            var nExpr = (NAryExpr)offset;
                            if (nExpr.Fun.FunctionName == "BV32_ADD" &&
                                nExpr.Args[0] is NAryExpr)
                            {
                                var n0Expr = (NAryExpr)nExpr.Args[0];
                                if (n0Expr.Fun.FunctionName.StartsWith("offset#"))
                                    offset = nExpr.Args[1];
                            }
                        }
                        result.Add(offset);
                    }

                }

            }

            return result;
        }

        public void AddRaceCheckingDeclarations()
        {
            foreach (Variable v in NonLocalStateToCheck.getAllNonLocalVariables())
            {
                AddRaceCheckingDecsAndProcsForVar(v);
            }
        }

        protected void AddLogAccessProcedure(Variable v, string Access)
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

        protected void AddLogRaceDeclarations(Variable v, String ReadOrWrite)
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

        protected void AddRequiresNoPendingAccess(Variable v)
        {
            IdentifierExpr ReadAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "READ")));
            IdentifierExpr WriteAccessOccurred1 = new IdentifierExpr(v.tok, new VariableDualiser(1, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, "WRITE")));

            verifier.KernelProcedure.Requires.Add(new Requires(false, Expr.And(Expr.Not(ReadAccessOccurred1), Expr.Not(WriteAccessOccurred1))));
        }

        protected Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwo)
        {
            Variable ReadOrWriteHasOccurred = GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite);
            ReadOrWriteHasOccurred.Name = ReadOrWriteHasOccurred.Name + "$" + OneOrTwo;
            ReadOrWriteHasOccurred.TypedIdent.Name = ReadOrWriteHasOccurred.TypedIdent.Name + "$" + OneOrTwo;
            Expr expr = Expr.Not(new IdentifierExpr(v.tok, ReadOrWriteHasOccurred));
            return expr;
        }


        protected void AddOffsetsSatisfyPredicatesCandidateInvariant(IRegion region, Variable v, string ReadOrWrite, List<Expr> preds)
        {
            if (preds.Count != 0)
            {
                Expr expr = AccessedOffsetsSatisfyPredicatesExpr(v, preds, ReadOrWrite, 1);
                verifier.AddCandidateInvariant(region, expr, "accessed offsets satisfy predicates");
            }
        }

        private Expr AccessedOffsetsSatisfyPredicatesExpr(Variable v, IEnumerable<Expr> offsets, string ReadOrWrite, int Thread) {
            return Expr.Imp(
                    new IdentifierExpr(Token.NoToken, new VariableDualiser(Thread, null, null).VisitVariable(GPUVerifier.MakeAccessHasOccurredVariable(v.Name, ReadOrWrite))),
                    offsets.Aggregate(Expr.Or));
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

        protected void AddAccessedOffsetInRangeCTimesLocalIdToCTimesLocalIdPlusC(IRegion region, Variable v, Expr constant, string ReadOrWrite)
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

        protected void AddAccessedOffsetInRangeCTimesGlobalIdToCTimesGlobalIdPlusC(IRegion region, Variable v, Expr constant, string ReadOrWrite)
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

        protected void AddAccessedOffsetIsThreadLocalIdCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateRequires(Proc, expr);
            }
        }

        protected void AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessedOffsetIsThreadLocalIdExpr(v, ReadOrWrite, Thread);
            if (expr != null)
            {
                verifier.AddCandidateEnsures(Proc, expr);
            }
        }



    }



    class FindReferencesToNamedVariableVisitor : StandardVisitor
    {
        internal bool found = false;
        private string name;

        internal FindReferencesToNamedVariableVisitor(string name)
        {
            this.name = name;
        }

        public override Variable VisitVariable(Variable node)
        {
            if (GPUVerifier.StripThreadIdentifier(node.Name).Equals(name))
            {
                found = true;
            }
            return base.VisitVariable(node);
        }
    }



}
