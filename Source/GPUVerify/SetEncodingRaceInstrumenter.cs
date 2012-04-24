using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify
{
    class SetEncodingRaceInstrumenter : RaceInstrumenterBase
    {

        protected override void AddLogRaceDeclarations(Variable v, string ReadOrWrite)
        {
            // TODO: requires revision due to major changes in this code.

            Variable AccessSet = MakeAccessSetVariable(v, ReadOrWrite);

            verifier.Program.TopLevelDeclarations.Add(AccessSet);

        }

        private static Variable MakeAccessSetVariable(Variable v, String ReadOrWrite)
        {
            Microsoft.Boogie.Type SetType = GetAccessSetType(v);

            Variable AccessSet = new GlobalVariable(v.tok, new TypedIdent(v.tok, MakeAccessSetName(v, ReadOrWrite), SetType));
            return AccessSet;
        }

        private static Microsoft.Boogie.Type GetAccessSetType(Variable v)
        {
            Microsoft.Boogie.Type SetType;

            if (v.TypedIdent.Type is MapType)
            {
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);
                Debug.Assert(GPUVerifier.IsIntOrBv32(mt.Arguments[0]));

                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(GPUVerifier.IsIntOrBv32(mt2.Arguments[0]));

                    if (mt2.Result is MapType)
                    {
                        MapType mt3 = mt2.Arguments[0] as MapType;
                        Debug.Assert(mt3.Arguments.Length == 1);
                        Debug.Assert(GPUVerifier.IsIntOrBv32(mt3.Arguments[0]));
                        Debug.Assert(!(mt3.Result is MapType));
                        SetType = new MapType(mt.tok, new TypeVariableSeq(), mt.Arguments,
                            new MapType(mt2.tok, new TypeVariableSeq(), mt2.Arguments,
                                new MapType(mt3.tok, new TypeVariableSeq(), mt3.Arguments,
                                    Microsoft.Boogie.Type.Bool
                                )
                            )
                        );

                    }
                    else
                    {
                        SetType = new MapType(mt.tok, new TypeVariableSeq(), mt.Arguments,
                            new MapType(mt2.tok, new TypeVariableSeq(), mt2.Arguments,
                                Microsoft.Boogie.Type.Bool
                            )
                        );
                    }
                }
                else
                {
                    SetType = new MapType(mt.tok, new TypeVariableSeq(), mt.Arguments,
                        Microsoft.Boogie.Type.Bool
                    );
                }
            }
            else
            {
                SetType = Microsoft.Boogie.Type.Bool;
            }
            return SetType;
        }

        private static string MakeAccessSetName(Variable v, String ReadOrWrite)
        {
            return "_" + ReadOrWrite + "_SET_" + v.Name;
        }

        protected override void AddLogAccessProcedure(Variable v, string ReadOrWrite)
        {
            // TODO: requires major revision due to significant changes in calling code
            throw new NotImplementedException();
        }
        

        protected override void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v, string AccessType)
        {
            IdentifierExpr AccessSet1 = new IdentifierExpr(tok, new VariableDualiser(1, null, null).VisitVariable(
                            MakeAccessSetVariable(v, AccessType)));
            IdentifierExprSeq VariablesToHavoc = new IdentifierExprSeq();
            VariablesToHavoc.Add(AccessSet1);
            bb.simpleCmds.Add(new HavocCmd(tok, VariablesToHavoc));

            AddAssumeNoAccess(bb, v, AccessType);

        }


        private static Microsoft.Boogie.Type GetIndexType(Variable v, int index)
        {
            Debug.Assert(index == 1 || index == 2 || index == 3);

            Debug.Assert(v.TypedIdent.Type is MapType);
            MapType mt = v.TypedIdent.Type as MapType;
            Debug.Assert(mt.Arguments.Length == 1);
            Debug.Assert(GPUVerifier.IsIntOrBv32(mt.Arguments[0]));

            if (index == 1)
            {
                return mt.Arguments[0];
            }

            Debug.Assert(mt.Result is MapType);
            MapType mt2 = mt.Result as MapType;
            Debug.Assert(mt2.Arguments.Length == 1);
            Debug.Assert(GPUVerifier.IsIntOrBv32(mt2.Arguments[0]));

            if (index == 2)
            {
                return mt2.Arguments[0];
            }

            Debug.Assert(mt2.Result is MapType);
            MapType mt3 = mt2.Arguments[0] as MapType;
            Debug.Assert(mt3.Arguments.Length == 1);
            Debug.Assert(GPUVerifier.IsIntOrBv32(mt3.Arguments[0]));
            Debug.Assert(!(mt3.Result is MapType));

            Debug.Assert(index == 3);
            return mt3.Arguments[0];
        }

        private static void SetNameDeep(IdentifierExpr e, string name)
        {
            e.Name = e.Decl.Name = e.Decl.TypedIdent.Name = name;
        }

        private static LocalVariable MakeDummy(Variable v, int index)
        {
            return new LocalVariable(v.tok, new TypedIdent(v.tok, "__dummy", GetIndexType(v, index)));
        }

        private static void AddAssumeNoAccess(BigBlock bb, Variable v, String AccessType)
        {
            bb.simpleCmds.Add(new AssumeCmd(v.tok, NoAccessExpr(v, AccessType, 1)));
        }

        private static Expr NoAccessExpr(Variable v, String AccessType, int Thread)
        {
            VariableSeq DummyVars;
            Expr result = AccessExpr(v, AccessType, Thread, out DummyVars);

            result = Expr.Not(result);

            if (DummyVars.Length > 0)
            {
                result = new ForallExpr(v.tok, DummyVars, result);
            }
            return result;

        }

        private static Expr AccessExpr(Variable v, String AccessType, int Thread, out VariableSeq DummyVars)
        {
            return QuantifiedIndexExpr(v, new VariableDualiser(Thread, null, null).VisitVariable(MakeAccessSetVariable(v, AccessType)), out DummyVars);
        }

        private static Expr QuantifiedIndexExpr(Variable v, Variable AccessSetVariable, out VariableSeq DummyVars)
        {
            DummyVars = new VariableSeq();
            Expr result = new IdentifierExpr(v.tok, AccessSetVariable);

            if (v.TypedIdent.Type is MapType)
            {
                IdentifierExprSeq DummyIdentifierExprs = new IdentifierExprSeq();
                MapType mt = v.TypedIdent.Type as MapType;
                Debug.Assert(mt.Arguments.Length == 1);
                Debug.Assert(GPUVerifier.IsIntOrBv32(mt.Arguments[0]));

                DummyVars.Add(MakeDummy(v, 1));
                DummyIdentifierExprs.Add(new IdentifierExpr(v.tok, DummyVars[0]));
                result = Expr.Select(result, new Expr[] { DummyIdentifierExprs[0] });

                if (mt.Result is MapType)
                {
                    MapType mt2 = mt.Result as MapType;
                    Debug.Assert(mt2.Arguments.Length == 1);
                    Debug.Assert(GPUVerifier.IsIntOrBv32(mt2.Arguments[0]));

                    DummyVars.Add(MakeDummy(v, 2));
                    DummyIdentifierExprs.Add(new IdentifierExpr(v.tok, DummyVars[1]));
                    result = Expr.Select(result, new Expr[] { DummyIdentifierExprs[1] });

                    if (mt2.Result is MapType)
                    {
                        MapType mt3 = mt2.Arguments[0] as MapType;
                        Debug.Assert(mt3.Arguments.Length == 1);
                        Debug.Assert(GPUVerifier.IsIntOrBv32(mt3.Arguments[0]));
                        Debug.Assert(!(mt3.Result is MapType));

                        DummyVars.Add(MakeDummy(v, 3));
                        DummyIdentifierExprs.Add(new IdentifierExpr(v.tok, DummyVars[2]));
                        result = Expr.Select(result, new Expr[] { DummyIdentifierExprs[2] });

                        SetNameDeep(DummyIdentifierExprs[0], "__z");
                        SetNameDeep(DummyIdentifierExprs[1], "__y");
                        SetNameDeep(DummyIdentifierExprs[2], "__x");
                    }
                    else
                    {
                        SetNameDeep(DummyIdentifierExprs[0], "__y");
                        SetNameDeep(DummyIdentifierExprs[1], "__x");
                    }
                }
                else
                {
                    SetNameDeep(DummyIdentifierExprs[0], "__x");
                }
            }
            return result;
        }

        private static Expr NoAccess0DExpr(IToken tok, Variable v, String AccessType, int Thread)
        {
            return Expr.Not(new IdentifierExpr(tok, new VariableDualiser(Thread, null, null).VisitVariable(MakeAccessSetVariable(v, AccessType))));
        }


        protected override void AddRequiresNoPendingAccess(Variable v)
        {
            verifier.KernelProcedure.Requires.Add(new Requires(false, NoAccessExpr(v, "WRITE", 1)));
            verifier.KernelProcedure.Requires.Add(new Requires(false, NoAccessExpr(v, "READ", 1)));
        }


        protected override Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwoString)
        {
            return NoAccessExpr(v, ReadOrWrite, Int32.Parse(OneOrTwoString));
        }



        protected override void AddAccessedOffsetIsThreadLocalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, 1);
            verifier.AddCandidateInvariant(wc, expr, "accessed offset is local id");

        }

        protected override void AddAccessedOffsetIsThreadGlobalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            throw new NotImplementedException();
        }

        private Expr AccessOnlyAtThreadId(Variable v, string ReadOrWrite, int Thread)
        {
            VariableSeq Dummies;
            Expr Access = AccessExpr(v, ReadOrWrite, Thread, out Dummies);

            if (Dummies.Length == 0)
            {
                return null;
            }

            Expr ImplicationLhs;

            if (Dummies.Length == 1)
            {
                ImplicationLhs = Expr.Neq(new IdentifierExpr(v.tok, Dummies[0]), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread)));
            }
            else if (Dummies.Length == 2)
            {
                if (!verifier.KernelHasIdY())
                {
                    return null;
                }
                ImplicationLhs = Expr.Or(
                        Expr.Neq(new IdentifierExpr(v.tok, Dummies[1]), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread))),
                        Expr.Neq(new IdentifierExpr(v.tok, Dummies[0]), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "Y", Thread)))
                    );
            }
            else
            {
                Debug.Assert(Dummies.Length == 3);
                if (!verifier.KernelHasIdZ())
                {
                    return null;
                }
                ImplicationLhs = Expr.Or(
                    Expr.Or(
                        Expr.Neq(new IdentifierExpr(v.tok, Dummies[2]), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread))),
                        Expr.Neq(new IdentifierExpr(v.tok, Dummies[1]), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "Y", Thread)))
                    ),
                    Expr.Neq(new IdentifierExpr(v.tok, Dummies[0]), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "Z", Thread)))
                );
            }

            return new ForallExpr(v.tok, Dummies, Expr.Imp(ImplicationLhs, Expr.Not(Access)));
        }

        protected override void AddAccessedOffsetIsThreadLocalIdCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, Thread);

            if (expr != null)
            {
                verifier.AddCandidateRequires(Proc, expr);
            }
        }

        protected override void AddAccessedOffsetIsThreadLocalIdCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, Thread);

            if (expr != null)
            {
                verifier.AddCandidateEnsures(Proc, expr);
            }
        }

        protected override void AddAccessedOffsetIsThreadFlattened2DLocalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            throw new NotImplementedException();
        }

        protected override void AddAccessedOffsetIsThreadFlattened2DGlobalIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite)
        {
            throw new NotImplementedException();
        }

        protected override void AddAccessedOffsetInRangeCTimesLocalIdToCTimesLocalIdPlusC(WhileCmd wc, Variable v, Expr constant, string ReadOrWrite)
        {
            throw new NotImplementedException();
        }

        protected override void AddAccessedOffsetInRangeCTimesGlobalIdToCTimesGlobalIdPlusC(WhileCmd wc, Variable v, Expr constant, string ReadOrWrite)
        {
            throw new NotImplementedException();
        }

    }
}
