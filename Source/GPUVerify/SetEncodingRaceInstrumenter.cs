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

        protected override void AddLogRaceDeclarations(Variable v, String ReadOrWrite, out IdentifierExprSeq ResetAtBarrier, out IdentifierExprSeq ModifiedAtLog)
        {
            Variable AccessSet = MakeAccessSetVariable(v, ReadOrWrite);

            if (CommandLineOptions.Symmetry && ReadOrWrite.Equals("READ"))
            {
                verifier.HalfDualisedVariableNames.Add(AccessSet.Name);
            }

            verifier.Program.TopLevelDeclarations.Add(AccessSet);

            ResetAtBarrier = new IdentifierExprSeq(new IdentifierExpr[] { new IdentifierExpr(v.tok, AccessSet) });
            ModifiedAtLog = ResetAtBarrier;

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
            Variable XParameterVariable;
            Variable YParameterVariable;
            Variable ZParameterVariable;
            Procedure LogReadOrWriteProcedure;

            MakeLogAccessProcedureHeader(v, ReadOrWrite, out XParameterVariable, out YParameterVariable, out ZParameterVariable, out LogReadOrWriteProcedure);

            LogReadOrWriteProcedure.Modifies.Add(new IdentifierExpr(v.tok, MakeAccessSetVariable(v, ReadOrWrite)));

            List<BigBlock> bigblocks = new List<BigBlock>();

            CmdSeq simpleCmds = new CmdSeq();

            List<Expr> trueExpr = new List<Expr>(new Expr[] { Expr.True });

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

                        simpleCmds.Add(
                            new AssignCmd(v.tok,
                                 new List<AssignLhs>(new AssignLhs[] {
                                new MapAssignLhs(v.tok, 
                                    new MapAssignLhs(v.tok, 
                                        new MapAssignLhs(v.tok, 
                                           new SimpleAssignLhs(v.tok, new IdentifierExpr(v.tok, MakeAccessSetVariable(v, ReadOrWrite)))
                                            , new List<Expr>(new Expr[] {  new IdentifierExpr(v.tok, ZParameterVariable) }))
                                            , new List<Expr>(new Expr[] {  new IdentifierExpr(v.tok, YParameterVariable) }))
                                            , new List<Expr>(new Expr[] {  new IdentifierExpr(v.tok, XParameterVariable) }))
                             }), trueExpr));

                    }
                    else
                    {
                        simpleCmds.Add(
                            new AssignCmd(v.tok,
                                 new List<AssignLhs>(new AssignLhs[] {
                                new MapAssignLhs(v.tok, 
                                    new MapAssignLhs(v.tok, 
                                       new SimpleAssignLhs(v.tok, new IdentifierExpr(v.tok, MakeAccessSetVariable(v, ReadOrWrite)))
                                        , new List<Expr>(new Expr[] {  new IdentifierExpr(v.tok, YParameterVariable) }))
                                        , new List<Expr>(new Expr[] {  new IdentifierExpr(v.tok, XParameterVariable) }))
                             }), trueExpr));
                    }
                }
                else
                {
                    simpleCmds.Add(
                        new AssignCmd(v.tok,
                             new List<AssignLhs>(new AssignLhs[] {
                                new MapAssignLhs(v.tok, 
                                    new SimpleAssignLhs(v.tok, new IdentifierExpr(v.tok, MakeAccessSetVariable(v, ReadOrWrite)))
                                    , new List<Expr>(new Expr[] {  new IdentifierExpr(v.tok, XParameterVariable) }))
                             }), trueExpr));
                }
            }
            else
            {
                simpleCmds.Add(new AssignCmd(v.tok, 
                    new List<AssignLhs>(new AssignLhs[] { new SimpleAssignLhs(v.tok, new IdentifierExpr(v.tok, MakeAccessSetVariable(v, ReadOrWrite))) }), 
                    trueExpr));
            }


            bigblocks.Add(new BigBlock(v.tok, "_LOG_" + ReadOrWrite + "", simpleCmds, null, null));

            StmtList statements = new StmtList(bigblocks, v.tok);

            Implementation LogReadOrWriteImplementation = new Implementation(v.tok, "_LOG_" + ReadOrWrite + "_" + v.Name, new TypeVariableSeq(), LogReadOrWriteProcedure.InParams, new VariableSeq(), new VariableSeq(), statements);
            LogReadOrWriteImplementation.AddAttribute("inline", new object[] { new LiteralExpr(v.tok, BigNum.FromInt(1)) });

            LogReadOrWriteImplementation.Proc = LogReadOrWriteProcedure;

            verifier.Program.TopLevelDeclarations.Add(LogReadOrWriteProcedure);
            verifier.Program.TopLevelDeclarations.Add(LogReadOrWriteImplementation);
        }

        protected override void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v, string AccessType)
        {
            IdentifierExpr AccessSet1 = new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(
                            MakeAccessSetVariable(v, AccessType)));
            IdentifierExprSeq VariablesToHavoc = new IdentifierExprSeq();
            VariablesToHavoc.Add(AccessSet1);
            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                IdentifierExpr AccessSet2 = new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(
                                MakeAccessSetVariable(v, AccessType)));
                VariablesToHavoc.Add(AccessSet2);
            }
            bb.simpleCmds.Add(new HavocCmd(tok, VariablesToHavoc));

            AddAssumeNoAccess(bb, v, AccessType);

        }

        public override void CheckForRaces(BigBlock bb, Variable v, bool ReadWriteOnly)
        {
            if (!ReadWriteOnly)
            {
                AddRaceCheck(bb, v, "WRITE", "WRITE");
            }
            AddRaceCheck(bb, v, "READ", "WRITE");
            if (!CommandLineOptions.Symmetry)
            {
                AddRaceCheck(bb, v, "WRITE", "READ");
            }


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

        private void AddRaceCheck(BigBlock bb, Variable v, String Access1, String Access2)
        {
            Expr AssertExpr = GenerateRaceCondition(v, Access1, Access2);

            bb.simpleCmds.Add(new AssertCmd(v.tok, AssertExpr));
        }

        protected override Expr GenerateRaceCondition(Variable v, String Access1, String Access2)
        {
            VariableSeq DummyVars1;
            Expr SetExpr1 = AccessExpr(v, Access1, 1, out DummyVars1);

            VariableSeq DummyVars2;
            Expr SetExpr2 = AccessExpr(v, Access2, 2, out DummyVars2);

            Debug.Assert(DummyVars1.Length == DummyVars2.Length);
            for (int i = 0; i < DummyVars1.Length; i++)
            {
                Debug.Assert(DummyVars1[i].Name.Equals(DummyVars2[i].Name));
            }

            Expr AssertExpr = Expr.And(SetExpr1, SetExpr2);

            if (Access1.Equals("WRITE") && Access2.Equals("WRITE") && !CommandLineOptions.FullAbstraction)
            {
                VariableSeq DummyVarsAccess1;
                VariableSeq DummyVarsAccess2;
                Expr IndexExpr1 = QuantifiedIndexExpr(v, new VariableDualiser(1).VisitVariable(v.Clone() as Variable), out DummyVarsAccess1);
                Expr IndexExpr2 = QuantifiedIndexExpr(v, new VariableDualiser(2).VisitVariable(v.Clone() as Variable), out DummyVarsAccess2);
                Debug.Assert(DummyVarsAccess1.Length == DummyVarsAccess2.Length);
                Debug.Assert(DummyVars1.Length == DummyVarsAccess1.Length);
                for (int i = 0; i < DummyVars1.Length; i++)
                {
                    Debug.Assert(DummyVarsAccess1[i].Name.Equals(DummyVarsAccess2[i].Name));
                    Debug.Assert(DummyVars1[i].Name.Equals(DummyVarsAccess1[i].Name));
                }
                AssertExpr = Expr.And(AssertExpr, Expr.Neq(IndexExpr1, IndexExpr2));
            }

            AssertExpr = Expr.Not(AssertExpr);
            if (DummyVars1.Length > 0)
            {
                AssertExpr = new ForallExpr(v.tok, DummyVars1, AssertExpr);
            }
            return AssertExpr;
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

            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                bb.simpleCmds.Add(new AssumeCmd(v.tok, NoAccessExpr(v, AccessType, 2)));
            }
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
            return QuantifiedIndexExpr(v, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, AccessType)), out DummyVars);
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
            return Expr.Not(new IdentifierExpr(tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, AccessType))));
        }


        protected override void AddRequiresNoPendingAccess(Variable v)
        {
            verifier.KernelProcedure.Requires.Add(new Requires(false, NoAccessExpr(v, "WRITE", 1)));
            verifier.KernelProcedure.Requires.Add(new Requires(false, NoAccessExpr(v, "WRITE", 2)));
            verifier.KernelProcedure.Requires.Add(new Requires(false, NoAccessExpr(v, "READ", 1)));
            if(!CommandLineOptions.Symmetry)
            {
                verifier.KernelProcedure.Requires.Add(new Requires(false, NoAccessExpr(v, "READ", 2)));
            }
        }

        protected override void AddNoReadOrWriteCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            verifier.AddCandidateInvariant(wc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
        }

        protected override Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwoString)
        {
            return NoAccessExpr(v, ReadOrWrite, Int32.Parse(OneOrTwoString));
        }



        protected override void AddReadOrWrittenOffsetIsThreadIdCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, Thread);

            if (expr != null)
            {
                verifier.AddCandidateInvariant(wc, expr);
            }
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

        protected override void AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, Thread);

            if (expr != null)
            {
                verifier.AddCandidateRequires(Proc, expr);
            }
        }

        protected override void AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, Thread);

            if (expr != null)
            {
                verifier.AddCandidateEnsures(Proc, expr);
            }
        }

    }
}
