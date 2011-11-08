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

        protected override void AddLogRaceDeclarations(Variable v, String ReadOrWrite)
        {
            Variable AccessSet = MakeAccessSetVariable(v, ReadOrWrite);

            if (CommandLineOptions.Symmetry && ReadOrWrite.Equals("READ"))
            {
                verifier.HalfDualisedVariableNames.Add(AccessSet.Name);
            }

            verifier.Program.TopLevelDeclarations.Add(AccessSet);

            // TODO: add modiies to every procedure that calls BARRIER

            verifier.KernelProcedure.Modifies.Add(new IdentifierExpr(v.tok, AccessSet));
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

            verifier.Program.TopLevelDeclarations.Add(LogReadOrWriteProcedure);
            verifier.Program.TopLevelDeclarations.Add(LogReadOrWriteImplementation);
        }

        protected override void SetNoAccessOccurred(IToken tok, BigBlock bb, Variable v, string AccessType)
        {
            IdentifierExpr AccessSet1 = new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(
                            MakeAccessSetVariable(v, AccessType)));
            IdentifierExprSeq VariablesToHavoc = new IdentifierExprSeq();
            VariablesToHavoc.Add(AccessSet1);
            verifier.BarrierProcedure.Modifies.Add(AccessSet1);
            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                IdentifierExpr AccessSet2 = new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(
                                MakeAccessSetVariable(v, AccessType)));
                VariablesToHavoc.Add(AccessSet2);
                verifier.BarrierProcedure.Modifies.Add(AccessSet2);
            }
            bb.simpleCmds.Add(new HavocCmd(tok, VariablesToHavoc));

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

                        Add3DAssumeNoAccess(tok, bb, v, AccessType, mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0]);

                    }
                    else
                    {
                        Add2DAssumeNoAccess(tok, bb, v, AccessType, mt.Arguments[0], mt2.Arguments[0]);
                    }
                }
                else
                {
                    Add1DAssumeNoAccess(tok, bb, v, AccessType, mt.Arguments[0]);
                }
            }
            else
            {
                Add0DAssumeNoAccess(tok, bb, v, AccessType);
            }
        }

        public override void CheckForRaces(IToken tok, BigBlock bb, Variable v)
        {
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

                        Add3DRaceCheck(tok, bb, v, "WRITE", "WRITE", mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0]);
                        Add3DRaceCheck(tok, bb, v, "READ", "WRITE", mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0]);
                        if (!CommandLineOptions.Symmetry)
                        {
                            Add3DRaceCheck(tok, bb, v, "WRITE", "READ", mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0]);
                        }


                    }
                    else
                    {
 
                        Add2DRaceCheck(tok, bb, v, "WRITE", "WRITE", mt.Arguments[0], mt2.Arguments[0]);
                        Add2DRaceCheck(tok, bb, v, "READ", "WRITE", mt.Arguments[0], mt2.Arguments[0]);
                        if (!CommandLineOptions.Symmetry)
                        {
                            Add2DRaceCheck(tok, bb, v, "WRITE", "READ", mt.Arguments[0], mt2.Arguments[0]);
                        }
                    }
                }
                else
                {
                    Add1DRaceCheck(tok, bb, v, "WRITE", "WRITE", mt.Arguments[0]);
                    Add1DRaceCheck(tok, bb, v, "READ", "WRITE", mt.Arguments[0]);
                    if (!CommandLineOptions.Symmetry)
                    {
                        Add1DRaceCheck(tok, bb, v, "WRITE", "READ", mt.Arguments[0]);
                    }
                }
            }
            else
            {
                Add0DRaceCheck(tok, bb, v, "WRITE", "WRITE");
                Add0DRaceCheck(tok, bb, v, "READ", "WRITE");
                if (!CommandLineOptions.Symmetry)
                {
                    Add0DRaceCheck(tok, bb, v, "WRITE", "READ");
                }
            }
        }

        private static void Add0DRaceCheck(IToken tok, BigBlock bb, Variable v, String Access1, String Access2)
        {
            bb.simpleCmds.Add(new AssertCmd(tok, Expr.Not(Expr.And(
                new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeAccessSetVariable(v, Access1))),
                new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeAccessSetVariable(v, Access2)))
                ))));
        }

        private static void Add1DRaceCheck(IToken tok, BigBlock bb, Variable v, String Access1, String Access2, Microsoft.Boogie.Type IndexType)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexType));
            bb.simpleCmds.Add(new AssertCmd(tok,
                new ForallExpr(tok, new VariableSeq(new Variable[] { DummyX }),
                    Expr.Not(Expr.And(
                        Expr.Select(new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeAccessSetVariable(v, Access1))), new Expr[] { new IdentifierExpr(tok, DummyX) }),
                        Expr.Select(new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeAccessSetVariable(v, Access2))), new Expr[] { new IdentifierExpr(tok, DummyX) })
                    ))
                )
            ));
        }

        private static void Add2DRaceCheck(IToken tok, BigBlock bb, Variable v, String Access1, String Access2, Microsoft.Boogie.Type IndexTypeY, Microsoft.Boogie.Type IndexTypeX)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexTypeX));
            Variable DummyY = new LocalVariable(tok, new TypedIdent(tok, "__y", IndexTypeX));
            bb.simpleCmds.Add(new AssertCmd(tok,
                new ForallExpr(tok, new VariableSeq(new Variable[] { DummyY, DummyX }),
                    Expr.Not(Expr.And(
                        Expr.Select(
                            Expr.Select(new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeAccessSetVariable(v, Access1))), new Expr[] { new IdentifierExpr(tok, DummyY) }),
                            new Expr[] { new IdentifierExpr(tok, DummyX) }
                        ),
                        Expr.Select(
                            Expr.Select(new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeAccessSetVariable(v, Access2))), new Expr[] { new IdentifierExpr(tok, DummyY) }),
                            new Expr[] { new IdentifierExpr(tok, DummyX) }
                        )
                    ))
                )
            ));
        }

        private static void Add3DRaceCheck(IToken tok, BigBlock bb, Variable v, String Access1, String Access2, Microsoft.Boogie.Type IndexTypeZ, Microsoft.Boogie.Type IndexTypeY, Microsoft.Boogie.Type IndexTypeX)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexTypeX));
            Variable DummyY = new LocalVariable(tok, new TypedIdent(tok, "__y", IndexTypeX));
            Variable DummyZ = new LocalVariable(tok, new TypedIdent(tok, "__z", IndexTypeX));
            bb.simpleCmds.Add(new AssertCmd(tok,
                new ForallExpr(tok, new VariableSeq(new Variable[] { DummyZ, DummyY, DummyX }),
                    Expr.Not(Expr.And(
                        Expr.Select(
                            Expr.Select(
                                Expr.Select(new IdentifierExpr(tok, new VariableDualiser(1).VisitVariable(MakeAccessSetVariable(v, Access1))), new Expr[] { new IdentifierExpr(tok, DummyZ) }),
                                new Expr[] { new IdentifierExpr(tok, DummyY) }
                            ),
                            new Expr[] { new IdentifierExpr(tok, DummyX) }
                        ),
                        Expr.Select(
                            Expr.Select(
                                Expr.Select(new IdentifierExpr(tok, new VariableDualiser(2).VisitVariable(MakeAccessSetVariable(v, Access2))), new Expr[] { new IdentifierExpr(tok, DummyZ) }),
                                new Expr[] { new IdentifierExpr(tok, DummyY) }
                            ),
                            new Expr[] { new IdentifierExpr(tok, DummyX) }
                        )
                    ))
                )
            ));
        }


        private static void Add0DAssumeNoAccess(IToken tok, BigBlock bb, Variable v, String AccessType)
        {
            bb.simpleCmds.Add(new AssumeCmd(tok,
                NoAccess0DExpr(tok, v, AccessType, 1)
            ));

            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                bb.simpleCmds.Add(new AssumeCmd(tok,
                    NoAccess0DExpr(tok, v, AccessType, 2)
                ));
            }
        }


        private static void Add1DAssumeNoAccess(IToken tok, BigBlock bb, Variable v, String AccessType, Microsoft.Boogie.Type IndexTypeX)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexTypeX));
            bb.simpleCmds.Add(new AssumeCmd(tok,
                NoAccess1DExpr(tok, v, AccessType, IndexTypeX, 1)
            ));

            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                bb.simpleCmds.Add(new AssumeCmd(tok,
                    NoAccess1DExpr(tok, v, AccessType, IndexTypeX, 2)
                ));
            }
        }


        private static void Add2DAssumeNoAccess(IToken tok, BigBlock bb, Variable v, String AccessType, Microsoft.Boogie.Type IndexTypeY, Microsoft.Boogie.Type IndexTypeX)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexTypeX));
            Variable DummyY = new LocalVariable(tok, new TypedIdent(tok, "__y", IndexTypeX));
            bb.simpleCmds.Add(new AssumeCmd(tok,
                NoAccess2DExpr(tok, v, AccessType, IndexTypeY, IndexTypeX, 1)
            ));

            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                bb.simpleCmds.Add(new AssumeCmd(tok,
                    NoAccess2DExpr(tok, v, AccessType, IndexTypeY, IndexTypeX, 2)
                ));
            }
        }


        private static void Add3DAssumeNoAccess(IToken tok, BigBlock bb, Variable v, String AccessType, Microsoft.Boogie.Type IndexTypeZ, Microsoft.Boogie.Type IndexTypeY, Microsoft.Boogie.Type IndexTypeX)
        {
            bb.simpleCmds.Add(new AssumeCmd(tok,
                NoAccess3DExpr(tok, v, AccessType, IndexTypeZ, IndexTypeY, IndexTypeX, 1)
            ));

            if (!CommandLineOptions.Symmetry || !AccessType.Equals("READ"))
            {
                bb.simpleCmds.Add(new AssumeCmd(tok,
                    NoAccess3DExpr(tok, v, AccessType, IndexTypeZ, IndexTypeY, IndexTypeX, 2)
                ));
            }
        }

        private static Expr NoAccess3DExpr(IToken tok, Variable v, String AccessType, Microsoft.Boogie.Type IndexTypeZ, Microsoft.Boogie.Type IndexTypeY, Microsoft.Boogie.Type IndexTypeX, int Thread)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexTypeX));
            Variable DummyY = new LocalVariable(tok, new TypedIdent(tok, "__y", IndexTypeY));
            Variable DummyZ = new LocalVariable(tok, new TypedIdent(tok, "__z", IndexTypeZ));
            return new ForallExpr(tok, new VariableSeq(new Variable[] { DummyZ, DummyY, DummyX }),
                                Expr.Not(
                                    Expr.Select(
                                        Expr.Select(
                                            Expr.Select(new IdentifierExpr(tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, AccessType))), new Expr[] { new IdentifierExpr(tok, DummyZ) }),
                                            new Expr[] { new IdentifierExpr(tok, DummyY) }
                                        ),
                                        new Expr[] { new IdentifierExpr(tok, DummyX) }
                                    )
                                )
                            )
            ;
        }

        private static Expr NoAccess2DExpr(IToken tok, Variable v, String AccessType, Microsoft.Boogie.Type IndexTypeY, Microsoft.Boogie.Type IndexTypeX, int Thread)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexTypeX));
            Variable DummyY = new LocalVariable(tok, new TypedIdent(tok, "__y", IndexTypeY));
            return new ForallExpr(tok, new VariableSeq(new Variable[] { DummyY, DummyX }),
                                Expr.Not(
                                    Expr.Select(
                                        Expr.Select(new IdentifierExpr(tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, AccessType))), new Expr[] { new IdentifierExpr(tok, DummyY) }),
                                        new Expr[] { new IdentifierExpr(tok, DummyX) }
                                    )
                                )
                            )
            ;
        }

        private static Expr NoAccess1DExpr(IToken tok, Variable v, String AccessType, Microsoft.Boogie.Type IndexTypeX, int Thread)
        {
            Variable DummyX = new LocalVariable(tok, new TypedIdent(tok, "__x", IndexTypeX));
            return new ForallExpr(tok, new VariableSeq(new Variable[] { DummyX }),
                                Expr.Not(
                                    Expr.Select(new IdentifierExpr(tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, AccessType))), new Expr[] { new IdentifierExpr(tok, DummyX) })
                                )
                            );
        }

        private static Expr NoAccess0DExpr(IToken tok, Variable v, String AccessType, int Thread)
        {
            return Expr.Not(new IdentifierExpr(tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, AccessType))));
        }


        protected override void AddRequiresNoPendingAccess(Variable v)
        {
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

                        verifier.KernelProcedure.Requires.Add(new Requires(false,
                            NoAccess3DExpr(v.tok, v, "WRITE", mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0], 1)));
                        verifier.KernelProcedure.Requires.Add(new Requires(false,
                            NoAccess3DExpr(v.tok, v, "WRITE", mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0], 2)));
                        verifier.KernelProcedure.Requires.Add(new Requires(false,
                            NoAccess3DExpr(v.tok, v, "READ", mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0], 1)));
                        if (!CommandLineOptions.Symmetry)
                        {
                            verifier.KernelProcedure.Requires.Add(new Requires(false,
                                NoAccess3DExpr(v.tok, v, "READ", mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0], 2)));
                        }


                    }
                    else
                    {
                        verifier.KernelProcedure.Requires.Add(new Requires(false, 
                            NoAccess2DExpr(v.tok, v, "WRITE", mt.Arguments[0], mt2.Arguments[0], 1)));
                        verifier.KernelProcedure.Requires.Add(new Requires(false, 
                            NoAccess2DExpr(v.tok, v, "WRITE", mt.Arguments[0], mt2.Arguments[0], 2)));
                        verifier.KernelProcedure.Requires.Add(new Requires(false, 
                            NoAccess2DExpr(v.tok, v, "READ", mt.Arguments[0], mt2.Arguments[0], 1)));
                        if(!CommandLineOptions.Symmetry)
                        {
                            verifier.KernelProcedure.Requires.Add(new Requires(false, 
                                NoAccess2DExpr(v.tok, v, "READ", mt.Arguments[0], mt2.Arguments[0], 2)));
                        }
                    }
                }
                else
                {
                    verifier.KernelProcedure.Requires.Add(new Requires(false, 
                        NoAccess1DExpr(v.tok, v, "WRITE", mt.Arguments[0], 1)));
                    verifier.KernelProcedure.Requires.Add(new Requires(false, 
                        NoAccess1DExpr(v.tok, v, "WRITE", mt.Arguments[0], 2)));
                    verifier.KernelProcedure.Requires.Add(new Requires(false, 
                        NoAccess1DExpr(v.tok, v, "READ", mt.Arguments[0], 1)));
                    if(!CommandLineOptions.Symmetry)
                    {
                        verifier.KernelProcedure.Requires.Add(new Requires(false, 
                            NoAccess1DExpr(v.tok, v, "READ", mt.Arguments[0], 2)));
                    }
                }
            }
            else
            {
                verifier.KernelProcedure.Requires.Add(new Requires(false, 
                    NoAccess0DExpr(v.tok, v, "WRITE", 1)));
                verifier.KernelProcedure.Requires.Add(new Requires(false, 
                    NoAccess0DExpr(v.tok, v, "WRITE", 2)));
                verifier.KernelProcedure.Requires.Add(new Requires(false, 
                    NoAccess0DExpr(v.tok, v, "READ", 1)));
                if(!CommandLineOptions.Symmetry)
                {
                    verifier.KernelProcedure.Requires.Add(new Requires(false, 
                        NoAccess0DExpr(v.tok, v, "READ", 2)));
                }
            }
        }

        protected override void AddNoReadOrWriteCandidateInvariant(WhileCmd wc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            verifier.AddCandidateInvariant(wc, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo));
        }

        private static Expr NoReadOrWriteExpr(Variable v, string ReadOrWrite, string OneOrTwoString)
        {
            int OneOrTwo = Int32.Parse(OneOrTwoString);
            Expr expr = null;

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
                        expr = NoAccess3DExpr(v.tok, v, ReadOrWrite, mt.Arguments[0], mt2.Arguments[0], mt3.Arguments[0], OneOrTwo);
                    }
                    else
                    {
                        expr = NoAccess2DExpr(v.tok, v, ReadOrWrite, mt.Arguments[0], mt2.Arguments[0], OneOrTwo);
                    }
                }
                else
                {
                    expr = NoAccess1DExpr(v.tok, v, ReadOrWrite, mt.Arguments[0], OneOrTwo);
                }
            }
            else
            {
                expr = NoAccess0DExpr(v.tok, v, ReadOrWrite, OneOrTwo);
            }
            return expr;
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
            Expr expr = null;

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

                        if (verifier.KernelHasIdZ() && mt.Arguments[0].Equals(verifier.GetTypeOfIdZ()) &&
                            mt2.Arguments[0].Equals(verifier.GetTypeOfIdY()) &&
                            mt3.Arguments[0].Equals(verifier.GetTypeOfIdX()))
                        {
                            expr = No3DAccessExceptAtThreadId(v, ReadOrWrite, Thread);
                        }

                    }
                    else
                    {
                        if (verifier.KernelHasIdY() && mt.Arguments[0].Equals(verifier.GetTypeOfIdY()) &&
                            mt2.Arguments[0].Equals(verifier.GetTypeOfIdX()))
                        {
                            expr = No2DAccessExceptAtThreadId(v, ReadOrWrite, Thread);
                        }
                    }
                }
                else
                {
                    if (mt.Arguments[0].Equals(verifier.GetTypeOfIdX()))
                    {
                        expr = No1DAccessExceptAtThreadId(v, ReadOrWrite, Thread);
                    }
                }
            }
            return expr;
        }

        private Expr No1DAccessExceptAtThreadId(Variable v, string ReadOrWrite, int Thread)
        {
            Variable DummyX = new LocalVariable(v.tok, new TypedIdent(v.tok, "__x", verifier.GetTypeOfIdX()));

            return new ForallExpr(v.tok,
                new VariableSeq(new Variable[] { DummyX }),
                Expr.Imp(
                    Expr.Neq(new IdentifierExpr(v.tok, DummyX), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread))),
                    Expr.Not(
                        Expr.Select(
                            new IdentifierExpr(v.tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, ReadOrWrite))),
                            new IdentifierExpr(v.tok, DummyX)
                        )
                    )
                )
            );
        }


        private Expr No2DAccessExceptAtThreadId(Variable v, string ReadOrWrite, int Thread)
        {
            Variable DummyX = new LocalVariable(v.tok, new TypedIdent(v.tok, "__x", verifier.GetTypeOfIdX()));
            Variable DummyY = new LocalVariable(v.tok, new TypedIdent(v.tok, "__y", verifier.GetTypeOfIdY()));

            return new ForallExpr(v.tok,
                new VariableSeq(new Variable[] { DummyY, DummyX }),
                Expr.Imp(
                    Expr.Or(
                        Expr.Neq(new IdentifierExpr(v.tok, DummyX), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread))),
                        Expr.Neq(new IdentifierExpr(v.tok, DummyY), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "Y", Thread)))
                    ),

                    Expr.Not(
                        Expr.Select(
                            Expr.Select(
                                new IdentifierExpr(v.tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, ReadOrWrite))),
                                new IdentifierExpr(v.tok, DummyY)
                            ),
                            new IdentifierExpr(v.tok, DummyX)
                        )
                    )
                )
            );
        }

        private Expr No3DAccessExceptAtThreadId(Variable v, string ReadOrWrite, int Thread)
        {
            Variable DummyX = new LocalVariable(v.tok, new TypedIdent(v.tok, "__x", verifier.GetTypeOfIdX()));
            Variable DummyY = new LocalVariable(v.tok, new TypedIdent(v.tok, "__y", verifier.GetTypeOfIdY()));
            Variable DummyZ = new LocalVariable(v.tok, new TypedIdent(v.tok, "__z", verifier.GetTypeOfIdY()));

            return new ForallExpr(v.tok,
                new VariableSeq(new Variable[] { DummyY, DummyX }),
                Expr.Imp(
                    Expr.Or(
                        Expr.Or(
                            Expr.Neq(new IdentifierExpr(v.tok, DummyX), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "X", Thread))),
                            Expr.Neq(new IdentifierExpr(v.tok, DummyY), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "Y", Thread)))
                        ),
                        Expr.Neq(new IdentifierExpr(v.tok, DummyZ), new IdentifierExpr(v.tok, verifier.MakeThreadId(v.tok, "Z", Thread)))
                    ),

                    Expr.Not(
                        Expr.Select(
                            Expr.Select(
                                Expr.Select(
                                    new IdentifierExpr(v.tok, new VariableDualiser(Thread).VisitVariable(MakeAccessSetVariable(v, ReadOrWrite))),
                                    new IdentifierExpr(v.tok, DummyZ)
                                ),
                                new IdentifierExpr(v.tok, DummyY)
                            ),
                            new IdentifierExpr(v.tok, DummyX)
                        )
                    )
                )
            );
        }

        protected override void AddReadOrWrittenOffsetIsThreadIdCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, Thread);

            if (expr != null)
            {
                Proc.Requires.Add(new Requires(false, expr));
            }
        }

        protected override void AddReadOrWrittenOffsetIsThreadIdCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, int Thread)
        {
            Expr expr = AccessOnlyAtThreadId(v, ReadOrWrite, Thread);

            if (expr != null)
            {
                Proc.Ensures.Add(new Ensures(false, expr));
            }
        }

        protected override void AddNoReadOrWriteCandidateRequires(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            Proc.Requires.Add(new Requires(false, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo)));
        }

        protected override void AddNoReadOrWriteCandidateEnsures(Procedure Proc, Variable v, string ReadOrWrite, string OneOrTwo)
        {
            Proc.Ensures.Add(new Ensures(false, NoReadOrWriteExpr(v, ReadOrWrite, OneOrTwo)));
        }

    }
}
