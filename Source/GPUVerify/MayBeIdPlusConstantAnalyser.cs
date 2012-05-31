using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    abstract class MayBeIdPlusConstantAnalyser
    {
        protected GPUVerifier verifier;

        protected MayBeAnalyser mayBeAnalyser;

        // Given a p.v, says whether p.v may be assigned to a tid variable at some point
        protected Dictionary<string, Dictionary<string, bool>> mayBeAssignedId;

        // Records the constants that p.v may be incremented by
        protected Dictionary<string, Dictionary<string, HashSet<Expr>>> incrementedBy;

        // The final result
        protected Dictionary<string, Dictionary<string, bool>> mayBeIdPlusConstantInfo;

        public MayBeIdPlusConstantAnalyser(GPUVerifier verifier)
        {
            this.verifier = verifier;
            mayBeAssignedId = new Dictionary<string, Dictionary<string, bool>>();
            incrementedBy = new Dictionary<string, Dictionary<string, HashSet<Expr>>>();
            mayBeIdPlusConstantInfo = new Dictionary<string, Dictionary<string, bool>>();
        }

        internal void Analyse()
        {
            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if (D is Implementation)
                {
                    Implementation Impl = D as Implementation;
                    mayBeAssignedId[Impl.Name] = new Dictionary<string, bool>();
                    incrementedBy[Impl.Name] = new Dictionary<string, HashSet<Expr>>();
                    mayBeIdPlusConstantInfo[Impl.Name] = new Dictionary<string, bool>();

                    foreach (Variable v in Impl.LocVars)
                    {
                        mayBeAssignedId[Impl.Name][v.Name] = false;
                        incrementedBy[Impl.Name][v.Name] = new HashSet<Expr>();
                    }

                    foreach (Variable v in Impl.InParams)
                    {
                        mayBeAssignedId[Impl.Name][v.Name] = false;
                        incrementedBy[Impl.Name][v.Name] = new HashSet<Expr>();
                    }

                    foreach (Variable v in Impl.OutParams)
                    {
                        mayBeAssignedId[Impl.Name][v.Name] = false;
                        incrementedBy[Impl.Name][v.Name] = new HashSet<Expr>();
                    }

                    // Fixpoint not required - this is just syntactic
                    Analyse(Impl);

                    foreach (string v in mayBeAssignedId[Impl.Name].Keys)
                    {
                        mayBeIdPlusConstantInfo[Impl.Name][v] =
                            mayBeAssignedId[Impl.Name][v] && incrementedBy[Impl.Name][v].Count == 1;
                    }

                }
            }

            if (CommandLineOptions.ShowMayBeTidPlusConstantAnalysis)
            {
                dump();
            }
        }

        private void Analyse(Implementation Impl)
        {
            Analyse(Impl, Impl.StructuredStmts);
        }

        private void Analyse(Implementation impl, StmtList stmtList)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                Analyse(impl, bb);
            }
        }


        private void Analyse(Implementation impl, BigBlock bb)
        {
            foreach (Cmd c in bb.simpleCmds)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assign = c as AssignCmd;

                    for (int i = 0; i != assign.Lhss.Count; i++)
                    {
                        if (assign.Lhss[i] is SimpleAssignLhs)
                        {
                            Variable lhsV = (assign.Lhss[i] as SimpleAssignLhs).AssignedVariable.Decl;

                            if (mayBeAssignedId[impl.Name].ContainsKey(lhsV.Name))
                            {

                                if (assign.Rhss[i] is IdentifierExpr)
                                {

                                    Variable rhsV = (assign.Rhss[i] as IdentifierExpr).Decl;

                                    if (mayBeAnalyser.MayBe(ComponentString(), impl.Name, rhsV.Name))
                                    {
                                        mayBeAssignedId[impl.Name][lhsV.Name] = true;
                                    }

                                }
                                else
                                {

                                    Expr constantIncrement = GetConstantIncrement(lhsV, assign.Rhss[i]);

                                    if (constantIncrement != null)
                                    {
                                        incrementedBy[impl.Name][lhsV.Name].Add(constantIncrement);
                                    }

                                }
                            }
                        }
                    }
                }
            }

            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;
                Analyse(impl, wc.Body);
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd ifCmd = bb.ec as IfCmd;
                Analyse(impl, ifCmd.thn);
                if (ifCmd.elseBlock != null)
                {
                    Analyse(impl, ifCmd.elseBlock);
                }
                Debug.Assert(ifCmd.elseIf == null);
            }

        }

        private string ConvertToString(Expr constantIncrement)
        {
            if (constantIncrement is IdentifierExpr)
            {
                return (constantIncrement as IdentifierExpr).Decl.Name;
            }

            LiteralExpr lit = constantIncrement as LiteralExpr;

            return (lit.Val as BvConst).Value.ToString() + "bv32";

        }

        private Expr GetConstantIncrement(Variable v, Expr expr)
        {

            if (!(expr is NAryExpr))
            {
                return null;
            }

            NAryExpr nary = expr as NAryExpr;

            if (!nary.Fun.FunctionName.Equals("BV32_ADD"))
            {
                return null;
            }

            if (!(nary.Args[0] is IdentifierExpr &&
                ((nary.Args[0] as IdentifierExpr).Decl.Name.Equals(v.Name))))
            {
                return null;
            }

            if (!IsConstant(nary.Args[1]))
            {
                return null;
            }

            return nary.Args[1];
        }

        private bool IsConstant(Expr expr)
        {
            return expr is LiteralExpr
                || (expr is IdentifierExpr && (expr as IdentifierExpr).Decl is Constant);
        }

        private bool IsVariable(Expr expr, Variable v)
        {
            return expr is IdentifierExpr && ((expr as IdentifierExpr).Decl.Name.Equals(v.Name));
        }

        private void dump()
        {
            foreach (string p in mayBeIdPlusConstantInfo.Keys)
            {
                Console.WriteLine("Procedure " + p);
                foreach (string v in mayBeIdPlusConstantInfo[p].Keys)
                {
                    Console.WriteLine("  " + v + ": gets assigned " + idKind() + " - " + mayBeAssignedId[p][v]);
                    Console.Write("  " + v + ": incremented by -");
                    foreach(Expr e in incrementedBy[p][v])
                    {
                        Console.Write(" " + ConvertToString(e));
                    }
                    Console.WriteLine("");

                    Console.Write("  " + v + ": ");
                    
                    if(mayBeIdPlusConstantInfo[p][v])
                    {
                        Console.Write("may be " + idKind() + " + ");
                        foreach(Expr e in incrementedBy[p][v])
                        {
                            Console.WriteLine(ConvertToString(e));
                        }
                    }
                    else
                    {
                        Console.WriteLine("likely not " + idKind() + " + const");
                    }
                }
            }

        }

        internal abstract string idKind();

        protected abstract string ComponentString();

        internal Expr GetIncrement(string p, string v)
        {
            Debug.Assert(mayBeIdPlusConstantInfo[p][v]);
            Debug.Assert(incrementedBy[p][v].Count == 1);
            foreach (Expr e in incrementedBy[p][v])
            {
                return e;
            }
            Debug.Assert(false);
            return null;
        }

        internal HashSet<string> GetMayBeIdPlusConstantVars(string p)
        {
            HashSet<string> result = new HashSet<string>();

            if (!mayBeIdPlusConstantInfo.ContainsKey(p))
            {
                return result;
            }

            foreach (string v in mayBeIdPlusConstantInfo[p].Keys)
            {
                if (mayBeIdPlusConstantInfo[p][v])
                {
                    result.Add(v);
                }
            }

            return result;
        }


        internal abstract Expr MakeIdExpr();
    }

    class MayBeLocalIdPlusConstantAnalyser : MayBeIdPlusConstantAnalyser
    {

        internal MayBeLocalIdPlusConstantAnalyser(GPUVerifier verifier) : base(verifier)
        {
            mayBeAnalyser = verifier.mayBeTidAnalyser;
        }

        override internal Expr MakeIdExpr()
        {
            return new IdentifierExpr(Token.NoToken, GPUVerifier._X);
        }

        internal override string idKind()
        {
            return "local id";
        }

        protected override string ComponentString()
        {
            return GPUVerifier.LOCAL_ID_X_STRING;
        }
    }

    class MayBeGlobalIdPlusConstantAnalyser : MayBeIdPlusConstantAnalyser
    {
        internal MayBeGlobalIdPlusConstantAnalyser(GPUVerifier verifier)
            : base(verifier)
        {
            mayBeAnalyser = verifier.mayBeGidAnalyser;
        }

        internal override string idKind()
        {
            return "global id";
        }

        override internal Expr MakeIdExpr()
        {
            return verifier.GlobalIdExpr("X");
        }

        protected override string ComponentString()
        {
            return "x";
        }

    }



}
