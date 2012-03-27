using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class MayBeTidPlusConstantAnalyser
    {
        private GPUVerifier verifier;

        // Given a p.v, says whether p.v may be assigned to a tid variable at some point
        private Dictionary<string, Dictionary<string, bool>> mayBeAssignedTid;

        // Records the constants (as strings) that p.v may be incremented by
        private Dictionary<string, Dictionary<string, HashSet<string>>> incrementedBy;

        // The final result
        private Dictionary<string, Dictionary<string, bool>> mayBeTidPlusConstantInfo;

        public MayBeTidPlusConstantAnalyser(GPUVerifier verifier)
        {
            this.verifier = verifier;
            mayBeAssignedTid = new Dictionary<string, Dictionary<string, bool>>();
            incrementedBy = new Dictionary<string, Dictionary<string, HashSet<string>>>();
            mayBeTidPlusConstantInfo = new Dictionary<string, Dictionary<string, bool>>();
        }

        internal void Analyse()
        {
            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if (D is Implementation)
                {
                    Implementation Impl = D as Implementation;
                    mayBeAssignedTid[Impl.Name] = new Dictionary<string, bool>();
                    incrementedBy[Impl.Name] = new Dictionary<string, HashSet<string>>();
                    mayBeTidPlusConstantInfo[Impl.Name] = new Dictionary<string, bool> ();

                    foreach (Variable v in Impl.LocVars)
                    {
                        mayBeAssignedTid[Impl.Name][v.Name] = false;
                        incrementedBy[Impl.Name][v.Name] = new HashSet<string>();
                    }

                    foreach (Variable v in Impl.InParams)
                    {
                        mayBeAssignedTid[Impl.Name][v.Name] = false;
                        incrementedBy[Impl.Name][v.Name] = new HashSet<string>();
                    }

                    foreach (Variable v in Impl.OutParams)
                    {
                        mayBeAssignedTid[Impl.Name][v.Name] = false;
                        incrementedBy[Impl.Name][v.Name] = new HashSet<string>();
                    }

                    // Fixpoint not required - this is just syntactic
                    Analyse(Impl);

                    foreach (string v in mayBeAssignedTid[Impl.Name].Keys)
                    {
                        mayBeTidPlusConstantInfo[Impl.Name][v] =
                            mayBeAssignedTid[Impl.Name][v] && incrementedBy[Impl.Name][v].Count == 1;
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
                    assign = c as AssignCmd;
                    Debug.Assert(assign.Lhss.Count == 1);
                    Debug.Assert(assign.Rhss.Count == 1);

                    if (assign.Lhss[0] is SimpleAssignLhs)
                    {
                        Variable lhsV = (assign.Lhss[0] as SimpleAssignLhs).AssignedVariable.Decl;

                        if (mayBeAssignedTid[impl.Name].ContainsKey(lhsV.Name))
                        {

                            if (assign.Rhss[0] is IdentifierExpr)
                            {

                                Variable rhsV = (assign.Rhss[0] as IdentifierExpr).Decl;

                                if (verifier.mayBeTidAnalyser.MayBeTid(impl.Name, rhsV.Name))
                                {
                                    mayBeAssignedTid[impl.Name][lhsV.Name] = true;
                                }

                            }
                            else
                            {

                                Expr constantIncrement = GetConstantIncrement(lhsV, assign.Rhss[0]);

                                if (constantIncrement != null)
                                {
                                    incrementedBy[impl.Name][lhsV.Name].Add(ConvertToString(constantIncrement));
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
            foreach (string p in mayBeTidPlusConstantInfo.Keys)
            {
                Console.WriteLine("Procedure " + p);
                foreach (string v in mayBeTidPlusConstantInfo[p].Keys)
                {
                    Console.WriteLine("  " + v + ": gets assigned tid - " + mayBeAssignedTid[p][v]);
                    Console.Write("  " + v + ": incremented by -");
                    foreach(string s in incrementedBy[p][v])
                    {
                        Console.Write(" " + s);
                    }
                    Console.WriteLine("");

                    Console.Write("  " + v + ": ");
                    
                    if(mayBeTidPlusConstantInfo[p][v])
                    {
                        Console.Write("may be tid + ");
                        foreach(string s in incrementedBy[p][v])
                        {
                            Console.WriteLine(s);
                        }
                    }
                    else
                    {
                        Console.WriteLine("likely not tid + const");
                    }
                }
            }

        }


        internal bool MayBeTidPlusConstant(string p, string v)
        {
            if (!mayBeTidPlusConstantInfo.ContainsKey(p))
            {
                return false;
            }

            if (!mayBeTidPlusConstantInfo[p].ContainsKey(v))
            {
                return false;
            }

            return mayBeTidPlusConstantInfo[p][v];
        }
    
    }
}
