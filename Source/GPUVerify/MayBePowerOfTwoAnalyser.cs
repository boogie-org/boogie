using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify
{
    class MayBePowerOfTwoAnalyser
    {
        private GPUVerifier verifier;

        private Dictionary<string, Dictionary<string, bool>> mayBePowerOfTwoInfo;

        public MayBePowerOfTwoAnalyser(GPUVerifier verifier)
        {
            this.verifier = verifier;
            mayBePowerOfTwoInfo = new Dictionary<string, Dictionary<string, bool>>();
        }

        internal void Analyse()
        {
            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if (D is Implementation)
                {
                    Implementation Impl = D as Implementation;
                    mayBePowerOfTwoInfo.Add(Impl.Name, new Dictionary<string, bool>());

                    SetNotPowerOfTwo(Impl.Name, GPUVerifier._X.Name);
                    SetNotPowerOfTwo(Impl.Name, GPUVerifier._Y.Name);
                    SetNotPowerOfTwo(Impl.Name, GPUVerifier._Z.Name);

                    foreach (Variable v in Impl.LocVars)
                    {
                        SetNotPowerOfTwo(Impl.Name, v.Name);
                    }

                    foreach (Variable v in Impl.InParams)
                    {
                        SetNotPowerOfTwo(Impl.Name, v.Name);
                    }

                    foreach (Variable v in Impl.OutParams)
                    {
                        SetNotPowerOfTwo(Impl.Name, v.Name);
                    }

                    // Fixpoint not required - this is just syntactic
                    Analyse(Impl);

                }
            }

            if (CommandLineOptions.ShowMayBePowerOfTwoAnalysis)
            {
                dump();
            }
        }

        private void SetNotPowerOfTwo(string p, string v)
        {
            mayBePowerOfTwoInfo[p][v] = false;
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
                        Variable v = (assign.Lhss[0] as SimpleAssignLhs).AssignedVariable.Decl;
                        if (mayBePowerOfTwoInfo[impl.Name].ContainsKey(v.Name))
                        {
                            if (isPowerOfTwoOperation(v, assign.Rhss[0]))
                            {
                                mayBePowerOfTwoInfo[impl.Name][v.Name] = true;
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

        private bool isPowerOfTwoOperation(Variable v, Expr expr)
        {
            if (!(
                v.TypedIdent.Type.Equals(
                Microsoft.Boogie.Type.GetBvType(8))
                ||
                v.TypedIdent.Type.Equals(
                Microsoft.Boogie.Type.GetBvType(16))
                ||
                v.TypedIdent.Type.Equals(
                Microsoft.Boogie.Type.GetBvType(32))
                ))
            {
                return false;
            }

            Microsoft.Boogie.Type bvType = v.TypedIdent.Type as BvType;

            if (!(expr is NAryExpr))
            {
                return false;
            }

            NAryExpr nary = expr as NAryExpr;

            string bvPrefix = "BV" + bvType.BvBits + "_";

            if (nary.Fun.FunctionName.Equals(bvPrefix + "MUL"))
            {
                Debug.Assert(nary.Args.Length == 2);
                return
                   (
                    (IsVariable(nary.Args[0], v) || IsVariable(nary.Args[1], v)) &&
                    (IsConstant(nary.Args[0], 2) || IsConstant(nary.Args[1], 2))
                    );
            }

            if (nary.Fun.FunctionName.Equals(bvPrefix + "DIV"))
            {
                Debug.Assert(nary.Args.Length == 2);
                return
                   (
                    IsVariable(nary.Args[0], v) && IsConstant(nary.Args[1], 2)
                    );
            }

            if (nary.Fun.FunctionName.Equals(bvPrefix + "SHL"))
            {
                return
                   (
                    IsVariable(nary.Args[0], v) && IsConstant(nary.Args[1], 1)
                    );
            }

            if (nary.Fun.FunctionName.Equals(bvPrefix + "ASHR"))
            {
                return
                   (
                    IsVariable(nary.Args[0], v) && IsConstant(nary.Args[1], 1)
                    );
            }

            return false;
        }

        private bool IsConstant(Expr expr, int x)
        {
            if (!(expr is LiteralExpr))
            {
                return false;
            }

            LiteralExpr lit = expr as LiteralExpr;

            if (!(lit.Val is BvConst))
            {
                return false;
            }

            return (lit.Val as BvConst).Value.ToInt == x;
        }

        private bool IsVariable(Expr expr, Variable v)
        {
            return expr is IdentifierExpr && ((expr as IdentifierExpr).Decl.Name.Equals(v.Name));
        }

        private void dump()
        {
            foreach (string p in mayBePowerOfTwoInfo.Keys)
            {
                Console.WriteLine("Procedure " + p);
                foreach (string v in mayBePowerOfTwoInfo[p].Keys)
                {
                    Console.WriteLine("  " + v + ": " +
                        (mayBePowerOfTwoInfo[p][v] ? "may be power of two" : "likely not power of two"));
                }
            }

        }


        internal bool MayBePowerOfTwo(string p, string v)
        {
            if (!mayBePowerOfTwoInfo.ContainsKey(p))
            {
                return false;
            }

            if (!mayBePowerOfTwoInfo[p].ContainsKey(v))
            {
                return false;
            }

            return mayBePowerOfTwoInfo[p][v];
        }
    }
}
