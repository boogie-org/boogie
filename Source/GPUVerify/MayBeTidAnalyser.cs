using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class MayBeTidAnalyser
    {

        private GPUVerifier verifier;

        private bool ProcedureChanged;

        private Dictionary<string, Dictionary<string, bool>> mayBeTidInfo;

        public MayBeTidAnalyser(GPUVerifier verifier)
        {
            this.verifier = verifier;
            mayBeTidInfo = new Dictionary<string, Dictionary<string, bool>>();
        }

        internal void Analyse()
        {
            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if(D is Implementation)
                {
                    Implementation Impl = D as Implementation;
                    mayBeTidInfo.Add(Impl.Name, new Dictionary<string, bool> ());

                    SetMayBeTid(Impl.Name, GPUVerifier._X.Name);
                    SetNotTid(Impl.Name, GPUVerifier._Y.Name);
                    SetNotTid(Impl.Name, GPUVerifier._Z.Name);

                    foreach (Variable v in Impl.LocVars)
                    {
                        SetMayBeTid(Impl.Name, v.Name);
                    }

                    foreach (Variable v in Impl.InParams)
                    {
                        SetMayBeTid(Impl.Name, v.Name);
                    }

                    foreach (Variable v in Impl.OutParams)
                    {
                        SetMayBeTid(Impl.Name, v.Name);
                    }

                    ProcedureChanged = true;
                }
            }

            while (ProcedureChanged)
            {
                ProcedureChanged = false;

                foreach (Declaration D in verifier.Program.TopLevelDeclarations)
                {
                    if (D is Implementation)
                    {
                        Implementation Impl = D as Implementation;
                        Analyse(Impl);
                    }
                }
            }

            if (CommandLineOptions.ShowMayBeTidAnalysis)
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
                    AssignCmd assignCmd = c as AssignCmd;
                    Debug.Assert(assignCmd.Lhss.Count == 1);
                    Debug.Assert(assignCmd.Rhss.Count == 1);
                    if (assignCmd.Lhss[0] is SimpleAssignLhs)
                    {
                        SimpleAssignLhs lhs = assignCmd.Lhss[0] as SimpleAssignLhs;
                        Expr rhs = assignCmd.Rhss[0];

                        if (MayBeTid (impl.Name, lhs.AssignedVariable.Name)
                            && !MayBeTid(impl.Name, rhs))
                        {
                            SetNotTid (impl.Name, lhs.AssignedVariable.Name);
                        }

                    }
                }
                else if (c is CallCmd)
                {
                    CallCmd callCmd = c as CallCmd;

                    if (callCmd.callee != verifier.BarrierProcedure.Name)
                    {

                        Implementation CalleeImplementation = verifier.GetImplementation(callCmd.callee);
                        for (int i = 0; i < CalleeImplementation.InParams.Length; i++)
                        {
                            if (MayBeTid(callCmd.callee, CalleeImplementation.InParams[i].Name)
                                && !MayBeTid(impl.Name, callCmd.Ins[i]))
                            {
                                SetNotTid(callCmd.callee, CalleeImplementation.InParams[i].Name);
                            }
                        }

                        for (int i = 0; i < CalleeImplementation.OutParams.Length; i++)
                        {
                            if (MayBeTid(impl.Name, callCmd.Outs[i].Name)
                                && !MayBeTid(callCmd.callee, CalleeImplementation.OutParams[i].Name))
                            {
                                SetNotTid(impl.Name, callCmd.Outs[i].Name);
                            }
                        }

                    }
                    else if (c is HavocCmd)
                    {
                        HavocCmd havoc = c as HavocCmd;
                        Debug.Assert(havoc.Vars.Length == 1);

                        if (MayBeTid(impl.Name, havoc.Vars[0].Decl.Name))
                        {
                            SetNotTid(impl.Name, havoc.Vars[0].Decl.Name);
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

        private void SetNotTid(string proc, string v)
        {
            mayBeTidInfo[proc][v] = false;
            ProcedureChanged = true;
        }

        private void SetMayBeTid(string proc, string v)
        {
            mayBeTidInfo[proc][v] = true;
        }

        internal bool MayBeTid(string proc, string v)
        {
            if (!mayBeTidInfo.ContainsKey(proc))
            {
                return false;
            }

            if (!mayBeTidInfo[proc].ContainsKey(v))
            {
                return false;
            }

            return mayBeTidInfo[proc][v];
        }

        internal bool MayBeTid(string proc, Expr e)
        {
            if (e is IdentifierExpr)
            {
                return MayBeTid(proc, (e as IdentifierExpr).Decl.Name);
            }
            return false;
        }

        private void dump()
        {
            foreach (string p in mayBeTidInfo.Keys)
            {
                Console.WriteLine("Procedure " + p);
                foreach (string v in mayBeTidInfo[p].Keys)
                {
                    Console.WriteLine("  " + v + ": " +
                        (mayBeTidInfo[p][v] ? "may be tid" : "likely not tid"));
                }
            }

        }

    }
}
