using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class MayBeGidAnalyser
    {
        private static string[] dimensions = { "x", "y", "z" };

        private GPUVerifier verifier;

        private bool ProcedureChanged;

        private Dictionary<string, Dictionary<string, Dictionary<string, bool>>> mayBeInfo;

        public MayBeGidAnalyser(GPUVerifier verifier)
        {
            this.verifier = verifier;

            mayBeInfo = new Dictionary<string,Dictionary<string,Dictionary<string,bool>>>();
            foreach (string s in dimensions)
            {
                mayBeInfo[s] = new Dictionary<string, Dictionary<string, bool>>();
            }
        
        }

        internal void Analyse()
        {
            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if(D is Implementation)
                {
                    Implementation Impl = D as Implementation;

                    foreach (string s in dimensions)
                    {
                        mayBeInfo[s][Impl.Name] = new Dictionary<string, bool>();
                    }

                    foreach (Variable v in Impl.LocVars)
                    {
                        foreach (string s in dimensions)
                        {
                            SetMayBe(s, Impl.Name, v.Name);
                        }
                    }

                    foreach (Variable v in Impl.InParams)
                    {
                        foreach (string s in dimensions)
                        {
                            SetMayBe(s, Impl.Name, v.Name);
                        }
                    }

                    foreach (Variable v in Impl.OutParams)
                    {
                        foreach (string s in dimensions)
                        {
                            SetMayBe(s, Impl.Name, v.Name);
                        }
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

            if (CommandLineOptions.ShowMayBeThreadConfigurationVariableAnalysis)
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
                    foreach (string s in dimensions)
                    {
                        TransferAssign(impl, c as AssignCmd, s);
                    }
                }
                else if (c is CallCmd)
                {
                    foreach (string s in dimensions)
                    {
                        TransferCall(impl, c as CallCmd, s);
                    }
                }
                else if (c is HavocCmd)
                {
                    foreach (string s in dimensions)
                    {
                        TransferHavoc(impl, c as HavocCmd, s);
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

        private void TransferHavoc(Implementation impl, HavocCmd havoc, string component)
        {
            Debug.Assert(havoc.Vars.Length == 1);
            if (MayBe(component, impl.Name, havoc.Vars[0].Decl.Name))
            {
                SetNot(component, impl.Name, havoc.Vars[0].Decl.Name);
            }
        }

        private void TransferCall(Implementation impl, CallCmd callCmd, string component)
        {
            if (callCmd.callee != verifier.BarrierProcedure.Name)
            {

                Implementation CalleeImplementation = verifier.GetImplementation(callCmd.callee);
                for (int i = 0; i < CalleeImplementation.InParams.Length; i++)
                {
                    if (MayBe(component, callCmd.callee, CalleeImplementation.InParams[i].Name)
                        && !MayBe(component, impl.Name, callCmd.Ins[i]))
                    {
                        SetNot(component, callCmd.callee, CalleeImplementation.InParams[i].Name);
                    }
                }

                for (int i = 0; i < CalleeImplementation.OutParams.Length; i++)
                {
                    if (MayBe(component, impl.Name, callCmd.Outs[i].Name)
                        && !MayBe(component, callCmd.callee, CalleeImplementation.OutParams[i].Name))
                    {
                        SetNot(component, impl.Name, callCmd.Outs[i].Name);
                    }
                }

            }
        }

        private void TransferAssign(Implementation impl, AssignCmd assignCmd, string component)
        {
            Debug.Assert(assignCmd.Lhss.Count == 1);
            Debug.Assert(assignCmd.Rhss.Count == 1);
            if (assignCmd.Lhss[0] is SimpleAssignLhs)
            {
                SimpleAssignLhs lhs = assignCmd.Lhss[0] as SimpleAssignLhs;
                Expr rhs = assignCmd.Rhss[0];

                if (MayBe(component, impl.Name, lhs.AssignedVariable.Name)
                    && !MayBe(component, impl.Name, rhs))
                {
                    SetNot(component, impl.Name, lhs.AssignedVariable.Name);
                }

            }
        }

        private void SetNot(string component, string proc, string v)
        {
            mayBeInfo[component][proc][v] = false;
            ProcedureChanged = true;
        }

        private void SetMayBe(string component, string proc, string v)
        {
            mayBeInfo[component][proc][v] = true;
        }

        internal bool MayBe(string component, string proc, string v)
        {
            if (!mayBeInfo[component].ContainsKey(proc))
            {
                return false;
            }

            if (!mayBeInfo[component][proc].ContainsKey(v))
            {
                return false;
            }

            return mayBeInfo[component][proc][v];
        }

        internal bool MayBe(string component, string proc, Expr e)
        {
            if (e is IdentifierExpr)
            {
                return MayBe(component, proc, (e as IdentifierExpr).Decl.Name);
            }

            if (e is NAryExpr && (e as NAryExpr).Fun.FunctionName.Equals("BV32_ADD"))
            {
                NAryExpr nary = e as NAryExpr;

                string localIdString = null;

                if (component.Equals("x"))
                {
                    localIdString = GPUVerifier.LOCAL_ID_X_STRING;
                }
                else if (component.Equals("y"))
                {
                    localIdString = GPUVerifier.LOCAL_ID_Y_STRING;
                }
                else if (component.Equals("z"))
                {
                    localIdString = GPUVerifier.LOCAL_ID_Z_STRING;
                }
                else
                {
                    Debug.Assert(false);
                }

                if(verifier.mayBeTidAnalyser.MayBe(localIdString, proc, nary.Args[1]))
                {
                    return IsGroupIdTimesGroupSize(component, proc, nary.Args[0]);
                }

                if (verifier.mayBeTidAnalyser.MayBe(localIdString, proc, nary.Args[0]))
                {
                    return IsGroupIdTimesGroupSize(component, proc, nary.Args[1]);
                }
            }

            return false;
        }

        private bool IsGroupIdTimesGroupSize(string component, string proc, Expr expr)
        {
            if (expr is NAryExpr && (expr as NAryExpr).Fun.FunctionName.Equals("BV32_MUL"))
            {
                NAryExpr innerNary = expr as NAryExpr;

                if (IsGroupIdAndSize(component, proc, innerNary.Args[0], innerNary.Args[1]))
                {
                    return true;
                }

                if (IsGroupIdAndSize(component, proc, innerNary.Args[1], innerNary.Args[0]))
                {
                    return true;
                }
            }
            return false;
        }

        private bool IsGroupIdAndSize(string component, string proc, Expr maybeGroupId, Expr maybeGroupSize)
        {
            string groupIdString = null;
            string groupSizeString = null;
            if (component.Equals("x"))
            {
                groupIdString = GPUVerifier.GROUP_ID_X_STRING;
                groupSizeString = GPUVerifier.GROUP_SIZE_X_STRING;
            }
            else if (component.Equals("y"))
            {
                groupIdString = GPUVerifier.GROUP_ID_Y_STRING;
                groupSizeString = GPUVerifier.GROUP_SIZE_Y_STRING;
            }
            else if (component.Equals("z"))
            {
                groupIdString = GPUVerifier.GROUP_ID_Z_STRING;
                groupSizeString = GPUVerifier.GROUP_SIZE_Z_STRING;
            }
            else
            {
                Debug.Assert(false);
            }

            return verifier.mayBeTidAnalyser.MayBe(groupIdString, proc, maybeGroupId) &&
                                       verifier.mayBeTidAnalyser.MayBe(groupSizeString, proc, maybeGroupSize);
        }

        private void dump()
        {
            foreach (string s in dimensions)
            {
                Console.WriteLine("*** global_id_" + s + " ***");

                foreach (string p in mayBeInfo[s].Keys)
                {
                    Console.WriteLine("  Procedure " + p);

                    foreach (string v in mayBeInfo[s][p].Keys)
                    {
                        if (mayBeInfo[s][p][v])
                        {
                            Console.WriteLine("    " + v + ": may be global_id_" + s);
                        }
                    }
                }
            }

        }

    }
}
