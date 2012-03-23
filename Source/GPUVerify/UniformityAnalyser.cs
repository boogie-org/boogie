using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{

    class UniformityAnalyser
    {
        private GPUVerifier verifier;

        private Dictionary<string, bool> ProcedureChanged = null;

        private Dictionary<string, KeyValuePair<bool, Dictionary<string, bool>>> uniformityInfo;

        public UniformityAnalyser(GPUVerifier verifier)
        {
            this.verifier = verifier;
            uniformityInfo = new Dictionary<string, KeyValuePair<bool, Dictionary<string, bool>>>();
        }

        internal void Analyse()
        {
            ProcedureChanged = new Dictionary<string, bool>();

            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if(D is Implementation)
                {
                    bool uniformProcedure =
                        (D == verifier.KernelImplementation
                        || CommandLineOptions.DoUniformityAnalysis);

                    Implementation Impl = D as Implementation;
                    uniformityInfo.Add(Impl.Name, new KeyValuePair<bool, Dictionary<string, bool>>
                        (uniformProcedure, new Dictionary<string, bool> ()));

                    SetNonUniform(Impl.Name, GPUVerifier._X.Name);
                    SetNonUniform(Impl.Name, GPUVerifier._Y.Name);
                    SetNonUniform(Impl.Name, GPUVerifier._Z.Name);

                    foreach (Variable v in Impl.LocVars)
                    {
                        if (CommandLineOptions.DoUniformityAnalysis)
                        {
                            SetUniform(Impl.Name, v.Name);
                        }
                        else
                        {
                            SetNonUniform(Impl.Name, v.Name);
                        }
                    }

                    foreach (Variable v in Impl.InParams)
                    {
                        if (CommandLineOptions.DoUniformityAnalysis)
                        {
                            SetUniform(Impl.Name, v.Name);
                        }
                        else
                        {
                            SetNonUniform(Impl.Name, v.Name);
                        }
                    }

                    foreach (Variable v in Impl.OutParams)
                    {
                        if (CommandLineOptions.DoUniformityAnalysis)
                        {
                            SetUniform(Impl.Name, v.Name);
                        }
                        else
                        {
                            SetNonUniform(Impl.Name, v.Name);
                        }
                    }

                    ProcedureChanged[Impl.Name] = true;
                }
            }

            if (CommandLineOptions.DoUniformityAnalysis)
            {
                while (SomeProcedureRequiresAnalysis())
                {

                    foreach (Declaration D in verifier.Program.TopLevelDeclarations)
                    {
                        if (D is Implementation)
                        {
                            Implementation Impl = D as Implementation;
                            if (ProcedureChanged[Impl.Name])
                            {
                                Analyse(Impl, uniformityInfo[Impl.Name].Key);
                            }
                        }
                    }
                }
            }

            if (CommandLineOptions.ShowUniformityAnalysis)
            {
                dump();
            }
        }


        private bool SomeProcedureRequiresAnalysis()
        {
            foreach (string procedureName in ProcedureChanged.Keys)
            {
                if (ProcedureChanged[procedureName])
                {
                    return true;
                }
            }
            return false;
        }

        private void Analyse(Implementation Impl, bool ControlFlowIsUniform)
        {
            ProcedureChanged[Impl.Name] = false;
            Analyse(Impl, Impl.StructuredStmts, ControlFlowIsUniform);
        }

        private void Analyse(Implementation impl, StmtList stmtList, bool ControlFlowIsUniform)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                Analyse(impl, bb, ControlFlowIsUniform);
            }
        }

        private void Analyse(Implementation impl, BigBlock bb, bool ControlFlowIsUniform)
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

                        if (IsUniform(impl.Name, lhs.AssignedVariable.Name) &&
                            (!ControlFlowIsUniform || !IsUniform(impl.Name, rhs)))
                        {
                            SetNonUniform(impl.Name, lhs.AssignedVariable.Name);
                        }

                    }
                }
                else if (c is CallCmd)
                {
                    CallCmd callCmd = c as CallCmd;

                    if (callCmd.callee != verifier.BarrierProcedure.Name)
                    {

                        if (!ControlFlowIsUniform)
                        {
                            if (IsUniform(callCmd.callee))
                            {
                                SetNonUniform(callCmd.callee);
                            }
                        }
                        Implementation CalleeImplementation = GetImplementation(callCmd.callee);
                        for (int i = 0; i < CalleeImplementation.InParams.Length; i++)
                        {
                            if (IsUniform(callCmd.callee, CalleeImplementation.InParams[i].Name)
                                && !IsUniform(impl.Name, callCmd.Ins[i]))
                            {
                                SetNonUniform(callCmd.callee, CalleeImplementation.InParams[i].Name);
                            }
                        }

                        for (int i = 0; i < CalleeImplementation.OutParams.Length; i++)
                        {
                            if (IsUniform(impl.Name, callCmd.Outs[i].Name)
                                && !IsUniform(callCmd.callee, CalleeImplementation.OutParams[i].Name))
                            {
                                SetNonUniform(impl.Name, callCmd.Outs[i].Name);
                            }
                        }

                    }
                }
            }

            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;
                Analyse(impl, wc.Body, ControlFlowIsUniform && IsUniform(impl.Name, wc.Guard));
            }
            else if (bb.ec is IfCmd)
            {
                IfCmd ifCmd = bb.ec as IfCmd;
                Analyse(impl, ifCmd.thn, ControlFlowIsUniform && IsUniform(impl.Name, ifCmd.Guard));
                if (ifCmd.elseBlock != null)
                {
                    Analyse(impl, ifCmd.elseBlock, ControlFlowIsUniform && IsUniform(impl.Name, ifCmd.Guard));
                }
                Debug.Assert(ifCmd.elseIf == null);
            }

        }

        private Implementation GetImplementation(string procedureName)
        {
            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if (D is Implementation && ((D as Implementation).Name == procedureName))
                {
                    return D as Implementation;
                }
            }
            Debug.Assert(false);
            return null;
        }

        private void SetNonUniform(string procedureName)
        {
            uniformityInfo[procedureName] = new KeyValuePair<bool,Dictionary<string,bool>>
                (false, uniformityInfo[procedureName].Value);
            RecordProcedureChanged(procedureName);
        }

        internal bool IsUniform(string procedureName)
        {
            if (!uniformityInfo.ContainsKey(procedureName))
            {
                return false;
            }
            return uniformityInfo[procedureName].Key;
        }

        internal bool IsUniform(string procedureName, Expr expr)
        {
            UniformExpressionAnalysisVisitor visitor = new UniformExpressionAnalysisVisitor(uniformityInfo[procedureName].Value);
            visitor.VisitExpr(expr);
            return visitor.IsUniform();
        }

        internal bool IsUniform(string procedureName, string v)
        {
            Debug.Assert(uniformityInfo.ContainsKey(procedureName));
            return uniformityInfo[procedureName].Value[v];
        }

        private void SetUniform(string procedureName, string v)
        {
            uniformityInfo[procedureName].Value[v] = true;
            RecordProcedureChanged(procedureName);
        }

        private void RecordProcedureChanged(string procedureName)
        {
            ProcedureChanged[procedureName] = true;
        }

        private void SetNonUniform(string procedureName, string v)
        {
            uniformityInfo[procedureName].Value[v] = false;
            RecordProcedureChanged(procedureName);
        }

        private void dump()
        {
            foreach (string p in uniformityInfo.Keys)
            {
                Console.WriteLine("Procedure " + p + ": "
                    + (uniformityInfo[p].Key ? "uniform" : "nonuniform"));
                foreach (string v in uniformityInfo[p].Value.Keys)
                {
                    Console.WriteLine("  " + v + ": " +
                        (uniformityInfo[p].Value[v] ? "uniform" : "nonuniform"));
                }
            }
        }

    }

}
