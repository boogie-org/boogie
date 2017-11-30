using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{

    public class UniformityAnalyser
    {
        private Program prog;

        private bool doAnalysis;

        private ISet<Implementation> entryPoints;

        private IEnumerable<Variable> nonUniformVars;

        private bool ProcedureChanged;

        private Dictionary<string, KeyValuePair<bool, Dictionary<string, bool>>> uniformityInfo;

        private Dictionary<string, HashSet<int>> nonUniformLoops;

        private Dictionary<string, HashSet<Block>> nonUniformBlocks;

        private Dictionary<string, HashSet<int>> loopsWithNonuniformReturn;

        private Dictionary<string, List<string>> inParameters;

        private Dictionary<string, List<string>> outParameters;

        /// <summary>
        /// Simplifies the CFG of the given implementation impl by merging each
        /// basic block with a single predecessor into that predecessor if the
        /// predecessor has a single successor.  If a uniformity analyser is
        /// being used then blocks will only be merged if they are both uniform
        /// or both non-uniform
        /// </summary>
        public static void MergeBlocksIntoPredecessors(Program prog, Implementation impl, UniformityAnalyser uni)
        {
            var blockGraph = prog.ProcessLoops(impl);
            var predMap = new Dictionary<Block, Block>();
            foreach (var block in blockGraph.Nodes)
            {
                try
                {
                    var pred = blockGraph.Predecessors(block).Single();
                    if (blockGraph.Successors(pred).Single() == block &&
                        (uni == null ||
                        (uni.IsUniform(impl.Name, pred) && uni.IsUniform(impl.Name, block)) ||
                        (!uni.IsUniform(impl.Name, pred) && !uni.IsUniform(impl.Name, block))))
                    {
                        Block predMapping;
                        while (predMap.TryGetValue(pred, out predMapping))
                            pred = predMapping;
                        pred.Cmds.AddRange(block.Cmds);
                        pred.TransferCmd = block.TransferCmd;
                        impl.Blocks.Remove(block);
                        predMap[block] = pred;
                    }
                    // If Single throws an exception above (i.e. not exactly one pred/succ), skip this block.
                }
                catch (InvalidOperationException) { }
            }
        }

        public UniformityAnalyser(Program prog, bool doAnalysis, ISet<Implementation> entryPoints, IEnumerable<Variable> nonUniformVars)
        {
            this.prog = prog;
            this.doAnalysis = doAnalysis;
            this.entryPoints = entryPoints;
            this.nonUniformVars = nonUniformVars;
            uniformityInfo = new Dictionary<string, KeyValuePair<bool, Dictionary<string, bool>>>();
            nonUniformLoops = new Dictionary<string, HashSet<int>>();
            nonUniformBlocks = new Dictionary<string, HashSet<Block>>();
            loopsWithNonuniformReturn = new Dictionary<string, HashSet<int>>();
            inParameters = new Dictionary<string, List<string>>();
            outParameters = new Dictionary<string, List<string>>();
        }

        public void Analyse()
        {
            var impls = prog.Implementations;

            foreach (var Impl in impls)
            {
                bool uniformProcedure = doAnalysis || entryPoints.Contains(Impl);

                uniformityInfo.Add(Impl.Name, new KeyValuePair<bool, Dictionary<string, bool>>
                    (uniformProcedure, new Dictionary<string, bool> ()));

                nonUniformLoops.Add(Impl.Name, new HashSet<int>());
                loopsWithNonuniformReturn.Add(Impl.Name, new HashSet<int>());

                foreach (var v in nonUniformVars)
                    SetNonUniform(Impl.Name, v.Name);

                foreach (Variable v in Impl.LocVars)
                {
                    if (doAnalysis)
                    {
                        SetUniform(Impl.Name, v.Name);
                    }
                    else
                    {
                        SetNonUniform(Impl.Name, v.Name);
                    }
                }

                inParameters[Impl.Name] = new List<string>();

                foreach (Variable v in Impl.InParams)
                {
                    inParameters[Impl.Name].Add(v.Name);
                    if (doAnalysis)
                    {
                        SetUniform(Impl.Name, v.Name);
                    }
                    else
                    {
                        SetNonUniform(Impl.Name, v.Name);
                    }
                }

                outParameters[Impl.Name] = new List<string>();
                foreach (Variable v in Impl.OutParams)
                {
                    outParameters[Impl.Name].Add(v.Name);
                    if (doAnalysis)
                    {
                        SetUniform(Impl.Name, v.Name);
                    }
                    else
                    {
                        SetNonUniform(Impl.Name, v.Name);
                    }
                }

                ProcedureChanged = true;
            }

            var procs = prog.Procedures;

            foreach (var Proc in procs) {

              if (uniformityInfo.ContainsKey(Proc.Name)) {
                continue;
              }

              bool uniformProcedure = doAnalysis;

              uniformityInfo.Add(Proc.Name, new KeyValuePair<bool, Dictionary<string, bool>>
                  (uniformProcedure, new Dictionary<string, bool>()));

              inParameters[Proc.Name] = new List<string>();

              foreach (Variable v in Proc.InParams) {
                inParameters[Proc.Name].Add(v.Name);
                if (doAnalysis) {
                  SetUniform(Proc.Name, v.Name);
                }
                else {
                  SetNonUniform(Proc.Name, v.Name);
                }
              }

              outParameters[Proc.Name] = new List<string>();
              foreach (Variable v in Proc.OutParams) {
                outParameters[Proc.Name].Add(v.Name);
                // We do not have a body for the procedure,
                // so we must assume it produces non-uniform
                // results
                SetNonUniform(Proc.Name, v.Name);
              }

              ProcedureChanged = true;
            }


            if (doAnalysis)
            {
                while (ProcedureChanged)
                {
                    ProcedureChanged = false;

                    foreach (var Impl in impls)
                    {
                        Analyse(Impl, uniformityInfo[Impl.Name].Key);
                    }
                }
            }

            foreach (var Proc in procs)
            {
                if (!IsUniform (Proc.Name))
                {
                    List<string> newIns = new List<String>();
                    newIns.Add("_P");
                    foreach (string s in inParameters[Proc.Name])
                    {
                        newIns.Add(s);
                    }
                    foreach (string s in outParameters[Proc.Name])
                    {
                        newIns.Add("_V" + s);
                    }
                    inParameters[Proc.Name] = newIns;
                }
            }
        }

        private void Analyse(Implementation Impl, bool ControlFlowIsUniform)
        {
            if (!ControlFlowIsUniform)
            {
                nonUniformBlocks[Impl.Name] = new HashSet<Block>(Impl.Blocks);

                foreach (Variable v in Impl.LocVars) {
                    if (IsUniform(Impl.Name, v.Name)) {
                        SetNonUniform(Impl.Name, v.Name);
                    }
                }

                foreach (Variable v in Impl.InParams) {
                    if (IsUniform(Impl.Name, v.Name)) {
                        SetNonUniform(Impl.Name, v.Name);
                    }
                }

                foreach (Variable v in Impl.OutParams) {
                  if (IsUniform(Impl.Name, v.Name)) {
                      SetNonUniform(Impl.Name, v.Name);
                  }
                }

                foreach (Block b in Impl.Blocks) {
                  Analyse(Impl, b.Cmds, false);
                }

                return;
            }

            Graph<Block> blockGraph = prog.ProcessLoops(Impl);
            var ctrlDep = blockGraph.ControlDependence();

            // Compute transitive closure of control dependence info.
            ctrlDep.TransitiveClosure();

            var nonUniformBlockSet = new HashSet<Block>();
            nonUniformBlocks[Impl.Name] = nonUniformBlockSet;

            bool changed;
            do {
              changed = false;
              foreach (var block in Impl.Blocks) {
                bool uniform = !nonUniformBlockSet.Contains(block);
                bool newUniform = Analyse(Impl, block.Cmds, uniform);
                if (uniform && !newUniform) {
                  changed = true;
                  nonUniformBlockSet.Add(block);
                  Block pred = blockGraph.Predecessors(block).Single();
                  if (ctrlDep.ContainsKey(pred))
                    nonUniformBlockSet.UnionWith(ctrlDep[pred]);
                }
              }
            } while (changed);
        }

        private Procedure GetProcedure(string procedureName)
        {
            foreach (var p in prog.Procedures)
            {
                if (p.Name == procedureName)
                {
                    return p;
                }
            }
            Debug.Assert(false);
            return null;
        }

        private bool Analyse(Implementation impl, List<Cmd> cmdSeq, bool ControlFlowIsUniform)
        {
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assignCmd = c as AssignCmd;
                    foreach (var a in assignCmd.Lhss.Zip(assignCmd.Rhss))
                    {

                        if (a.Item1 is SimpleAssignLhs)
                        {
                            SimpleAssignLhs lhs = a.Item1 as SimpleAssignLhs;
                            Expr rhs = a.Item2;
                            if (IsUniform(impl.Name, lhs.AssignedVariable.Name) &&
                                (!ControlFlowIsUniform || !IsUniform(impl.Name, rhs)))
                            {
                                SetNonUniform(impl.Name, lhs.AssignedVariable.Name);
                            }

                        }
                    }
                }
                else if (c is HavocCmd)
                {
                    HavocCmd havocCmd = c as HavocCmd;
                    foreach(IdentifierExpr ie in havocCmd.Vars)
                    {
                        if(IsUniform(impl.Name, ie.Decl.Name)) {
                            SetNonUniform(impl.Name, ie.Decl.Name);
                        }
                    }
                }
                else if (c is CallCmd)
                {
                    CallCmd callCmd = c as CallCmd;
                    DeclWithFormals Callee = GetProcedure(callCmd.callee);
                    Debug.Assert(Callee != null);

                    if (!ControlFlowIsUniform)
                    {
                        if (IsUniform(callCmd.callee))
                        {
                            SetNonUniform(callCmd.callee);
                        }
                    }
                    for (int i = 0; i < Callee.InParams.Count; i++)
                    {
                        if (IsUniform(callCmd.callee, Callee.InParams[i].Name)
                            && !IsUniform(impl.Name, callCmd.Ins[i]))
                        {
                            SetNonUniform(callCmd.callee, Callee.InParams[i].Name);
                        }
                    }

                    for (int i = 0; i < Callee.OutParams.Count; i++)
                    {
                        if (IsUniform(impl.Name, callCmd.Outs[i].Name)
                        && !IsUniform(callCmd.callee, Callee.OutParams[i].Name))
                        {
                            SetNonUniform(impl.Name, callCmd.Outs[i].Name);
                        }
                    }

                }
                else if (c is AssumeCmd)
                {
                    var ac = (AssumeCmd)c;
                    if (ControlFlowIsUniform && QKeyValue.FindBoolAttribute(ac.Attributes, "partition") &&
                        !IsUniform(impl.Name, ac.Expr))
                    {
                      ControlFlowIsUniform = false;
                    }
                }
            }

            return ControlFlowIsUniform;
        }

        private int GetLoopId(WhileCmd wc)
        {
            AssertCmd inv = wc.Invariants[0] as AssertCmd;
            Debug.Assert(inv.Attributes.Key.Contains("loophead_"));
            return Convert.ToInt32(inv.Attributes.Key.Substring("loophead_".Length));
        }

        private void SetNonUniform(string procedureName)
        {
            uniformityInfo[procedureName] = new KeyValuePair<bool,Dictionary<string,bool>>
                (false, uniformityInfo[procedureName].Value);
            RecordProcedureChanged();
        }

        private void SetNonUniform(string procedureName, WhileCmd wc)
        {
            nonUniformLoops[procedureName].Add(GetLoopId(wc));
            RecordProcedureChanged();
        }

        public bool IsUniform(string procedureName)
        {
            if (!uniformityInfo.ContainsKey(procedureName))
            {
                return false;
            }
            return uniformityInfo[procedureName].Key;
        }

        public bool IsUniform(string procedureName, Block b)
        {
            if (!nonUniformBlocks.ContainsKey(procedureName))
            {
                return false;
            }
            return !nonUniformBlocks[procedureName].Contains(b);
        }

        class UniformExpressionAnalysisVisitor : ReadOnlyVisitor {

          private bool isUniform = true;
          private Dictionary<string, bool> uniformityInfo;

          public UniformExpressionAnalysisVisitor(Dictionary<string, bool> uniformityInfo) {
            this.uniformityInfo = uniformityInfo;
          }

          public override Variable VisitVariable(Variable v) {
            if (!uniformityInfo.ContainsKey(v.Name)) {
              isUniform = isUniform && (v is Constant);
            } else if (!uniformityInfo[v.Name]) {
              isUniform = false;
            }

            return v;
          }

          internal bool IsUniform() {
            return isUniform;
          }
        }

        public bool IsUniform(string procedureName, Expr expr)
        {
            if (!uniformityInfo.ContainsKey(procedureName))
            {
                return false;
            }

            UniformExpressionAnalysisVisitor visitor = new UniformExpressionAnalysisVisitor(uniformityInfo[procedureName].Value);
            visitor.VisitExpr(expr);
            return visitor.IsUniform();
        }

        public bool IsUniform(string procedureName, string v)
        {
            if (!uniformityInfo.ContainsKey(procedureName))
            {
                return false;
            }

            if (!uniformityInfo[procedureName].Value.ContainsKey(v))
            {
                return false;
            }
            return uniformityInfo[procedureName].Value[v];
        }

        private void SetUniform(string procedureName, string v)
        {
            uniformityInfo[procedureName].Value[v] = true;
            RecordProcedureChanged();
        }

        private void RecordProcedureChanged()
        {
            ProcedureChanged = true;
        }

        private void SetNonUniform(string procedureName, string v)
        {
            uniformityInfo[procedureName].Value[v] = false;
            RecordProcedureChanged();
        }

        public void dump()
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
                Console.Write("Ins [");
                for (int i = 0; i < inParameters[p].Count; i++)
                {
                    Console.Write((i == 0 ? "" : ", ") + inParameters[p][i]);
                }
                Console.WriteLine("]");
                Console.Write("Outs [");
                for (int i = 0; i < outParameters[p].Count; i++)
                {
                    Console.Write((i == 0 ? "" : ", ") + outParameters[p][i]);
                }
                Console.WriteLine("]");
                if (nonUniformLoops.ContainsKey(p)) {
                Console.Write("Non-uniform loops:");
                  foreach (int l in nonUniformLoops[p]) {
                    Console.Write(" " + l);
                }
                Console.WriteLine();
                }
                if (nonUniformBlocks.ContainsKey(p)) {
                Console.Write("Non-uniform blocks:");
                  foreach (Block b in nonUniformBlocks[p]) {
                    Console.Write(" " + b.Label);
                }
                Console.WriteLine();
            }
        }
        }


        public string GetInParameter(string procName, int i)
        {
            return inParameters[procName][i];
        }

        public string GetOutParameter(string procName, int i)
        {
            return outParameters[procName][i];
        }


        public bool knowsOf(string p)
        {
            return uniformityInfo.ContainsKey(p);
        }

        public void AddNonUniform(string proc, string v)
        {
            if (uniformityInfo.ContainsKey(proc))
            {
                Debug.Assert(!uniformityInfo[proc].Value.ContainsKey(v));
                uniformityInfo[proc].Value[v] = false;
            }
        }

        public void AddNonUniform(string proc, Block b) {
          if (nonUniformBlocks.ContainsKey(proc)) {
            Debug.Assert(!nonUniformBlocks[proc].Contains(b));
            nonUniformBlocks[proc].Add(b);
          }
        }

    }

}
