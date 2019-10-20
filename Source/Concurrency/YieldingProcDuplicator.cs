using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public class YieldingProcDuplicator : Duplicator
    {
        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private Dictionary<Procedure, Procedure> procToSkipProcDummy;
        private YieldingProc enclosingYieldingProc;

        private int layerNum;
        private Dictionary<Procedure, Procedure> procMap; /* Original -> Duplicate */
        private Dictionary<Absy, Absy> absyMap; /* Duplicate -> Original */
        private Dictionary<Implementation, Implementation> implMap; /* Duplicate -> Original */
        private HashSet<Procedure> yieldingProcs;

        public YieldingProcDuplicator(CivlTypeChecker civlTypeChecker, LinearTypeChecker linearTypeChecker,
            int layerNum, Dictionary<Procedure, Procedure> procToSkipProcDummy)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.layerNum = layerNum;
            this.procToSkipProcDummy = procToSkipProcDummy;

            this.procMap = new Dictionary<Procedure, Procedure>();
            this.absyMap = new Dictionary<Absy, Absy>();
            this.implMap = new Dictionary<Implementation, Implementation>();
            this.yieldingProcs = new HashSet<Procedure>();
        }

        public override Procedure VisitProcedure(Procedure node)
        {
            if (!civlTypeChecker.procToYieldingProc.ContainsKey(node))
                return node;
            if (!procMap.ContainsKey(node))
            {
                YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[node];

                if (layerNum > yieldingProc.upperLayer)
                {
                    if (yieldingProc is ActionProc actionProc)
                    {
                        // yielding procedure already transformed to atomic action
                        var action = actionProc.refinedAction;
                        if (action.layerRange.Contains(layerNum))
                            return action.layerToActionCopy[layerNum].proc;
                        else
                            return node;
                    }
                    else if (yieldingProc is SkipProc)
                    {
                        // (calls to) skip procedures do not completely disappear because of output variables
                        return procToSkipProcDummy[yieldingProc.proc];
                    }
                    else if (yieldingProc is MoverProc)
                    {
                        // mover procedure does not exist on this layer any more
                        return node;
                    }
                }

                Procedure proc = (Procedure) node.Clone();
                proc.Name = $"{node.Name}_{layerNum}";
                proc.InParams = this.VisitVariableSeq(node.InParams);
                proc.OutParams = this.VisitVariableSeq(node.OutParams);
                proc.Requires = this.VisitRequiresSeq(node.Requires);
                proc.Ensures = this.VisitEnsuresSeq(node.Ensures);
                if (yieldingProc is MoverProc moverProc && yieldingProc.upperLayer == layerNum)
                {
                    proc.Modifies = moverProc.modifiedGlobalVars.Select(g => Expr.Ident(g)).ToList();
                }
                else
                {
                    proc.Modifies = civlTypeChecker.sharedVariableIdentifiers;
                    yieldingProcs.Add(proc);
                }

                procMap[node] = proc;
            }

            return procMap[node];
        }

        public override List<Requires> VisitRequiresSeq(List<Requires> requiresSeq)
        {
            requiresSeq = base.VisitRequiresSeq(requiresSeq);
            requiresSeq.RemoveAll(req => req.Condition.Equals(Expr.True));
            return requiresSeq;
        }

        public override List<Ensures> VisitEnsuresSeq(List<Ensures> ensuresSeq)
        {
            ensuresSeq = base.VisitEnsuresSeq(ensuresSeq);
            ensuresSeq.RemoveAll(ens => ens.Condition.Equals(Expr.True));
            return ensuresSeq;
        }

        public override Requires VisitRequires(Requires node)
        {
            Requires requires = base.VisitRequires(node);
            if (node.Free)
                return requires;
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                requires.Condition = Expr.True;
            return requires;
        }

        public override Ensures VisitEnsures(Ensures node)
        {
            Ensures ensures = base.VisitEnsures(node);
            if (node.Free)
                return ensures;
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                ensures.Condition = Expr.True;
            return ensures;
        }

        public override Implementation VisitImplementation(Implementation impl)
        {
            if (!civlTypeChecker.procToYieldingProc.ContainsKey(impl.Proc))
                return impl;

            enclosingYieldingProc = civlTypeChecker.procToYieldingProc[impl.Proc];
            if (layerNum > enclosingYieldingProc.upperLayer)
                return impl;

            Implementation newImpl = base.VisitImplementation(impl);
            newImpl.Name = newImpl.Proc.Name;
            implMap[newImpl] = impl;
            return newImpl;
        }

        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            YieldCmd yieldCmd = base.VisitYieldCmd(node);
            absyMap[yieldCmd] = node;
            return yieldCmd;
        }

        public override Block VisitBlock(Block node)
        {
            Block block = base.VisitBlock(node);
            absyMap[block] = node;
            return block;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            AssertCmd assertCmd = (AssertCmd) base.VisitAssertCmd(node);
            if (!civlTypeChecker.absyToLayerNums[node].Contains(layerNum))
                assertCmd.Expr = Expr.True;
            return assertCmd;
        }

        public override Cmd VisitCallCmd(CallCmd call)
        {
            CallCmd newCall = (CallCmd) base.VisitCallCmd(call);
            newCall.Proc = VisitProcedure(newCall.Proc);

            if (newCall.IsAsync)
            {
                Debug.Assert(civlTypeChecker.procToYieldingProc.ContainsKey(call.Proc));
                YieldingProc yieldingProc = civlTypeChecker.procToYieldingProc[call.Proc];
                Debug.Assert(yieldingProc.IsLeftMover);
                if (yieldingProc.upperLayer < layerNum ||
                    (yieldingProc is MoverProc && yieldingProc.upperLayer == layerNum))
                {
                    newCall.IsAsync = false;
                }

                if (enclosingYieldingProc.upperLayer == layerNum && yieldingProc.upperLayer > layerNum)
                {
                    ActionProc actionProc = (ActionProc) yieldingProc;
                    newCall.Proc = actionProc.addPendingAsyncProc;
                    newCall.IsAsync = false;
                }
            }

            newCall.callee = newCall.Proc.Name;
            absyMap[newCall] = call;
            return newCall;
        }

        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            ParCallCmd parCallCmd = (ParCallCmd) base.VisitParCallCmd(node);
            absyMap[parCallCmd] = node;
            return parCallCmd;
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> visitedCmdSeq = base.VisitCmdSeq(cmdSeq);
            List<Cmd> newCmdSeq = new List<Cmd>();
            for (int i = 0; i < visitedCmdSeq.Count; i++)
            {
                Cmd originalCmd = cmdSeq[i];
                Cmd visitedCmd = visitedCmdSeq[i];

                if (originalCmd is CallCmd)
                {
                    ProcessCallCmd((CallCmd) originalCmd, (CallCmd) visitedCmd, newCmdSeq);
                }
                else if (originalCmd is ParCallCmd)
                {
                    ProcessParCallCmd((ParCallCmd) originalCmd, (ParCallCmd) visitedCmd, newCmdSeq);
                }
                else
                {
                    newCmdSeq.Add(visitedCmd);
                }
            }

            newCmdSeq.RemoveAll(cmd => (cmd is AssertCmd assertCmd && assertCmd.Expr.Equals(Expr.True)) ||
                                       (cmd is AssumeCmd assumeCmd && assumeCmd.Expr.Equals(Expr.True)));
            return newCmdSeq;
        }

        // We only have to check the gate of a called atomic action (via an assert) at the creation layer of the caller.
        // In all layers below we just establish invariants which do not require the gates to be checked and we can inject is as an assume.
        private void InjectGate(ActionProc calledActionProc, CallCmd callCmd, List<Cmd> newCmds)
        {
            if (calledActionProc.upperLayer >= layerNum) return;
            AtomicActionCopy atomicActionCopy = calledActionProc.refinedAction.layerToActionCopy[layerNum];
            if (atomicActionCopy.gate.Count == 0) return;

            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            for (int i = 0; i < calledActionProc.proc.InParams.Count; i++)
            {
                // Parameters come from the implementation that defines the atomic action
                map[atomicActionCopy.impl.InParams[i]] = callCmd.Ins[i];
            }

            Substitution subst = Substituter.SubstitutionFromHashtable(map);

            // Important: Do not remove CommentCmd!
            // It separates the injected gate from yield assertions in CollectAndDesugarYields.
            newCmds.Add(new CommentCmd("<<< injected gate"));
            foreach (AssertCmd assertCmd in atomicActionCopy.gate)
            {
                if (layerNum == enclosingYieldingProc.upperLayer)
                    newCmds.Add((AssertCmd) Substituter.Apply(subst, assertCmd));
                else
                    newCmds.Add(new AssumeCmd(assertCmd.tok, Substituter.Apply(subst, assertCmd.Expr)));
            }

            newCmds.Add(new CommentCmd("injected gate >>>"));
        }

        private void ProcessCallCmd(CallCmd originalCallCmd, CallCmd callCmd, List<Cmd> newCmds)
        {
            Procedure originalProc = originalCallCmd.Proc;

            if (civlTypeChecker.procToIntroductionProc.ContainsKey(originalProc))
            {
                if (!civlTypeChecker.CallExists(originalCallCmd, enclosingYieldingProc.upperLayer, layerNum))
                    return;
            }
            else if (civlTypeChecker.procToYieldingProc[originalProc] is ActionProc actionProc)
            {
                Debug.Assert(layerNum <= enclosingYieldingProc.upperLayer);
                InjectGate(actionProc, callCmd, newCmds);
            }

            newCmds.Add(callCmd);
        }

        private void ProcessParCallCmd(ParCallCmd originalParCallCmd, ParCallCmd parCallCmd, List<Cmd> newCmds)
        {
            int maxCalleeLayerNum = 0;
            foreach (CallCmd iter in originalParCallCmd.CallCmds)
            {
                int calleeLayerNum = civlTypeChecker.procToYieldingProc[iter.Proc].upperLayer;
                if (calleeLayerNum > maxCalleeLayerNum)
                    maxCalleeLayerNum = calleeLayerNum;
            }

            if (layerNum > maxCalleeLayerNum)
            {
                for (int i = 0; i < parCallCmd.CallCmds.Count; i++)
                {
                    ProcessCallCmd(originalParCallCmd.CallCmds[i], parCallCmd.CallCmds[i], newCmds);
                    absyMap[parCallCmd.CallCmds[i]] = originalParCallCmd;
                }
            }
            else
            {
                newCmds.Add(parCallCmd);
            }
        }

        public List<Declaration> Collect()
        {
            var decls = new List<Declaration>();
            decls.AddRange(procMap.Values);
            decls.AddRange(implMap.Keys);
            decls.AddRange(YieldingProcInstrumentation.TransformImplementations(
                civlTypeChecker,
                linearTypeChecker,
                layerNum,
                absyMap,
                implMap,
                yieldingProcs));
            return decls;
        }
    }
}
