using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
    class ProcedureInfo
    {
        // containsYield is true iff there is an implementation that contains a yield statement
        public bool containsYield;
        // isThreadStart is true iff there is an async call to the procedure
        public bool isThreadStart;
        // isEntrypoint is true iff the procedure is an entrypoint
        public bool isEntrypoint;
        // isAtomic is true if there are no yields transitively in any implementation
        public bool isAtomic;
        // inParallelCall is true iff this procedure is involved in some parallel call
        public bool inParallelCall;
        public Procedure yieldCheckerProc;
        public Implementation yieldCheckerImpl;
        public Procedure dummyAsyncTargetProc;
        public ProcedureInfo()
        {
            containsYield = false;
            isThreadStart = false;
            isAtomic = true;
            inParallelCall = false;
            yieldCheckerProc = null;
            yieldCheckerImpl = null;
            dummyAsyncTargetProc = null;
        }
    }

    class AsyncAndYieldTraverser : StandardVisitor
    {
        Dictionary<string, ProcedureInfo> procNameToInfo = new Dictionary<string, ProcedureInfo>();
        Implementation currentImpl = null;
        public static Dictionary<string, ProcedureInfo> Traverse(Program program)
        {
            AsyncAndYieldTraverser traverser = new AsyncAndYieldTraverser();
            traverser.VisitProgram(program);
            return traverser.procNameToInfo;
        }
        public override Procedure VisitProcedure(Procedure node)
        {
            if (!procNameToInfo.ContainsKey(node.Name))
            {
                procNameToInfo[node.Name] = new ProcedureInfo();
            }
            if (QKeyValue.FindBoolAttribute(node.Attributes, "entrypoint"))
            {
                procNameToInfo[node.Name].isEntrypoint = true;
            }
            if (QKeyValue.FindBoolAttribute(node.Attributes, "yields"))
            {
                procNameToInfo[node.Name].isAtomic = false;
            }
            return base.VisitProcedure(node);
        }
        public override Implementation VisitImplementation(Implementation node)
        {
            currentImpl = node;
            if (!procNameToInfo.ContainsKey(node.Name))
            {
                procNameToInfo[node.Name] = new ProcedureInfo();
            }
            if (QKeyValue.FindBoolAttribute(node.Attributes, "entrypoint"))
            {
                procNameToInfo[node.Name].isEntrypoint = true;
            }
            return base.VisitImplementation(node);
        }
        public override YieldCmd VisitYieldCmd(YieldCmd node)
        {
            procNameToInfo[currentImpl.Name].containsYield = true;
            procNameToInfo[currentImpl.Name].isAtomic = false;
            CreateYieldCheckerProcedure(currentImpl.Proc);
            return base.VisitYieldCmd(node);
        }
        public override Cmd VisitCallCmd(CallCmd node)
        {
            if (!procNameToInfo.ContainsKey(node.Proc.Name))
            {
                procNameToInfo[node.Proc.Name] = new ProcedureInfo();
            }
            if (node.IsAsync)
            {
                procNameToInfo[node.Proc.Name].isThreadStart = true;
                CreateYieldCheckerProcedure(node.Proc);
                if (procNameToInfo[node.Proc.Name].dummyAsyncTargetProc == null)
                {
                    var dummyAsyncTargetName = string.Format("DummyAsyncTarget_{0}", node.Proc.Name);
                    var dummyAsyncTargetProc = new Procedure(Token.NoToken, dummyAsyncTargetName, node.Proc.TypeParameters, node.Proc.InParams, node.Proc.OutParams, node.Proc.Requires, new IdentifierExprSeq(), new EnsuresSeq());
                    procNameToInfo[node.Proc.Name].dummyAsyncTargetProc = dummyAsyncTargetProc;
                }
            }
            if (node.InParallelWith != null)
            {
                CallCmd iter = node;
                while (iter != null)
                {
                    if (!procNameToInfo.ContainsKey(iter.Proc.Name))
                    {
                        procNameToInfo[iter.Proc.Name] = new ProcedureInfo();
                    }
                    procNameToInfo[iter.Proc.Name].isThreadStart = true;
                    CreateYieldCheckerProcedure(iter.Proc);
                    procNameToInfo[iter.Proc.Name].inParallelCall = true;
                    iter = iter.InParallelWith;
                }
            }
            return base.VisitCallCmd(node);
        }
        private void CreateYieldCheckerProcedure(Procedure proc)
        {
            if (procNameToInfo[proc.Name].yieldCheckerProc != null) return;
            var yieldCheckerName = string.Format("YieldChecker_{0}", proc.Name);
            var yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, proc.TypeParameters, new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());
            yieldCheckerProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
            procNameToInfo[proc.Name].yieldCheckerProc = yieldCheckerProc;
        }
    }

    class AtomicTraverser : StandardVisitor
    {
        Implementation currentImpl;
        static Dictionary<string, ProcedureInfo> procNameToInfo;
        static bool moreProcessingRequired;
        public static void Traverse(Program program, Dictionary<string, ProcedureInfo> procNameToInfo)
        {
            AtomicTraverser.procNameToInfo = procNameToInfo;
            do
            {
                moreProcessingRequired = false;
                AtomicTraverser traverser = new AtomicTraverser();
                traverser.VisitProgram(program);
            } while (moreProcessingRequired);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            if (!procNameToInfo[node.Name].isAtomic)
                return node;
            currentImpl = node;
            return base.VisitImplementation(node);
        }

        public override Cmd VisitCallCmd(CallCmd node)
        {
            ProcedureInfo info = procNameToInfo[node.callee];
            if (!node.IsAsync && !info.isAtomic)
            {
                procNameToInfo[currentImpl.Name].isAtomic = false;
                moreProcessingRequired = true;
            }
            return base.VisitCallCmd(node);
        }
    }

    public class OwickiGriesTransform
    {
        Dictionary<string, ProcedureInfo> procNameToInfo;
        IdentifierExprSeq globalMods;
        Hashtable ogOldGlobalMap;
        Program program;
        Dictionary<string, Procedure> parallelCallDesugarings; 

        public OwickiGriesTransform(Program program)
        {
            this.program = program;
            procNameToInfo = AsyncAndYieldTraverser.Traverse(program);
            AtomicTraverser.Traverse(program, procNameToInfo);
            ogOldGlobalMap = new Hashtable();
            globalMods = new IdentifierExprSeq();
            foreach (Variable g in program.GlobalVariables())
            {
                var oldg = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og@global_old_{0}", g.Name), g.TypedIdent.Type));
                ogOldGlobalMap[g] = new IdentifierExpr(Token.NoToken, oldg);
                globalMods.Add(new IdentifierExpr(Token.NoToken, g));
            }
            parallelCallDesugarings = new Dictionary<string, Procedure>();
        }

        private void AddCallsToYieldCheckers(CmdSeq newCmds)
        {
            foreach (ProcedureInfo info in procNameToInfo.Values)
            {
                if (info.yieldCheckerProc != null)
                {
                    CallCmd yieldCallCmd = new CallCmd(Token.NoToken, info.yieldCheckerProc.Name, new ExprSeq(), new IdentifierExprSeq());
                    yieldCallCmd.Proc = info.yieldCheckerProc;
                    newCmds.Add(yieldCallCmd);
                }
            }
        }

        private void AddUpdatesToOldGlobalVars(CmdSeq newCmds)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (Variable g in ogOldGlobalMap.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, (IdentifierExpr)ogOldGlobalMap[g]));
                rhss.Add(new IdentifierExpr(Token.NoToken, g));
            }
            newCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
        }

        private void DesugarYield(CmdSeq cmds, CmdSeq newCmds)
        {
            AddCallsToYieldCheckers(newCmds);

            newCmds.Add(new HavocCmd(Token.NoToken, globalMods));

            AddUpdatesToOldGlobalVars(newCmds);

            for (int j = 0; j < cmds.Length; j++)
            {
                PredicateCmd predCmd = (PredicateCmd)cmds[j];
                newCmds.Add(new AssumeCmd(Token.NoToken, predCmd.Expr));
            }
        }

        public Procedure DesugarParallelCallCmd(CallCmd callCmd, out List<Expr> ins, out List<IdentifierExpr> outs)
        {
            List<string> parallelCalleeNames = new List<string>();
            CallCmd iter = callCmd;
            ins = new List<Expr>();
            outs = new List<IdentifierExpr>();
            while (iter != null)
            {
                parallelCalleeNames.Add(iter.Proc.Name);
                ins.AddRange(iter.Ins);
                outs.AddRange(iter.Outs);
                iter = iter.InParallelWith;
            }
            parallelCalleeNames.Sort();
            string procName = "og";
            foreach (string calleeName in parallelCalleeNames)
            {
                procName = procName + "@" + calleeName;
            }
            if (parallelCallDesugarings.ContainsKey(procName))
                return parallelCallDesugarings[procName];

            VariableSeq inParams = new VariableSeq();
            VariableSeq outParams = new VariableSeq();
            RequiresSeq requiresSeq = new RequiresSeq();
            EnsuresSeq ensuresSeq = new EnsuresSeq();
            IdentifierExprSeq ieSeq = new IdentifierExprSeq();
            int count = 0;
            while (callCmd != null)
            {
                Hashtable map = new Hashtable();
                foreach (Variable x in callCmd.Proc.InParams)
                {
                    Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "og@" + count + x.Name, x.TypedIdent.Type), true);
                    inParams.Add(y);
                    map[x] = new IdentifierExpr(Token.NoToken, y);
                }
                foreach (Variable x in callCmd.Proc.OutParams)
                {
                    Variable y = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "og@" + count + x.Name, x.TypedIdent.Type), false);
                    outParams.Add(y);
                    map[x] = new IdentifierExpr(Token.NoToken, y);
                }
                Contract.Assume(callCmd.Proc.TypeParameters.Length == 0);
                Substitution subst = Substituter.SubstitutionFromHashtable(map);
                foreach (Requires req in callCmd.Proc.Requires)
                {
                    requiresSeq.Add(new Requires(req.Free, Substituter.Apply(subst, req.Condition)));
                }
                foreach (IdentifierExpr ie in callCmd.Proc.Modifies)
                {
                    ieSeq.Add(ie);
                }
                foreach (Ensures ens in callCmd.Proc.Ensures)
                {
                    ensuresSeq.Add(new Ensures(ens.Free, Substituter.Apply(subst, ens.Condition)));
                } 
                count++;
                callCmd = callCmd.InParallelWith;
            }

            Procedure proc = new Procedure(Token.NoToken, procName, new TypeVariableSeq(), inParams, outParams, requiresSeq, ieSeq, ensuresSeq);
            parallelCallDesugarings[procName] = proc;
            return proc;
        }

        public void Transform()
        {
            foreach (var decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null) continue;
                ProcedureInfo info = procNameToInfo[impl.Name];

                // Add free requires
                if (!info.isAtomic || info.isEntrypoint || info.isThreadStart)
                {
                    Expr freeRequiresExpr = Expr.True;
                    foreach (Variable g in ogOldGlobalMap.Keys)
                    {
                        freeRequiresExpr = Expr.And(freeRequiresExpr, Expr.Eq(new IdentifierExpr(Token.NoToken, g), (IdentifierExpr)ogOldGlobalMap[g]));
                    }
                    impl.Proc.Requires.Add(new Requires(true, freeRequiresExpr));
                }

                // Create substitution maps
                Hashtable map = new Hashtable();
                VariableSeq locals = new VariableSeq();
                for (int i = 0; i < impl.Proc.InParams.Length; i++)
                {
                    Variable inParam = impl.Proc.InParams[i];
                    var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type));
                    locals.Add(copy);
                    map[impl.InParams[i]] = new IdentifierExpr(Token.NoToken, copy);
                }
                for (int i = 0; i < impl.Proc.OutParams.Length; i++)
                {
                    Variable outParam = impl.Proc.OutParams[i];
                    var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, outParam.Name, outParam.TypedIdent.Type), outParam.Attributes);
                    locals.Add(copy);
                    map[impl.OutParams[i]] = new IdentifierExpr(Token.NoToken, copy);
                }
                foreach (Variable local in impl.LocVars)
                {
                    var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, local.Name, local.TypedIdent.Type), local.Attributes);
                    locals.Add(copy);
                    map[local] = new IdentifierExpr(Token.NoToken, copy);
                }
                Hashtable assumeMap = new Hashtable(map);
                foreach (var global in ogOldGlobalMap.Keys)
                {
                    assumeMap[global] = ogOldGlobalMap[global];
                }

                Hashtable ogOldLocalMap = new Hashtable();
                foreach (var g in program.GlobalVariables())
                {
                    var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og@local_old_{0}", g.Name), g.TypedIdent.Type));
                    locals.Add(copy);
                    ogOldLocalMap[g] = new IdentifierExpr(Token.NoToken, copy);
                }

                // Collect the yield predicates and desugar yields
                HashSet<CmdSeq> yields = new HashSet<CmdSeq>();
                CmdSeq cmds = new CmdSeq();
                if (info.isThreadStart && impl.Proc.Requires.Length > 0)
                {
                    foreach (Requires r in impl.Proc.Requires)
                    {
                        if (r.Free) continue;
                        cmds.Add(new AssertCmd(r.tok, r.Condition));
                    }
                    yields.Add(cmds);
                    cmds = new CmdSeq();
                }
                if (info.inParallelCall && impl.Proc.Ensures.Length > 0)
                {
                    foreach (Ensures e in impl.Proc.Ensures)
                    {
                        if (e.Free) continue;
                        cmds.Add(new AssertCmd(e.tok, e.Condition));
                    }
                    yields.Add(cmds);
                    cmds = new CmdSeq();
                }
                foreach (Block b in impl.Blocks)
                {
                    bool insideYield = false;
                    CmdSeq newCmds = new CmdSeq();
                    for (int i = 0; i < b.Cmds.Length; i++)
                    {
                        Cmd cmd = b.Cmds[i];
                        if (cmd is YieldCmd)
                        {
                            insideYield = true;
                            continue;
                        }
                        if (insideYield)
                        {
                            PredicateCmd pcmd = cmd as PredicateCmd;
                            if (pcmd == null)
                            {
                                DesugarYield(cmds, newCmds);
                                if (cmds.Length > 0)
                                {
                                    yields.Add(cmds);
                                    cmds = new CmdSeq();
                                }
                                insideYield = false;
                            }
                            else
                            {
                                cmds.Add(pcmd);
                            }
                        }
                        CallCmd callCmd = cmd as CallCmd;
                        if (callCmd != null)
                        {
                            if (callCmd.InParallelWith != null)
                            {
                                List<Expr> ins;
                                List<IdentifierExpr> outs;
                                Procedure dummyParallelCallDesugaring = DesugarParallelCallCmd(callCmd, out ins, out outs);
                                CallCmd dummyCallCmd = new CallCmd(Token.NoToken, dummyParallelCallDesugaring.Name, ins, outs);
                                dummyCallCmd.Proc = dummyParallelCallDesugaring;
                                newCmds.Add(dummyCallCmd);
                            }
                            else if (callCmd.IsAsync)
                            {
                                var dummyAsyncTargetProc = procNameToInfo[callCmd.callee].dummyAsyncTargetProc;
                                CallCmd dummyCallCmd = new CallCmd(Token.NoToken, dummyAsyncTargetProc.Name, callCmd.Ins, callCmd.Outs);
                                dummyCallCmd.Proc = dummyAsyncTargetProc;
                                newCmds.Add(dummyCallCmd);
                            }
                            else if (procNameToInfo[callCmd.callee].isAtomic)
                            {
                                newCmds.Add(callCmd);
                            }
                            else
                            {
                                AddCallsToYieldCheckers(newCmds);
                                newCmds.Add(callCmd);
                                AddUpdatesToOldGlobalVars(newCmds);
                            }
                        }
                        else
                        {
                            newCmds.Add(cmd);
                        }
                    }
                    if (insideYield)
                    {
                        DesugarYield(cmds, newCmds);
                        if (cmds.Length > 0)
                        {
                            yields.Add(cmds);
                            cmds = new CmdSeq();
                        }
                    } 
                    if (b.TransferCmd is ReturnCmd && (!info.isAtomic || info.isEntrypoint || info.isThreadStart))
                    {
                        AddCallsToYieldCheckers(newCmds);
                    }
                    b.Cmds = newCmds;
                }

                if (!info.isAtomic)
                {
                    // Loops
                    impl.PruneUnreachableBlocks();
                    impl.ComputePredecessorsForBlocks();
                    GraphUtil.Graph<Block> g = Program.GraphFromImpl(impl);
                    g.ComputeLoops();
                    if (g.Reducible)
                    {
                        foreach (Block header in g.Headers)
                        {
                            foreach (Block pred in header.Predecessors)
                            {
                                AddCallsToYieldCheckers(pred.Cmds);
                                AddUpdatesToOldGlobalVars(pred.Cmds);
                            }
                            CmdSeq newCmds = new CmdSeq();
                            foreach (Variable v in ogOldGlobalMap.Keys)
                            {
                                newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Binary(BinaryOperator.Opcode.Eq, new IdentifierExpr(Token.NoToken, v), (IdentifierExpr)ogOldGlobalMap[v])));
                            }
                            newCmds.AddRange(header.Cmds);
                            header.Cmds = newCmds;
                        }
                    }
                }

                if (!info.containsYield && !info.isThreadStart) continue;

                // Create the body of the yield checker procedure
                Substitution assumeSubst = Substituter.SubstitutionFromHashtable(assumeMap);
                Substitution oldSubst = Substituter.SubstitutionFromHashtable(ogOldLocalMap);
                Substitution subst = Substituter.SubstitutionFromHashtable(map);
                List<Block> yieldCheckerBlocks = new List<Block>();
                StringSeq labels = new StringSeq();
                BlockSeq labelTargets = new BlockSeq();
                Block yieldCheckerBlock = new Block(Token.NoToken, "exit", new CmdSeq(), new ReturnCmd(Token.NoToken));
                labels.Add(yieldCheckerBlock.Label);
                labelTargets.Add(yieldCheckerBlock);
                yieldCheckerBlocks.Add(yieldCheckerBlock);
                int yieldCount = 0;
                foreach (CmdSeq cs in yields)
                {
                    CmdSeq newCmds = new CmdSeq();
                    foreach (Cmd cmd in cs)
                    {
                        PredicateCmd predCmd = (PredicateCmd)cmd;
                        newCmds.Add(new AssumeCmd(Token.NoToken, Substituter.ApplyReplacingOldExprs(assumeSubst, oldSubst, predCmd.Expr)));
                    }
                    foreach (Cmd cmd in cs)
                    {
                        PredicateCmd predCmd = (PredicateCmd)cmd;
                        var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldSubst, predCmd.Expr);
                        if (predCmd is AssertCmd)
                            newCmds.Add(new AssertCmd(predCmd.tok, newExpr));
                        else
                            newCmds.Add(new AssumeCmd(Token.NoToken, newExpr));
                    }
                    newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                    yieldCheckerBlock = new Block(Token.NoToken, "L" + yieldCount++, newCmds, new ReturnCmd(Token.NoToken));
                    labels.Add(yieldCheckerBlock.Label);
                    labelTargets.Add(yieldCheckerBlock);
                    yieldCheckerBlocks.Add(yieldCheckerBlock); 
                }
                yieldCheckerBlocks.Insert(0, new Block(Token.NoToken, "enter", new CmdSeq(), new GotoCmd(Token.NoToken, labels, labelTargets)));
                
                // Create the yield checker implementation
                var yieldCheckerImpl = new Implementation(Token.NoToken, info.yieldCheckerProc.Name, impl.TypeParameters, new VariableSeq(), new VariableSeq(), locals, yieldCheckerBlocks);
                yieldCheckerImpl.Proc = info.yieldCheckerProc;
                yieldCheckerImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                info.yieldCheckerImpl = yieldCheckerImpl;
            }

            foreach (Variable v in ogOldGlobalMap.Keys)
            {
                IdentifierExpr ie = (IdentifierExpr) ogOldGlobalMap[v];
                program.TopLevelDeclarations.Add(ie.Decl);
            }
            foreach (ProcedureInfo info in procNameToInfo.Values)
            {
                if (info.yieldCheckerProc != null)
                {
                    Debug.Assert(info.yieldCheckerImpl != null);
                    program.TopLevelDeclarations.Add(info.yieldCheckerProc);
                    program.TopLevelDeclarations.Add(info.yieldCheckerImpl);
                }
                if (info.dummyAsyncTargetProc != null)
                {
                    program.TopLevelDeclarations.Add(info.dummyAsyncTargetProc);
                }
            }
        }
    }
}
