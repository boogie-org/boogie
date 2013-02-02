using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    class ProcedureInfo
    {
        // containsYield is true iff there is an implementation that contains a yield statement
        public bool containsYield;
        // isThreadStart is true iff the procedure is labeled entrypoint or if there is an async call to the procedure
        public bool isThreadStart;
        // isAtomic is true if there are no yields transitively in any implementation
        public bool isAtomic;
        public Procedure yieldCheckerProc;
        public Implementation yieldCheckerImpl;
        public Procedure dummyAsyncTargetProc;
        public ProcedureInfo()
        {
            containsYield = false;
            isThreadStart = false;
            isAtomic = true;
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
                procNameToInfo[node.Name].isThreadStart = true;
                CreateYieldCheckerProcedure(node);
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
                procNameToInfo[node.Name].isThreadStart = true;
                CreateYieldCheckerProcedure(node.Proc);
            }
            return base.VisitImplementation(node);
        }
        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            if (QKeyValue.FindBoolAttribute(node.Attributes, "yield"))
            {
                procNameToInfo[currentImpl.Name].containsYield = true;
                procNameToInfo[currentImpl.Name].isAtomic = false;
                CreateYieldCheckerProcedure(currentImpl.Proc);
            }
            return base.VisitAssertCmd(node);
        }
        public override Cmd VisitCallCmd(CallCmd node)
        {
            if (!procNameToInfo.ContainsKey(node.Proc.Name))
            {
                procNameToInfo[node.Proc.Name] = new ProcedureInfo();
            }
            if (QKeyValue.FindBoolAttribute(node.Attributes, "async"))
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
            if (!QKeyValue.FindBoolAttribute(node.Attributes, "async") && !info.isAtomic)
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

        public OwickiGriesTransform(Program program)
        {
            this.program = program;
            procNameToInfo = AsyncAndYieldTraverser.Traverse(program);
            AtomicTraverser.Traverse(program, procNameToInfo);
            ogOldGlobalMap = new Hashtable();
            globalMods = new IdentifierExprSeq();
            bool workTodo = procNameToInfo.Values.Aggregate<ProcedureInfo, bool>(false, (b, info) => (b || !info.isAtomic || info.isThreadStart));
            if (workTodo)
            {
                foreach (Variable g in program.GlobalVariables())
                {
                    var oldg = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("og@global_old_{0}", g.Name), g.TypedIdent.Type));
                    ogOldGlobalMap[g] = new IdentifierExpr(Token.NoToken, oldg);
                    globalMods.Add(new IdentifierExpr(Token.NoToken, g));
                }
            }
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

        public void Transform()
        {
            foreach (var decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null) continue;
                if (procNameToInfo[impl.Name].isAtomic && !procNameToInfo[impl.Name].isThreadStart) continue;

                // Add free requires
                Expr freeRequiresExpr = Expr.True;
                foreach (Variable g in ogOldGlobalMap.Keys)
                {
                    freeRequiresExpr = Expr.And(freeRequiresExpr, Expr.Eq(new IdentifierExpr(Token.NoToken, g), (IdentifierExpr)ogOldGlobalMap[g]));
                }
                impl.Proc.Requires.Add(new Requires(true, freeRequiresExpr));

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
                if (procNameToInfo[impl.Name].isThreadStart && impl.Proc.Requires.Length > 0)
                {
                    foreach (Requires r in impl.Proc.Requires)
                    {
                        if (r.Free) continue;
                        cmds.Add(new AssertCmd(Token.NoToken, r.Condition));
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
                        PredicateCmd pcmd = b.Cmds[i] as PredicateCmd;
                        if (pcmd == null || QKeyValue.FindBoolAttribute(pcmd.Attributes, "yield"))
                        {
                            if (cmds.Length > 0)
                            {
                                DesugarYield(cmds, newCmds);
                                yields.Add(cmds);
                                cmds = new CmdSeq();
                            }
                            insideYield = (pcmd != null);
                        }
                        if (insideYield)
                        {
                            cmds.Add(pcmd);
                        }

                        CallCmd callCmd = b.Cmds[i] as CallCmd;
                        if (callCmd != null)
                        {
                            if (QKeyValue.FindBoolAttribute(callCmd.Attributes, "async"))
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
                            newCmds.Add(b.Cmds[i]);
                        }
                    }
                    if (cmds.Length > 0)
                    {
                        DesugarYield(cmds, newCmds);
                        yields.Add(cmds);
                        cmds = new CmdSeq();
                    } 
                    if (b.TransferCmd is ReturnCmd)
                    {
                        AddCallsToYieldCheckers(newCmds);
                    }
                    b.Cmds = newCmds;
                }

                if (!procNameToInfo[impl.Name].containsYield && !procNameToInfo[impl.Name].isThreadStart) continue;

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
                            newCmds.Add(new AssertCmd(Token.NoToken, newExpr));
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
                var yieldCheckerImpl = new Implementation(Token.NoToken, procNameToInfo[impl.Name].yieldCheckerProc.Name, impl.TypeParameters, new VariableSeq(), new VariableSeq(), locals, yieldCheckerBlocks);
                yieldCheckerImpl.Proc = procNameToInfo[impl.Name].yieldCheckerProc;
                yieldCheckerImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                procNameToInfo[impl.Name].yieldCheckerImpl = yieldCheckerImpl;
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
