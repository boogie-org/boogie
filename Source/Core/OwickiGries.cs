using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Boogie
{
    class ProcedureInfo
    {
        public bool hasImplementation;
        public bool isAtomic;
        public bool containsYield;
        public bool isThreadStart;
        public Procedure yieldCheckerProc;
        public Implementation yieldCheckerImpl;
        public Procedure dummyAsyncTargetProc;
        public ProcedureInfo()
        {
            hasImplementation = false;
            isAtomic = true;
            containsYield = false;
            isThreadStart = false;
            yieldCheckerProc = null;
            yieldCheckerImpl = null;
            dummyAsyncTargetProc = null;
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
            if (!info.isAtomic)
            {
                procNameToInfo[currentImpl.Name].isAtomic = false;
                moreProcessingRequired = true;
            }
            return base.VisitCallCmd(node);
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
            }
            if (QKeyValue.FindBoolAttribute(node.Attributes, "yields"))
            {
                procNameToInfo[node.Name].containsYield = true;
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
            procNameToInfo[node.Name].hasImplementation = true;
            if (QKeyValue.FindBoolAttribute(node.Attributes, "entrypoint"))
            {
                procNameToInfo[node.Name].isThreadStart = true;
            }
            return base.VisitImplementation(node);
        }
        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            if (QKeyValue.FindBoolAttribute(node.Attributes, "yield") && !procNameToInfo[currentImpl.Name].containsYield)
            {
                procNameToInfo[currentImpl.Name].containsYield = true;
                procNameToInfo[currentImpl.Name].isAtomic = false;
                var yieldCheckerName = string.Format("YieldChecker_{0}", currentImpl.Name);
                var yieldCheckerProc = new Procedure(Token.NoToken, yieldCheckerName, currentImpl.TypeParameters, new VariableSeq(), new VariableSeq(), new RequiresSeq(), new IdentifierExprSeq(), new EnsuresSeq());
                yieldCheckerProc.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                procNameToInfo[currentImpl.Name].yieldCheckerProc = yieldCheckerProc;
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
                if (procNameToInfo[node.Proc.Name].dummyAsyncTargetProc == null)
                {
                    var dummyAsyncTargetName = string.Format("DummyAsyncTarget_{0}", node.Proc.Name);
                    var dummyAsyncTargetProc = new Procedure(Token.NoToken, dummyAsyncTargetName, node.Proc.TypeParameters, node.Proc.InParams, node.Proc.OutParams, node.Proc.Requires, new IdentifierExprSeq(), new EnsuresSeq());
                    procNameToInfo[node.Proc.Name].dummyAsyncTargetProc = dummyAsyncTargetProc;
                }
            }
            return base.VisitCallCmd(node);
        }
    }

    class OwickiGriesTransform
    {
        Dictionary<string, ProcedureInfo> procNameToInfo;
        IdentifierExprSeq globalMods;
        Hashtable globalMap;

        public OwickiGriesTransform(Program program)
        {
            procNameToInfo = AsyncAndYieldTraverser.Traverse(program);
            AtomicTraverser.Traverse(program, procNameToInfo);
            globalMap = new Hashtable();
            globalMods = new IdentifierExprSeq();
            foreach (Variable g in program.GlobalVariables())
            {
                var oldg = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("old_{0}", g.Name), g.TypedIdent.Type));
                globalMap[g] = new IdentifierExpr(Token.NoToken, oldg);
                globalMods.Add(new IdentifierExpr(Token.NoToken, g));
            }
        }

        private void AddCallsToYieldCheckers(CmdSeq newCmds)
        {
            foreach (ProcedureInfo info in procNameToInfo.Values)
            {
                if (info.containsYield)
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
            foreach (Variable g in globalMap.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, (IdentifierExpr)globalMap[g]));
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

        public void Transform(Program program)
        {
            foreach (var decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null) continue;
                if (procNameToInfo[impl.Name].isAtomic) continue;

                // Add free requires
                Expr freeRequiresExpr = Expr.True;
                foreach (Variable g in globalMap.Keys)
                {
                    freeRequiresExpr = Expr.And(freeRequiresExpr, Expr.Eq(new IdentifierExpr(Token.NoToken, g), (IdentifierExpr)globalMap[g]));
                }
                impl.Proc.Requires.Add(new Requires(true, freeRequiresExpr));

                // Create substitution maps
                Hashtable map = new Hashtable();
                VariableSeq locals = new VariableSeq();
                foreach (Variable inParam in impl.Proc.InParams)
                {
                    var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, inParam.Name, inParam.TypedIdent.Type));
                    locals.Add(copy);
                    map[inParam] = new IdentifierExpr(Token.NoToken, copy);
                }
                foreach (Variable outParam in impl.Proc.OutParams)
                {
                    var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, outParam.Name, outParam.TypedIdent.Type), outParam.Attributes);
                    locals.Add(copy);
                    map[outParam] = new IdentifierExpr(Token.NoToken, copy);
                }
                foreach (Variable local in impl.LocVars)
                {
                    var copy = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, local.Name, local.TypedIdent.Type), local.Attributes);
                    locals.Add(copy);
                    map[local] = new IdentifierExpr(Token.NoToken, copy);
                }
                Hashtable oldMap = new Hashtable(map);
                foreach (var global in globalMap.Keys)
                {
                    oldMap[global] = globalMap[global];
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
                    if (b.TransferCmd is ReturnCmd)
                    {
                        AddCallsToYieldCheckers(newCmds);
                    }
                    else if (cmds.Length > 0)
                    {
                        DesugarYield(cmds, newCmds);
                        yields.Add(cmds);
                        cmds = new CmdSeq();
                    }
                    b.Cmds = newCmds;
                }

                if (!procNameToInfo[impl.Name].containsYield) continue;

                // Create the body of the yield checker procedure
                Substitution oldSubst = Substituter.SubstitutionFromHashtable(oldMap);
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
                        newCmds.Add(new AssumeCmd(Token.NoToken, Substituter.Apply(oldSubst, predCmd.Expr)));
                    }
                    foreach (Cmd cmd in cs)
                    {
                        PredicateCmd predCmd = (PredicateCmd)cmd;
                        var newExpr = Substituter.Apply(subst, predCmd.Expr);
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
                IdentifierExprSeq ieSeq = new IdentifierExprSeq();
                foreach (Variable local in locals)
                {
                    if (QKeyValue.FindStringAttribute(local.Attributes, "linear") != null)
                    {
                        ieSeq.Add(new IdentifierExpr(Token.NoToken, local));
                    }
                }
                CmdSeq initCmds;
                if (ieSeq.Length == 0)
                {
                    initCmds = new CmdSeq();
                }
                else
                {
                    initCmds = new CmdSeq(new HavocCmd(Token.NoToken, ieSeq));
                }

                yieldCheckerBlocks.Insert(0, new Block(Token.NoToken, "enter", initCmds, new GotoCmd(Token.NoToken, labels, labelTargets)));
                
                // Create the yield checker implementation
                var yieldCheckerImpl = new Implementation(Token.NoToken, procNameToInfo[impl.Name].yieldCheckerProc.Name, impl.TypeParameters, new VariableSeq(), new VariableSeq(), locals, yieldCheckerBlocks);
                yieldCheckerImpl.Proc = procNameToInfo[impl.Name].yieldCheckerProc;
                yieldCheckerImpl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
                procNameToInfo[impl.Name].yieldCheckerImpl = yieldCheckerImpl;
            }

            foreach (Variable v in globalMap.Keys)
            {
                IdentifierExpr ie = (IdentifierExpr) globalMap[v];
                program.TopLevelDeclarations.Add(ie.Decl);
            }
            foreach (ProcedureInfo info in procNameToInfo.Values)
            {
                if (info.containsYield)
                {
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
