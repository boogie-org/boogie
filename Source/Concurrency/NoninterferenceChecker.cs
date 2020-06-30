using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
    public static class NoninterferenceChecker
    {
        public static List<Declaration> CreateNoninterferenceCheckers(
            CivlTypeChecker civlTypeChecker,
            LinearTypeChecker linearTypeChecker,
            int layerNum,
            Dictionary<Absy, Absy> absyMap,
            DeclWithFormals decl,
            List<Variable> declLocalVariables)
        {
            Dictionary<string, Variable> domainNameToHoleVar = new Dictionary<string, Variable>();
            Dictionary<Variable, Variable> localVarMap = new Dictionary<Variable, Variable>();
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            List<Variable> locals = new List<Variable>();
            List<Variable> inputs = new List<Variable>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                var inParam = linearTypeChecker.LinearDomainInFormal(domainName);
                inputs.Add(inParam);
                domainNameToHoleVar[domainName] = inParam;
            }
            foreach (Variable local in declLocalVariables.Union(decl.InParams).Union(decl.OutParams))
            {
                var copy = CopyLocal(local);
                locals.Add(copy);
                localVarMap[local] = copy;
                map[local] = Expr.Ident(copy);
            }
            Dictionary<Variable, Expr> oldLocalMap = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Expr> assumeMap = new Dictionary<Variable, Expr>(map);
            foreach (Variable g in civlTypeChecker.GlobalVariables)
            {
                var copy = OldLocalLocal(g);
                locals.Add(copy);
                oldLocalMap[g] = Expr.Ident(copy);
                Formal f = OldGlobalFormal(g);
                inputs.Add(f);
                assumeMap[g] = Expr.Ident(f);
            }

            var linearPermissionInstrumentation = new LinearPermissionInstrumentation(civlTypeChecker, linearTypeChecker, layerNum, absyMap, domainNameToHoleVar, localVarMap);
            List<Tuple<List<Cmd>, List<PredicateCmd>>> yieldInfo = null;
            if (decl is Implementation impl)
            {
                yieldInfo = CollectYields(civlTypeChecker, absyMap, layerNum, impl).Select(kv => new Tuple<List<Cmd>, List<PredicateCmd>>(linearPermissionInstrumentation.DisjointnessAssumeCmds(kv.Key, false), kv.Value)).ToList();
            }
            else if (decl is Procedure proc)
            {
                yieldInfo = new List<Tuple<List<Cmd>, List<PredicateCmd>>>();
                if (civlTypeChecker.procToYieldInvariant.ContainsKey(proc))
                {
                    if (proc.Requires.Count > 0)
                    {
                        var disjointnessCmds = linearPermissionInstrumentation.ProcDisjointnessAssumeCmds(proc, true);
                        var yieldPredicates = proc.Requires.Select(requires =>
                            requires.Free
                                ? (PredicateCmd) new AssumeCmd(requires.tok, requires.Condition)
                                : (PredicateCmd) new AssertCmd(requires.tok, requires.Condition)).ToList();
                        yieldInfo.Add(new Tuple<List<Cmd>, List<PredicateCmd>>(disjointnessCmds, yieldPredicates));
                    }
                }
                else
                {
                    if (proc.Requires.Count > 0)
                    {
                        var entryDisjointnessCmds =
                            linearPermissionInstrumentation.ProcDisjointnessAssumeCmds(proc, true);
                        var entryYieldPredicates = proc.Requires.Select(requires =>
                            requires.Free
                                ? (PredicateCmd) new AssumeCmd(requires.tok, requires.Condition)
                                : (PredicateCmd) new AssertCmd(requires.tok, requires.Condition)).ToList();
                        yieldInfo.Add(
                            new Tuple<List<Cmd>, List<PredicateCmd>>(entryDisjointnessCmds, entryYieldPredicates));
                    }
                    if (proc.Ensures.Count > 0)
                    {
                        var exitDisjointnessCmds =
                            linearPermissionInstrumentation.ProcDisjointnessAssumeCmds(proc, false);
                        var exitYieldPredicates = proc.Ensures.Select(ensures =>
                            ensures.Free
                                ? (PredicateCmd) new AssumeCmd(ensures.tok, ensures.Condition)
                                : (PredicateCmd) new AssertCmd(ensures.tok, ensures.Condition)).ToList();
                        yieldInfo.Add(
                            new Tuple<List<Cmd>, List<PredicateCmd>>(exitDisjointnessCmds, exitYieldPredicates));
                    }
                }
            }
            else
            {
                Debug.Assert(false);
            }
            
            Substitution assumeSubst = Substituter.SubstitutionFromHashtable(assumeMap);
            Substitution oldSubst = Substituter.SubstitutionFromHashtable(oldLocalMap);
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            List<Block> noninterferenceCheckerBlocks = new List<Block>();
            List<String> labels = new List<String>();
            List<Block> labelTargets = new List<Block>();
            Block noninterferenceCheckerBlock = new Block(Token.NoToken, "exit", new List<Cmd>(), new ReturnCmd(Token.NoToken));
            labels.Add(noninterferenceCheckerBlock.Label);
            labelTargets.Add(noninterferenceCheckerBlock);
            noninterferenceCheckerBlocks.Add(noninterferenceCheckerBlock);
            int yieldCount = 0;
            foreach (var kv in yieldInfo)
            {
                var disjointnessCmds = kv.Item1;
                var yieldPredicates = kv.Item2;
                var newCmds = new List<Cmd>(disjointnessCmds);
                foreach (var predCmd in yieldPredicates)
                {
                    var newExpr = Substituter.ApplyReplacingOldExprs(assumeSubst, oldSubst, predCmd.Expr);
                    newCmds.Add(new AssumeCmd(Token.NoToken, newExpr));
                }

                foreach (var predCmd in yieldPredicates)
                {
                    if (predCmd is AssertCmd)
                    {
                        var newExpr = Substituter.ApplyReplacingOldExprs(subst, oldSubst, predCmd.Expr);
                        AssertCmd assertCmd = new AssertCmd(predCmd.tok, newExpr, predCmd.Attributes);
                        assertCmd.ErrorData = "Non-interference check failed";
                        newCmds.Add(assertCmd);
                    }
                }

                newCmds.Add(new AssumeCmd(Token.NoToken, Expr.False));
                noninterferenceCheckerBlock = new Block(Token.NoToken, "L" + yieldCount++, newCmds, new ReturnCmd(Token.NoToken));
                labels.Add(noninterferenceCheckerBlock.Label);
                labelTargets.Add(noninterferenceCheckerBlock);
                noninterferenceCheckerBlocks.Add(noninterferenceCheckerBlock);
            }

            noninterferenceCheckerBlocks.Insert(0,
                new Block(Token.NoToken, "enter", new List<Cmd>(), new GotoCmd(Token.NoToken, labels, labelTargets)));

            // Create the yield checker procedure
            var noninterferenceCheckerName = decl is Procedure ? $"NoninterferenceChecker_proc_{decl.Name}" : $"NoninterferenceChecker_impl_{decl.Name}";
            var noninterferenceCheckerProc = new Procedure(Token.NoToken, noninterferenceCheckerName, decl.TypeParameters, inputs,
                new List<Variable>(), new List<Requires>(), new List<IdentifierExpr>(), new List<Ensures>());
            CivlUtil.AddInlineAttribute(noninterferenceCheckerProc);

            // Create the yield checker implementation
            var noninterferenceCheckerImpl = new Implementation(Token.NoToken, noninterferenceCheckerName, decl.TypeParameters, inputs,
                new List<Variable>(), locals, noninterferenceCheckerBlocks);
            noninterferenceCheckerImpl.Proc = noninterferenceCheckerProc;
            CivlUtil.AddInlineAttribute(noninterferenceCheckerImpl);
            return new List<Declaration> {noninterferenceCheckerProc, noninterferenceCheckerImpl};
        }

        private static Dictionary<Absy, List<PredicateCmd>> CollectYields(CivlTypeChecker civlTypeChecker, Dictionary<Absy, Absy> absyMap, int layerNum, Implementation impl)
        {
            var allYieldPredicates = new Dictionary<Absy, List<PredicateCmd>>();
            List<PredicateCmd> yieldPredicates = new List<PredicateCmd>();
            foreach (Block b in impl.Blocks)
            {
                Absy absy = null;
                var originalBlock = (Block) absyMap[b];
                if (civlTypeChecker.yieldingLoops.ContainsKey(originalBlock) &&
                    civlTypeChecker.yieldingLoops[originalBlock].layers.Contains(layerNum))
                {
                    absy = b;
                }
                foreach (Cmd cmd in b.Cmds)
                {
                    if (absy != null)
                    {
                        if (cmd is PredicateCmd)
                        {
                            yieldPredicates.Add(cmd as PredicateCmd);
                        }
                        else
                        {
                            allYieldPredicates[absy] = yieldPredicates;
                            yieldPredicates = new List<PredicateCmd>();
                            absy = null;
                        }
                    }
                    if (cmd is YieldCmd ycmd)
                    {
                        absy = ycmd;
                    }
                }
                if (absy != null)
                {
                    allYieldPredicates[absy] = yieldPredicates;
                    yieldPredicates = new List<PredicateCmd>();
                }
            }
            return allYieldPredicates;
        }
        
        private static LocalVariable CopyLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
        }

        private static Formal OldGlobalFormal(Variable v)
        {
            return new Formal(Token.NoToken,
                new TypedIdent(Token.NoToken, $"civl_global_old_{v.Name}", v.TypedIdent.Type), true);
        }

        private static LocalVariable OldLocalLocal(Variable v)
        {
            return new LocalVariable(Token.NoToken,
                new TypedIdent(Token.NoToken, $"civl_local_old_{v.Name}", v.TypedIdent.Type));
        }
    }
}