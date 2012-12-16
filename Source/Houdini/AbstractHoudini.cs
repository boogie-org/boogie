using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Outcome = VC.VCGen.Outcome;
using Bpl = Microsoft.Boogie;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie.Houdini {

    public class AbstractHoudini
    {
        // Input Program
        Program program;
        // Impl -> VC
        Dictionary<string, VCExpr> impl2VC;
        // Impl -> Vars at end of the impl
        Dictionary<string, List<VCExpr>> impl2EndStateVars;
        // Impl -> (callee,summary pred)
        Dictionary<string, List<Tuple<string, bool, VCExprNAry>>> impl2CalleeSummaries;
        // pointer to summary class
        ISummaryElement summaryClass;
        // impl -> summary
        Dictionary<string, ISummaryElement> impl2Summary;
        // name -> impl
        Dictionary<string, Implementation> name2Impl;
        // Use Bilateral algorithm
        public static bool UseBilateralAlgo = true;

        public static readonly string summaryPredSuffix = "SummaryPred";

        // Essentials: VCGen, Prover, and reporter
        VCGen vcgen;
        ProverInterface prover;
        AbstractHoudiniErrorReporter reporter;

        // Stats
        TimeSpan proverTime;
        int numProverQueries;

        // Produce witness for correctness: can be set programmatically
        public static string WitnessFile = "absHoudiniWitness.bpl";

        public AbstractHoudini(Program program)
        {
            this.program = program;
            this.impl2VC = new Dictionary<string, VCExpr>();
            this.impl2EndStateVars = new Dictionary<string, List<VCExpr>>();
            this.impl2CalleeSummaries = new Dictionary<string, List<Tuple<string, bool, VCExprNAry>>>();
            this.impl2Summary = new Dictionary<string, ISummaryElement>();
            this.name2Impl = SimpleUtil.nameImplMapping(program);

            this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
            this.prover = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime);
            this.reporter = new AbstractHoudiniErrorReporter();

            this.proverTime = TimeSpan.Zero;
            this.numProverQueries = 0;

            if (CommandLineOptions.Clo.AbstractHoudini == "0")
                UseBilateralAlgo = false;
        }

        public void computeSummaries(ISummaryElement summaryClass)
        {
            this.summaryClass = summaryClass;

            name2Impl.Values.Iter(attachEnsures);

            program.TopLevelDeclarations
                .OfType<Implementation>()
                .Iter(impl => impl2Summary.Add(impl.Name, summaryClass.GetFlaseSummary(program, impl)));

            // Build call graph
            var Succ = new Dictionary<Implementation, HashSet<Implementation>>();
            var Pred = new Dictionary<Implementation, HashSet<Implementation>>();
            name2Impl.Values.Iter(impl => Succ.Add(impl, new HashSet<Implementation>()));
            name2Impl.Values.Iter(impl => Pred.Add(impl, new HashSet<Implementation>()));

            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                foreach (var blk in impl.Blocks)
                {
                    foreach (var cmd in blk.Cmds.OfType<CallCmd>())
                    {
                        if (!name2Impl.ContainsKey(cmd.callee)) continue;
                        Succ[impl].Add(name2Impl[cmd.callee]);
                        Pred[name2Impl[cmd.callee]].Add(impl);
                    }
                }
            }

            // Build SCC
            var sccs = new StronglyConnectedComponents<Implementation>(name2Impl.Values,
                new Adjacency<Implementation>(n => Pred[n]),
                new Adjacency<Implementation>(n => Succ[n]));
            sccs.Compute();

            // impl -> priority
            var impl2Priority = new Dictionary<string, int>();
            int p = 0;
            foreach (var scc in sccs)
            {
                foreach (var impl in scc)
                {
                    impl2Priority.Add(impl.Name, p);
                    p++;
                }
            }


            Inline();

            #region Witness generation setup
            // Create a copy of the program
            var copy = new Dictionary<string, Implementation>();
            if (WitnessFile != null)
            {
                foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
                {
                    var nimpl = new Implementation(Token.NoToken, impl.Name, impl.TypeParameters,
                        impl.InParams, impl.OutParams, new VariableSeq(impl.LocVars), new List<Block>());
                    foreach (var blk in impl.Blocks)
                    {
                        var cd = new CodeCopier();
                        nimpl.Blocks.Add(new Block(Token.NoToken, blk.Label,
                            cd.CopyCmdSeq(blk.Cmds), cd.CopyTransferCmd(blk.TransferCmd)));
                    }

                    copy.Add(impl.Name, nimpl);
                }
            }
            #endregion

            // Turn off subsumption. Why? Because then I see multiple occurences of the
            // attached ensures in the VC
            CommandLineOptions.Clo.UseSubsumption = CommandLineOptions.SubsumptionOption.Never;

            // Create all VCs
            name2Impl.Values
                .Iter(GenVC);

            // Start the iteration
            var worklist = new SortedSet<Tuple<int, Implementation>>();
            name2Impl.Values
                .Iter(impl => worklist.Add(Tuple.Create(impl2Priority[impl.Name], impl)));

            while (worklist.Any())
            {
                var impl = worklist.First().Item2;
                worklist.Remove(worklist.First());

                var changed = ProcessImpl(impl);

                if (changed)
                {
                    Pred[impl].Where(pred => UseBilateralAlgo || pred != impl).Iter(pred => worklist.Add(Tuple.Create(impl2Priority[pred.Name], pred)));
                }
            }

            var allImpls = new SortedSet<Tuple<int, string>>();
            name2Impl.Values.Iter(impl => allImpls.Add(Tuple.Create(impl2Priority[impl.Name], impl.Name)));
            if (CommandLineOptions.Clo.Trace)
            {
                foreach (var tup in allImpls)
                {
                    Console.WriteLine("Summary of {0}:", tup.Item2);
                    Console.WriteLine("{0}", impl2Summary[tup.Item2]);
                }
                Console.WriteLine("Prover time = {0}", proverTime.TotalSeconds.ToString("F2"));
                Console.WriteLine("Number of prover queries = " + numProverQueries);
            }

            ProduceWitness(copy);

            prover.Close();
            CommandLineOptions.Clo.TheProverFactory.Close();
        }

        // Obtain the summary expression for a procedure: used programmatically by clients
        // of AbstractHoudini
        private Expr GetSummary(Program program, Procedure proc)
        {
            if (!impl2Summary.ContainsKey(proc.Name))
                return Expr.True;

            var vars = new Dictionary<string, Expr>();
            foreach (var g in program.TopLevelDeclarations.OfType<GlobalVariable>())
                vars.Add(g.Name, Expr.Ident(g));
            foreach (var v in proc.InParams.OfType<Variable>())
                vars.Add(v.Name, Expr.Ident(v));
            foreach (var v in proc.OutParams.OfType<Variable>())
                vars.Add(v.Name, Expr.Ident(v));

            return impl2Summary[proc.Name].GetSummaryExpr(
                v => { if (vars.ContainsKey(v)) return vars[v]; else return null; },
                v => { if (vars.ContainsKey(v)) return new OldExpr(Token.NoToken, vars[v]); else return null; });
        }

        // Produce a witness that proves that the inferred annotations are correct
        private void ProduceWitness(Dictionary<string, Implementation> copy)
        {
            if (WitnessFile == null)
                return;

            foreach (var proc in program.TopLevelDeclarations.OfType<Procedure>())
            {
                var nensures = new EnsuresSeq();
                proc.Ensures.OfType<Ensures>()
                .Where(ens => !QKeyValue.FindBoolAttribute(ens.Attributes, "ah") &&
                    !QKeyValue.FindBoolAttribute(ens.Attributes, "pre") &&
                    !QKeyValue.FindBoolAttribute(ens.Attributes, "post") &&
                    QKeyValue.FindStringAttribute(ens.Attributes, "pre") == null &&
                    QKeyValue.FindStringAttribute(ens.Attributes, "post") == null)
                .Iter(ens => nensures.Add(ens));
                foreach (Ensures en in nensures)
                    en.Attributes = removeAttr("assume", en.Attributes);

                proc.Ensures = nensures;
            }

            var decls = new List<Declaration>();
            copy.Values.Iter(impl => decls.Add(impl));
            program.TopLevelDeclarations.Where(decl => !(decl is Implementation))
                .Iter(decl => decls.Add(decl));
            program.TopLevelDeclarations = decls;
            var name2Proc = new Dictionary<string, Procedure>();
            foreach (var proc in program.TopLevelDeclarations.OfType<Procedure>())
            {
                name2Proc.Add(proc.Name, proc);
                if (impl2Summary.ContainsKey(proc.Name))
                {
                    var ens = new Ensures(false, 
                        impl2Summary[proc.Name].GetSummaryExpr(
                        new Func<string, Expr>(s => null), new Func<string, Expr>(s => null)));
                    ens.Attributes = new QKeyValue(Token.NoToken, "inferred", new List<object>(), ens.Attributes);
                    proc.Ensures.Add(ens);
                }
            }

            using (var wt = new TokenTextWriter(WitnessFile))
            {
                program.Emit(wt);
            }

            // Replace SummaryPreds with their definition
            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                foreach (var blk in impl.Blocks)
                {
                    foreach (var cmd in blk.Cmds.OfType<AssumeCmd>())
                    {
                        var expr = cmd.Expr as NAryExpr;
                        if (expr == null) continue;
                        var op = expr.Fun as FunctionCall;
                        if (op == null || !op.FunctionName.EndsWith(summaryPredSuffix)) continue;
                        var calleeName = op.FunctionName.Substring(0, op.FunctionName.Length - summaryPredSuffix.Length);
                        if (!impl2Summary.ContainsKey(calleeName)) continue;
                        var callee = name2Impl[calleeName];

                        // variable order: globals, ins, outs, modifies
                        var forold = new Dictionary<string, Expr>();
                        var always = new Dictionary<string, Expr>();
                        int i = 0;
                        foreach (var g in program.TopLevelDeclarations.OfType<GlobalVariable>())
                        {
                            forold.Add(g.Name, expr.Args[i]);
                            always.Add(g.Name, expr.Args[i]);
                            i++;
                        }
                        foreach (var v in callee.InParams.OfType<Variable>())
                        {
                            always.Add(v.Name, expr.Args[i]);
                            i++;
                        }
                        foreach (var v in callee.OutParams.OfType<Variable>())
                        {
                            always.Add(v.Name, expr.Args[i]);
                            i++;
                        }
                        foreach (var ie in name2Proc[calleeName].Modifies.OfType<IdentifierExpr>())
                        {
                            always[ie.Name] = expr.Args[i];
                            i++;
                        }

                        cmd.Expr = impl2Summary[calleeName].GetSummaryExpr(
                            v => { if (always.ContainsKey(v)) return always[v]; else return null; },
                            v => { if (forold.ContainsKey(v)) return forold[v]; else return null; });
                    }
                }
            }

            using (var wt = new TokenTextWriter(WitnessFile))
            {
                program.Emit(wt);
            }
            if (CommandLineOptions.Clo.Trace) Console.WriteLine("Witness written to {0}", WitnessFile);
        }

        private QKeyValue removeAttr(string key, QKeyValue attr)
        {
            if (attr == null) return attr;
            if (attr.Key == key) return removeAttr(key, attr.Next);
            attr.Next = removeAttr(key, attr.Next);
            return attr;
        }

        private void Inline()
        {
            if (CommandLineOptions.Clo.InlineDepth < 0)
                return;

            var callGraph = BuildCallGraph();

            foreach (Implementation impl in callGraph.Nodes)
            {
                InlineRequiresVisitor inlineRequiresVisitor = new InlineRequiresVisitor();
                inlineRequiresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                FreeRequiresVisitor freeRequiresVisitor = new FreeRequiresVisitor();
                freeRequiresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                InlineEnsuresVisitor inlineEnsuresVisitor = new InlineEnsuresVisitor();
                inlineEnsuresVisitor.Visit(impl);
            }

            foreach (Implementation impl in callGraph.Nodes)
            {
                impl.OriginalBlocks = impl.Blocks;
                impl.OriginalLocVars = impl.LocVars;
            }
            foreach (Implementation impl in callGraph.Nodes)
            {
                CommandLineOptions.Inlining savedOption = CommandLineOptions.Clo.ProcedureInlining;
                CommandLineOptions.Clo.ProcedureInlining = CommandLineOptions.Inlining.Spec;
                Inliner.ProcessImplementationForHoudini(program, impl);
                CommandLineOptions.Clo.ProcedureInlining = savedOption;
            }
            foreach (Implementation impl in callGraph.Nodes)
            {
                impl.OriginalBlocks = null;
                impl.OriginalLocVars = null;
            }

            Graph<Implementation> oldCallGraph = callGraph;
            callGraph = new Graph<Implementation>();
            foreach (Implementation impl in oldCallGraph.Nodes)
            {
                callGraph.AddSource(impl);
            }
            foreach (Tuple<Implementation, Implementation> edge in oldCallGraph.Edges)
            {
                callGraph.AddEdge(edge.Item1, edge.Item2);
            }
            int count = CommandLineOptions.Clo.InlineDepth;
            while (count > 0)
            {
                foreach (Implementation impl in oldCallGraph.Nodes)
                {
                    List<Implementation> newNodes = new List<Implementation>();
                    foreach (Implementation succ in callGraph.Successors(impl))
                    {
                        newNodes.AddRange(oldCallGraph.Successors(succ));
                    }
                    foreach (Implementation newNode in newNodes)
                    {
                        callGraph.AddEdge(impl, newNode);
                    }
                }
                count--;
            }
        }

        private Graph<Implementation> BuildCallGraph()
        {
            Graph<Implementation> callGraph = new Graph<Implementation>();
            Dictionary<Procedure, HashSet<Implementation>> procToImpls = new Dictionary<Procedure, HashSet<Implementation>>();
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc == null) continue;
                procToImpls[proc] = new HashSet<Implementation>();
            }
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null || impl.SkipVerification) continue;
                callGraph.AddSource(impl);
                procToImpls[impl.Proc].Add(impl);
            }
            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null || impl.SkipVerification) continue;
                foreach (Block b in impl.Blocks)
                {
                    foreach (Cmd c in b.Cmds)
                    {
                        CallCmd cc = c as CallCmd;
                        if (cc == null) continue;
                        foreach (Implementation callee in procToImpls[cc.Proc])
                        {
                            callGraph.AddEdge(impl, callee);
                        }
                    }
                }
            }
            return callGraph;
        }


        private bool ProcessImpl(Implementation impl)
        {
            var ret = false;
            var gen = prover.VCExprGen;

            // construct summaries
            var env = VCExpressionGenerator.True;
            foreach (var tup in impl2CalleeSummaries[impl.Name])
            {
                // Not Bilateral: then reject self predicates
                if (UseBilateralAlgo == false && tup.Item1 == impl.Name)
                    continue;

                // Bilateral: only reject self summary
                if (UseBilateralAlgo == true && tup.Item1 == impl.Name && tup.Item2)
                    continue;

                var calleeSummary = 
                    impl2Summary[tup.Item1].GetSummaryExpr(
                       GetVarMapping(name2Impl[tup.Item1], tup.Item3), prover.VCExprGen);
                env = gen.AndSimp(env, gen.Eq(tup.Item3, calleeSummary));
            }

            var upper = impl2Summary[impl.Name].GetTrueSummary(program, impl);

            while(true)
            {
                var usedLower = true;
                var query = impl2Summary[impl.Name];

                // construct self summaries
                var summaryExpr = VCExpressionGenerator.True;
                foreach (var tup in impl2CalleeSummaries[impl.Name])
                {
                    if (UseBilateralAlgo == false && tup.Item1 != impl.Name)
                        continue;
                    if (UseBilateralAlgo == true && (tup.Item1 != impl.Name || !tup.Item2))
                        continue;
                    
                    if (UseBilateralAlgo)
                    {
                        query = query.AbstractConsequence(upper);
                        if (query == null) query = impl2Summary[tup.Item1];
                        else usedLower = false;
                    }

                    var ts =
                        query.GetSummaryExpr(
                           GetVarMapping(name2Impl[tup.Item1], tup.Item3), prover.VCExprGen);
                    summaryExpr = gen.AndSimp(summaryExpr, gen.Eq(tup.Item3, ts));
                }
                //Console.WriteLine("Trying summary for {0}: {1}", impl.Name, summaryExpr);

                reporter.model = null;
                var vc = gen.AndSimp(env, summaryExpr);
                vc = gen.Implies(vc, impl2VC[impl.Name]);
                
                //Console.WriteLine("Checking: {0}", vc);
                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("Verifying {0}: {1}", impl.Name, query);
                }

                var start = DateTime.Now;

                prover.BeginCheck(impl.Name, vc, reporter);
                ProverInterface.Outcome proverOutcome = prover.CheckOutcome(reporter);
                
                proverTime += (DateTime.Now - start);
                numProverQueries++;

                if (UseBilateralAlgo)
                {
                    if (proverOutcome == ProverInterface.Outcome.TimeOut || proverOutcome == ProverInterface.Outcome.OutOfMemory)
                    {
                        if(CommandLineOptions.Clo.Trace)
                            Console.WriteLine("Timeout/Spaceout while verifying " + impl.Name);
                        impl2Summary[impl.Name] = upper;
                        ret = true;
                        break;
                    }
                    
                    if (reporter.model == null && usedLower)
                        break;

                    if (reporter.model == null)
                    {
                        upper.Meet(query);
                    }
                    else
                    {
                        var state = CollectState(impl);
                        impl2Summary[impl.Name].Join(state, reporter.model);
                        ret = true;
                    }
                }
                else
                {
                    if (proverOutcome == ProverInterface.Outcome.TimeOut || proverOutcome == ProverInterface.Outcome.OutOfMemory)
                    {
                        if (CommandLineOptions.Clo.Trace)
                            Console.WriteLine("Timeout/Spaceout while verifying " + impl.Name);
                        impl2Summary[impl.Name] = impl2Summary[impl.Name].GetTrueSummary(program, impl);
                        ret = true;
                        break;
                    }

                    if (reporter.model == null)
                        break;
                    //reporter.model.Write(Console.Out);

                    var state = CollectState(impl);
                    impl2Summary[impl.Name].Join(state, reporter.model);
                    ret = true;
                }
            }
            return ret;
        }

        private Dictionary<string, VCExpr> GetVarMapping(Implementation impl, VCExprNAry summaryPred)
        {
            var ret = new Dictionary<string, VCExpr>();

            var cnt = 0;
            foreach (var g in program.TopLevelDeclarations.OfType<GlobalVariable>())
            {
                ret.Add(string.Format("old({0})", g.Name), summaryPred[cnt]);
                cnt++;
            }
            foreach (var v in impl.InParams.OfType<Variable>().Concat(
                impl.OutParams.OfType<Variable>().Concat(
                impl.Proc.Modifies.OfType<IdentifierExpr>().Select(ie => ie.Decl))))
            {
                ret.Add(v.Name, summaryPred[cnt]);
                cnt++;
            }

            // Fill up values of globals that are not modified
            cnt = 0;
            foreach (var g in program.TopLevelDeclarations.OfType<GlobalVariable>())
            {
                if (ret.ContainsKey(g.Name)) { cnt++; continue; }

                ret.Add(string.Format("{0}", g.Name), summaryPred[cnt]);
                cnt++;
            }

            // Constants
            foreach (var c in program.TopLevelDeclarations.OfType<Constant>())
            {
                var value = prover.Context.BoogieExprTranslator.Translate(Expr.Ident(c));
                ret.Add(string.Format("{0}", c.Name), value);
                ret.Add(string.Format("old({0})", c.Name), value);
            }

            return ret;
        }

        private Dictionary<string, Model.Element> CollectState(Implementation impl)
        {
            var ret = new Dictionary<string, Model.Element>();

            var model = reporter.model;
            var implVars = impl2EndStateVars[impl.Name];

            var cnt = 0;
            foreach (var g in program.TopLevelDeclarations.OfType<GlobalVariable>())
            {
                ret.Add(string.Format("old({0})", g.Name), getValue(implVars[cnt], model));
                cnt++;
            }
            foreach (var v in impl.InParams.OfType<Variable>().Concat(
                impl.OutParams.OfType<Variable>().Concat(
                impl.Proc.Modifies.OfType<IdentifierExpr>().Select(ie => ie.Decl))))
            {
                ret.Add(v.Name, getValue(implVars[cnt], model));
                cnt++;
            }

            // Fill up values of globals that are not modified
            cnt = 0;
            foreach (var g in program.TopLevelDeclarations.OfType<GlobalVariable>())
            {
                if (ret.ContainsKey(g.Name)) { cnt++; continue; }

                ret.Add(string.Format("{0}", g.Name), getValue(implVars[cnt], model));
                cnt++;
            }

            // Constants
            foreach (var c in program.TopLevelDeclarations.OfType<Constant>())
            {
                try
                {
                    var value = getValue(prover.Context.BoogieExprTranslator.Translate(Expr.Ident(c)), model);
                    ret.Add(string.Format("{0}", c.Name), value);
                    ret.Add(string.Format("old({0})", c.Name), value);
                }
                catch (Exception)
                {
                    // constant not assigned a value: add a default value
                    Model.Element value = null;
                    if (c.TypedIdent.Type.IsInt)
                        value = model.MkIntElement(0);
                    else if (c.TypedIdent.Type.IsBool)
                        value = model.MkElement("false");

                    ret.Add(string.Format("{0}", c.Name), value);
                    ret.Add(string.Format("old({0})", c.Name), value);
                }
            }

            return ret;
        }

        private Model.Element getValue(VCExpr arg, Model model)
        {
            if (arg is VCExprLiteral)
            {
                return model.GetElement(arg.ToString());
            }
            else if (arg is VCExprVar)
            {
                var el = model.GetFunc(prover.Context.Lookup(arg as VCExprVar));
                Debug.Assert(el.Arity == 0 && el.AppCount == 1);
                return el.Apps.First().Result;
            }
            else
            {
                Debug.Assert(false);
                return null;
            }
        }

        private void attachEnsures(Implementation impl)
        {
            VariableSeq functionInterfaceVars = new VariableSeq();
            foreach (Variable v in vcgen.program.GlobalVariables())
            {
                functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type), true));
            }
            foreach (Variable v in impl.InParams)
            {
                functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type), true));
            }
            foreach (Variable v in impl.OutParams)
            {
                functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", v.TypedIdent.Type), true));
            }
            foreach (IdentifierExpr e in impl.Proc.Modifies)
            {
                if (e.Decl == null) continue;
                functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", e.Decl.TypedIdent.Type), true));
            }
            Formal returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false);
            var function = new Function(Token.NoToken, impl.Name + summaryPredSuffix, functionInterfaceVars, returnVar);
            prover.Context.DeclareFunction(function, "");

            ExprSeq exprs = new ExprSeq();
            foreach (Variable v in vcgen.program.GlobalVariables())
            {
                Contract.Assert(v != null);
                exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
            }
            foreach (Variable v in impl.Proc.InParams)
            {
                Contract.Assert(v != null);
                exprs.Add(new IdentifierExpr(Token.NoToken, v));
            }
            foreach (Variable v in impl.Proc.OutParams)
            {
                Contract.Assert(v != null);
                exprs.Add(new IdentifierExpr(Token.NoToken, v));
            }
            foreach (IdentifierExpr ie in impl.Proc.Modifies)
            {
                Contract.Assert(ie != null);
                if (ie.Decl == null)
                    continue;
                exprs.Add(ie);
            }
            Expr postExpr = new NAryExpr(Token.NoToken, new FunctionCall(function), exprs);
            impl.Proc.Ensures.Add(
                new Ensures(Token.NoToken, false, postExpr, "", 
                    new QKeyValue(Token.NoToken, "ah", new List<object>(), null)));
        }

        private void GenVC(Implementation impl)
        {
            ModelViewInfo mvInfo;
            System.Collections.Hashtable label2absy;

            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Generating VC of {0}", impl.Name);
            }

            vcgen.ConvertCFG2DAG(impl);
            vcgen.PassifyImpl(impl, out mvInfo);

            var gen = prover.VCExprGen;
            var vcexpr = vcgen.GenerateVC(impl, null, out label2absy, prover.Context);

            // Create a macro so that the VC can sit with the theorem prover
            Macro macro = new Macro(Token.NoToken, impl.Name + "Macro", new VariableSeq(), new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false));
            prover.DefineMacro(macro, vcexpr);

            // Store VC
            impl2VC.Add(impl.Name, gen.Function(macro));

            //Console.WriteLine("VC of {0}: {1}", impl.Name, vcexpr);

            // Find the assert
            impl2EndStateVars.Add(impl.Name, new List<VCExpr>());
            var found = false;
            var assertId = -1;
            foreach (var blk in impl.Blocks)
            {
                foreach (var cmd in blk.Cmds.OfType<AssertCmd>())
                {
                    if (SimpleUtil.isAssertTrue(cmd)) continue;
                    var nary = cmd.Expr as NAryExpr;
                    if (nary == null) continue;
                    var pred = nary.Fun as FunctionCall;
                    if (pred == null || pred.FunctionName != (impl.Name + (AbstractHoudini.summaryPredSuffix)))
                        continue;

                    Debug.Assert(!found);
                    found = true;
                    assertId = cmd.UniqueId;
                    //Console.WriteLine("assert cmd id: {0}", cmd.UniqueId);
                    nary.Args.OfType<Expr>()
                        .Iter(expr => impl2EndStateVars[impl.Name].Add(prover.Context.BoogieExprTranslator.Translate(expr)));
                }
            }
            Debug.Assert(found);

            // Grab summary predicates
            var visitor = new FindSummaryPred(prover.VCExprGen, assertId);
            visitor.Mutate(vcexpr, true);

            // check sanity: only one predicate for self-summary
            // (There may be none when the procedure doesn't return)
            Debug.Assert(visitor.summaryPreds.Count(tup => tup.Item2) <= 1);

            impl2CalleeSummaries.Add(impl.Name, new List<Tuple<string, bool, VCExprNAry>>());
            visitor.summaryPreds.Iter(tup => impl2CalleeSummaries[impl.Name].Add(tup));
        }
    }

    public interface ISummaryElement
    {
        ISummaryElement GetFlaseSummary(Program program, Implementation impl);
        void Join(Dictionary<string, Model.Element> state, Model model);
        VCExpr GetSummaryExpr(Dictionary<string, VCExpr> incarnations, VCExpressionGenerator gen);
        Expr GetSummaryExpr(Func<string, Expr> always, Func<string, Expr> forold);

        // For Bilateral
        ISummaryElement GetTrueSummary(Program program, Implementation impl);
        void Meet(ISummaryElement other);
        bool IsEqual(ISummaryElement other);
        ISummaryElement AbstractConsequence(ISummaryElement upper);
    }

    public class ConstantVal : ISummaryElement
    {
        Program program;
        Implementation impl;
        // var -> const set
        Dictionary<string, HashSet<int>> val;
        // set of vars
        HashSet<Variable> vars;

        public static readonly int MAX = 3;

        public ConstantVal()
        {
            // this is just a place holder
            val = new Dictionary<string, HashSet<int>>();
            vars = new HashSet<Variable>();
        }

        private ConstantVal(Program program, Implementation impl)
        {
            this.program = program;
            this.impl = impl;
            this.val = new Dictionary<string, HashSet<int>>();

            vars = new HashSet<Variable>();
            impl.Proc.Modifies
                .OfType<IdentifierExpr>()
                .Select(ie => ie.Decl)
                .Where(v => v.TypedIdent.Type.IsInt)
                .Iter(v => vars.Add(v));
            impl.OutParams.OfType<Variable>()
                .Where(v => v.TypedIdent.Type.IsInt)
                .Iter(v => vars.Add(v));

            vars.Iter(v => val.Add(v.Name, null));
        }


        public void Join(Dictionary<string, Model.Element> state, Model model)
        {
            foreach (var vv in vars)
            {
                var v = vv.Name;
                var newv = state[v].AsInt();
                var oldv = val[v];

                if (oldv == null)
                {
                    val[v] = new HashSet<int>();
                    val[v].Add(newv);
                }
                else if(oldv.Count > 0)
                {
                    val[v].Add(newv);
                    if (val[v].Count > MAX)
                        val[v] = new HashSet<int>();
                } 

            }
        }

        public VCExpr GetSummaryExpr(Dictionary<string, VCExpr> incarnations, VCExpressionGenerator gen)
        {
            VCExpr ret = VCExpressionGenerator.True;
            if (val.Values.Any(v => v == null))
                return VCExpressionGenerator.False;
            
            foreach (var v in vars)
            {
                var consts = val[v.Name];
                Debug.Assert(consts != null);

                if (consts.Count == 0)
                    continue;

                var vexpr = VCExpressionGenerator.False;
                consts.Iter(c => vexpr = gen.OrSimp(vexpr, gen.Eq(incarnations[v.Name], gen.Integer(Microsoft.Basetypes.BigNum.FromInt(c)))));
                ret = gen.AndSimp(ret, vexpr);
            }

            return ret;
        }

        public override string ToString()
        {
            var ret = "true";
            if (val.Values.Any(v => v == null))
                return "false";

            foreach (var v in vars)
            {
                var consts = val[v.Name];
                Debug.Assert(consts != null);

                if (consts.Count == 0)
                    continue;

                var vexpr = "false";
                consts.Iter(c => vexpr = 
                    string.Format("{0} OR ({1} == {2})", vexpr, v.Name, c));

                ret = string.Format("{0} AND ({1})", ret, vexpr);
            }

            return ret;
        }


        public ISummaryElement GetFlaseSummary(Program program, Implementation impl)
        {
            return new ConstantVal(program, impl);
        }

        #region ISummaryElement (Bilateral) Members


        public ISummaryElement GetTrueSummary(Program program, Implementation impl)
        {
            throw new NotImplementedException();
        }

        public void Meet(ISummaryElement other)
        {
            throw new NotImplementedException();
        }

        public bool IsEqual(ISummaryElement other)
        {
            throw new NotImplementedException();
        }

        public ISummaryElement AbstractConsequence(ISummaryElement upper)
        {
            throw new NotImplementedException();
        }

        #endregion

        #region ISummaryElement Members


        public Expr GetSummaryExpr(Func<string, Expr> always, Func<string, Expr> forold)
        {
            throw new NotImplementedException();
        }

        #endregion
    }

    public class NamedExpr 
    {
        public string name;
        public Expr expr;

        public NamedExpr(string name, Expr expr)
        {
            this.name = name;
            this.expr = expr;
        }

        public NamedExpr(Expr expr)
        {
            this.name = null;
            this.expr = expr;
        }

        public override string ToString()
        {
            //if (name != null)
            //    return name;

            return expr.ToString();
        }
    }

    public class PredicateAbs : ISummaryElement
    {
        public static Dictionary<string, List<NamedExpr>> PrePreds { get; private set; }
        public static Dictionary<string, List<NamedExpr>> PostPreds { get; private set; }
        private static HashSet<string> boolConstants;
        // Temporary: used during eval
        private static Model model = null;

        string procName;
        PredicateAbsDisjunct[] value;
        bool isFalse;

        public PredicateAbs(string procName)
        {
            this.procName = procName;
            isFalse = true;
            value = new PredicateAbsDisjunct[PostPreds[this.procName].Count];
            for (int i = 0; i < PostPreds[this.procName].Count; i++) value[i] = null;
        }

        public static void Initialize(Program program)
        {
            PrePreds = new Dictionary<string, List<NamedExpr>>();
            PostPreds = new Dictionary<string, List<NamedExpr>>();
            boolConstants = new HashSet<string>();

            program.TopLevelDeclarations.OfType<Constant>()
                .Where(c => c.TypedIdent.Type.IsBool)
                .Iter(c => boolConstants.Add(c.Name));

            // Add template pre-post to all procedures
            var preT = new List<NamedExpr>();
            var postT = new List<NamedExpr>();
            var tempP = new HashSet<Procedure>();
            foreach (var proc in
                program.TopLevelDeclarations.OfType<Procedure>()
                .Where(proc => QKeyValue.FindBoolAttribute(proc.Attributes, "template")))
            {
                tempP.Add(proc);
                foreach (var ens in proc.Ensures.OfType<Ensures>())
                {
                    if (QKeyValue.FindBoolAttribute(ens.Attributes, "pre"))
                        preT.Add(new NamedExpr(null, ens.Condition));
                    if (QKeyValue.FindBoolAttribute(ens.Attributes, "post"))
                        postT.Add(new NamedExpr(null, ens.Condition));

                    var s = QKeyValue.FindStringAttribute(ens.Attributes, "pre");
                    if (s != null)
                        preT.Add(new NamedExpr(s, ens.Condition));

                    s = QKeyValue.FindStringAttribute(ens.Attributes, "post");
                    if (s != null)
                        postT.Add(new NamedExpr(s, ens.Condition));
                }
            }

            program.TopLevelDeclarations.RemoveAll(decl => tempP.Contains(decl));

            foreach (var impl in program.TopLevelDeclarations.OfType<Implementation>())
            {
                PrePreds.Add(impl.Name, new List<NamedExpr>());
                PostPreds.Add(impl.Name, new List<NamedExpr>());

                preT.Iter(e => PrePreds[impl.Name].Add(e));
                postT.Iter(e => PostPreds[impl.Name].Add(e));

                // Pick up per-procedure pre-post
                var nens = new EnsuresSeq();
                foreach (var ens in impl.Proc.Ensures.OfType<Ensures>())
                {
                    string s = null;
                    if (QKeyValue.FindBoolAttribute(ens.Attributes, "pre"))
                    {
                        PrePreds[impl.Name].Add(new NamedExpr(ens.Condition));
                    }
                    else if (QKeyValue.FindBoolAttribute(ens.Attributes, "post"))
                    {
                        PostPreds[impl.Name].Add(new NamedExpr(ens.Condition));
                    }
                    else if ((s = QKeyValue.FindStringAttribute(ens.Attributes, "pre")) != null)
                    {
                        PrePreds[impl.Name].Add(new NamedExpr(s, ens.Condition));
                    }
                    else if ((s = QKeyValue.FindStringAttribute(ens.Attributes, "post")) != null)
                    {
                        PostPreds[impl.Name].Add(new NamedExpr(s, ens.Condition));
                    }
                    else
                    {
                        nens.Add(ens);
                    }
                }
                impl.Proc.Ensures = nens;
            }
            
            //Console.WriteLine("Running Abstract Houdini");
            //PostPreds.Iter(expr => Console.WriteLine("\tPost: {0}", expr));
            //PrePreds.Iter(expr => Console.WriteLine("\tPre: {0}", expr));
        }

        private Model.Element Eval(Expr expr, Dictionary<string, Model.Element> state)
        {
            if (expr is LiteralExpr)
            {
                return ToElem((expr as LiteralExpr).Val);
            }

            if (expr is IdentifierExpr)
            {
                return LookupVariable((expr as IdentifierExpr).Name, state, false);
            }

            if (expr is OldExpr)
            {
                var ide = (expr as OldExpr).Expr as IdentifierExpr;
                Debug.Assert(ide != null);

                return LookupVariable(ide.Name, state, true);
            }

            if (expr is NAryExpr)
            {
                var nary = expr as NAryExpr;
                if (nary.Fun is UnaryOperator)
                {
                    return ToElem((nary.Fun as UnaryOperator).Evaluate(ToValue(Eval(nary.Args[0], state))));
                }
                if (nary.Fun is BinaryOperator)
                {
                    return ToElem((nary.Fun as BinaryOperator).Evaluate(ToValue(Eval(nary.Args[0], state)), ToValue(Eval(nary.Args[1], state))));
                }
                if (nary.Fun is MapSelect && nary.Args.Length == 2)
                {
                    var index = Eval(nary.Args[1], state);
                    var map = Eval(nary.Args[0], state) as Model.Array;
                    Debug.Assert(map != null, "Variable of map type must have an Array-typed value");
                    var ret = map.Value.TryEval(index as Model.Element);
                    if (ret == null) ret = map.Value.Else;
                    Debug.Assert(ret != null);
                    return ret;
                }
                Debug.Assert(false, "No other op is handled");                
            }
            throw new NotImplementedException(string.Format("Expr of type {0} is not handled", expr.GetType().ToString()));
        }

        private Model.Element LookupVariable(string v, Dictionary<string, Model.Element> state, bool tryOld)
        {
            if (tryOld)
            {
                var oldv = string.Format("old({0})", v);
                if (state.ContainsKey(oldv))
                {
                    return state[oldv];
                }
                throw new AbsHoudiniInternalError("Cannot handle this case");
            }

            if (state.ContainsKey(v))
            {
                return state[v];
            }

            /*
            if (boolConstants.Contains(v))
            {
                // value of this constant is immaterial, return true
                return model.MkElement("true");
            }
            */

            throw new AbsHoudiniInternalError("Cannot handle this case");
        }

        private VCExpr ToVcVar(string v, Dictionary<string, VCExpr> incarnations, bool tryOld)
        {
            if (tryOld)
            {
                var oldv = string.Format("old({0})", v);
                if (incarnations.ContainsKey(oldv))
                {
                    return incarnations[oldv];
                }
                throw new AbsHoudiniInternalError("Cannot handle this case");
            }

            if (incarnations.ContainsKey(v))
            {
                return incarnations[v];
            }

            throw new AbsHoudiniInternalError("Cannot handle this case");
        }

        private object ToValue(Model.Element elem)
        {
            if (elem is Model.Integer)
            {
                return Microsoft.Basetypes.BigNum.FromInt((elem as Model.Integer).AsInt());
            }
            if (elem is Model.Boolean)
            {
                return (elem as Model.Boolean).Value;
            }
            throw new NotImplementedException("Cannot yet handle this Model.Element type");
        }

        private Model.Element ToElem(object val)
        {
            if (val is bool || val is int || val is Basetypes.BigNum)
                return model.MkElement(val.ToString());
            throw new NotImplementedException("Cannot yet handle this value type");
        }

        private static Expr ToExpr(Expr expr, Func<string, Expr> always, Func<string, Expr> forold)
        {
            var substalways = new Substitution(v =>
            {
                var ret = always(v.Name);
                if (ret != null) return ret;
                else return Expr.Ident(v);
            });
            var substold = new Substitution(v =>
            {
                var ret = forold(v.Name);
                if (ret != null) return ret;
                else return new OldExpr(Token.NoToken, Expr.Ident(v));
            });

            return Substituter.ApplyReplacingOldExprs(substalways, substold, expr);
        }

        private VCExpr ToVcExpr(Expr expr, Dictionary<string, VCExpr> incarnations, VCExpressionGenerator gen)
        {
            if (expr is LiteralExpr)
            {
                var val = (expr as LiteralExpr).Val;
                if (val is bool)
                {
                    if ((bool)val)
                    {
                        return VCExpressionGenerator.True;
                    }
                    else
                    {
                        return VCExpressionGenerator.False;
                    }
                }
                else if (val is Microsoft.Basetypes.BigNum)
                {
                    return gen.Integer((Microsoft.Basetypes.BigNum)val);
                }

                throw new NotImplementedException("Cannot handle literals of this type");
            }

            if (expr is IdentifierExpr)
            {
                return ToVcVar((expr as IdentifierExpr).Name, incarnations, false);
            }

            if (expr is OldExpr)
            {
                var ide = (expr as OldExpr).Expr as IdentifierExpr;
                Debug.Assert(ide != null);

                return ToVcVar(ide.Name, incarnations, true);
            }

            if (expr is NAryExpr)
            {
                var nary = expr as NAryExpr;
                if (nary.Fun is UnaryOperator)
                {
                    if ((nary.Fun as UnaryOperator).Op == UnaryOperator.Opcode.Not)
                        return gen.Not(ToVcExpr(nary.Args[0], incarnations, gen));
                    else if ((nary.Fun as UnaryOperator).Op == UnaryOperator.Opcode.Neg)
                        return gen.Function(VCExpressionGenerator.SubIOp, gen.Integer(Basetypes.BigNum.FromInt(0)), ToVcExpr(nary.Args[0], incarnations, gen));
                    else
                        Debug.Assert(false, "No other unary op is handled");
                }
                if (nary.Fun is BinaryOperator)
                {
                    return gen.Function(Translate(nary.Fun as BinaryOperator), ToVcExpr(nary.Args[0], incarnations, gen), ToVcExpr(nary.Args[1], incarnations, gen));
                }
                if (nary.Fun is MapSelect && nary.Args.Length == 2)
                {
                    return gen.Select(ToVcExpr(nary.Args[0], incarnations, gen), ToVcExpr(nary.Args[1], incarnations, gen));
                }
                Debug.Assert(false, "No other op is handled");
            }
            throw new NotImplementedException(string.Format("Expr of type {0} is not handled", expr.GetType().ToString()));
        }

        private VCExprOp Translate(BinaryOperator op)
        {
            switch (op.Op)
            {
                case BinaryOperator.Opcode.Add:
                    return VCExpressionGenerator.AddIOp;
                case BinaryOperator.Opcode.Sub:
                    return VCExpressionGenerator.SubIOp;
                case BinaryOperator.Opcode.Mul:
                    return VCExpressionGenerator.MulIOp;
                case BinaryOperator.Opcode.Div:
                    return VCExpressionGenerator.DivIOp;
                case BinaryOperator.Opcode.Mod:
                    return VCExpressionGenerator.ModOp;
                case BinaryOperator.Opcode.Eq:
                case BinaryOperator.Opcode.Iff:
                    // we don't distinguish between equality and equivalence at this point
                    return VCExpressionGenerator.EqOp;
                case BinaryOperator.Opcode.Neq:
                    return VCExpressionGenerator.NeqOp;
                case BinaryOperator.Opcode.Lt:
                    return VCExpressionGenerator.LtOp;
                case BinaryOperator.Opcode.Le:
                    return VCExpressionGenerator.LeOp;
                case BinaryOperator.Opcode.Ge:
                    return VCExpressionGenerator.GeOp;
                case BinaryOperator.Opcode.Gt:
                    return VCExpressionGenerator.GtOp;
                case BinaryOperator.Opcode.Imp:
                    return VCExpressionGenerator.ImpliesOp;
                case BinaryOperator.Opcode.And:
                    return VCExpressionGenerator.AndOp;
                case BinaryOperator.Opcode.Or:
                    return VCExpressionGenerator.OrOp;
                case BinaryOperator.Opcode.Subtype:
                    return VCExpressionGenerator.SubtypeOp;
                default:
                    Contract.Assert(false);
                    throw new NotImplementedException();
            }

        }

        public override string ToString()
        {
            var ret = "";
            if (isFalse) return "false";
            var first = true;
            PredicateAbsConjunct.tempProcName = procName;
            for(int i = 0; i < PostPreds[procName].Count; i++) 
            {
                if(value[i].isFalse) continue;
                
                if(value[i].isTrue)
                    ret += string.Format("{0}{1}", first ? "" : " && ", PostPreds[procName][i]);
                else
                    ret += string.Format("{0}({1} ==> {2})", first ? "" : " && ", value[i], PostPreds[procName][i]);

                first = false;
            }
            if (ret == "") ret = "true";
            return ret;
        }


        #region ISummaryElement Members

        public ISummaryElement GetFlaseSummary(Program program, Implementation impl)
        {
            return new PredicateAbs(impl.Name);
        }

        public ISummaryElement GetTrueSummary(Program program, Implementation impl)
        {
            var ret = new PredicateAbs(impl.Name);
            ret.isFalse = false;
            for (int i = 0; i < PostPreds[this.procName].Count; i++) ret.value[i] = new PredicateAbsDisjunct(false);

            return ret;
        }

        public void Join(Dictionary<string, Model.Element> state, Model model)
        {
            PredicateAbs.model = model;

            // Evaluate each predicate on the state
            var prePredsVal = new bool[PrePreds[procName].Count];
            var postPredsVal = new bool[PostPreds[procName].Count];

            var indexSeq = new List<int>();
            for (int i = 0; i < PrePreds[procName].Count; i++) indexSeq.Add(i);

            for (int i = 0; i < PrePreds[procName].Count; i++)
            {
                var v = ToValue(Eval(PrePreds[procName][i].expr, state));
                Debug.Assert(v is bool);
                prePredsVal[i] = (bool)v;
            }

            for (int i = 0; i < PostPreds[procName].Count; i++)
            {
                var v = ToValue(Eval(PostPreds[procName][i].expr, state));
                Debug.Assert(v is bool);
                postPredsVal[i] = (bool)v;
            }

            for (int i = 0; i < PostPreds[procName].Count; i++)
            {
                // No hope for this post pred?
                if (!isFalse && value[i].isFalse) continue;

                var newDisj = new PredicateAbsDisjunct(true);
                if (!postPredsVal[i])
                {
                    newDisj = new PredicateAbsDisjunct(indexSeq.Where(j => !prePredsVal[j]), indexSeq.Where(j => prePredsVal[j]));
                }

                if (isFalse)
                    value[i] = newDisj;
                else 
                    value[i] = PredicateAbsDisjunct.And(value[i], newDisj);
            }

            isFalse = false;

            //Console.WriteLine("Result of Join: {0}", this.ToString());
        }

        // Precondition: the upper guys are just {true/false} ==> post-pred
        public void Meet(ISummaryElement iother)
        {
            var other = iother as PredicateAbs;
            if (isFalse) return;
            if (other.isFalse)
            {
                isFalse = true;
                for (int i = 0; i < PostPreds[this.procName].Count; i++) value[i] = null;
                return;
            }
            Debug.Assert(this.procName == other.procName);

            for (int i = 0; i < PostPreds[this.procName].Count; i++)
            {
                // check precondition
                if (!value[i].isTrue && !value[i].isFalse)
                    throw new NotImplementedException("Invalid upper domain element");
                if (!other.value[i].isTrue && !other.value[i].isFalse)
                    throw new NotImplementedException("Invalid upper domain element");

                if (value[i].isFalse && other.value[i].isTrue)
                    value[i] = new PredicateAbsDisjunct(true);
            }
        }

        public bool IsEqual(ISummaryElement other)
        {
            return false;
        }

        // Precondition: the upper guys are just {true/false} ==> post-pred
        // Postcondition: the returned value is also of this form
        public ISummaryElement AbstractConsequence(ISummaryElement iupper)
        {
            var upper = iupper as PredicateAbs;

            for (int i = 0; i < PostPreds[this.procName].Count; i++)
            {
                // check precondition
                if (!upper.value[i].isTrue && !upper.value[i].isFalse)
                    throw new NotImplementedException("Invalid upper domain element");

                if (upper.value[i].isTrue)
                    continue;

                var ret = new PredicateAbs(this.procName);
                ret.isFalse = false;
                for (int j = 0; j < PostPreds[this.procName].Count; j++)
                    ret.value[j] = new PredicateAbsDisjunct(false);

                ret.value[i] = new PredicateAbsDisjunct(true);

                // check that this \lesseq ret 
                if (isFalse) return ret;

                if (value[i].isTrue)
                    return ret;
            }

            // Giveup: the abstract consequence is too difficult to compute
            return null;
        }

        public VCExpr GetSummaryExpr(Dictionary<string, VCExpr> incarnations, VCExpressionGenerator gen)
        {
            if (isFalse)
                return VCExpressionGenerator.False;

            var ret = VCExpressionGenerator.True;

            for(int i = 0; i < PostPreds[procName].Count; i++)
            {
                ret = gen.AndSimp(ret, gen.ImpliesSimp(value[i].ToVcExpr(j => ToVcExpr(PrePreds[procName][j].expr, incarnations, gen), gen), ToVcExpr(PostPreds[procName][i].expr, incarnations, gen)));
            }

            return ret;
        }

        public Expr GetSummaryExpr(Func<string, Expr> always, Func<string, Expr> forold)
        {
            if (isFalse)
                return Expr.False;

            Expr ret = Expr.True;

            for (int i = 0; i < PostPreds[procName].Count; i++)
            {
                ret = Expr.And(ret, Expr.Imp(value[i].ToExpr(j => ToExpr(PrePreds[procName][j].expr, always, forold)), ToExpr(PostPreds[procName][i].expr, always, forold)));
            }

            return ret;
        }

        #endregion
    }

    class PredicateAbsDisjunct
    {
        List<PredicateAbsConjunct> conjuncts;
        public bool isTrue {get; private set;}
        public bool isFalse
        {
            get
            {
                if (isTrue) return false;
                return conjuncts.Count == 0;
            }
        }

        public PredicateAbsDisjunct(bool isTrue)
        {
            this.isTrue = isTrue;
            conjuncts = new List<PredicateAbsConjunct>();
        }

        private PredicateAbsDisjunct(List<PredicateAbsConjunct> conjuncts)
        {
            isTrue = false;
            this.conjuncts = conjuncts;
        }

        // Disjunct of singleton conjuncts
        public PredicateAbsDisjunct(IEnumerable<int> pos, IEnumerable<int> neg)
        {
            conjuncts = new List<PredicateAbsConjunct>();
            isTrue = false;
            pos.Iter(p => conjuncts.Add(PredicateAbsConjunct.Singleton(p, true)));
            neg.Iter(p => conjuncts.Add(PredicateAbsConjunct.Singleton(p, false)));
        }

        public static PredicateAbsDisjunct And(PredicateAbsDisjunct v1, PredicateAbsDisjunct v2)
        {
            if (v1.isTrue) return v2;
            if (v2.isTrue) return v1;

            var result = new List<PredicateAbsConjunct>();

            foreach (var c1 in v1.conjuncts)
            {
                foreach (var c2 in v2.conjuncts)
                {
                    var c = PredicateAbsConjunct.And(c1, c2);
                    if (c.isFalse) continue;
                    if (result.Any(cprime => c.implies(cprime))) continue;
                    var tmp = new List<PredicateAbsConjunct>();
                    tmp.Add(c);
                    result.Where(cprime => !cprime.implies(c)).Iter(cprime => tmp.Add(cprime));
                    result = tmp;
                }
            }

            return new PredicateAbsDisjunct(result);
        }

        public VCExpr ToVcExpr(Func<int, VCExpr> predToExpr, VCExpressionGenerator gen)
        {
            if (isTrue) return VCExpressionGenerator.True;
            var ret = VCExpressionGenerator.False;
            conjuncts.Iter(c => ret = gen.OrSimp(ret, c.ToVcExpr(predToExpr, gen)));
            return ret;
        }

        public Expr ToExpr(Func<int, Expr> predToExpr)
        {
            if (isTrue) return Expr.True;
            Expr ret = Expr.False;
            conjuncts.Iter(c => ret = Expr.Or(ret, c.ToExpr(predToExpr)));
            return ret;
        }

        public override string ToString()
        {
            if(isTrue) 
                return "true";
            var ret = "";
            var first = true;
            foreach (var c in conjuncts)
            {
                if (c.isFalse) continue;
                ret += string.Format("{0}{1}", first ? "" : " || ", c);
                first = false;
            }
            return ret;
        }
    }

    class PredicateAbsConjunct
    {
        static int ConjunctBound = 3;
        public static string tempProcName = null;

        public bool isFalse { get; private set; }
        HashSet<int> posPreds;
        HashSet<int> negPreds;

        public static void Initialize(int bound)
        {
            ConjunctBound = bound;
        }

        private void Normalize()
        {
            if (posPreds.Intersect(negPreds).Any() || negPreds.Intersect(posPreds).Any() || (posPreds.Count + negPreds.Count > ConjunctBound))
            {
                isFalse = true;
                posPreds = new HashSet<int>();
                negPreds = new HashSet<int>();
            }
        }

        public PredicateAbsConjunct(bool isFalse)
        {
            posPreds = new HashSet<int>();
            negPreds = new HashSet<int>();
            this.isFalse = isFalse;
        }

        public static PredicateAbsConjunct Singleton(int v, bool isPositive)
        {
            if (isPositive)
                return new PredicateAbsConjunct(new int[] { v }, new HashSet<int>());
            else
                return new PredicateAbsConjunct(new HashSet<int>(), new int[] { v });
        }

        public PredicateAbsConjunct(IEnumerable<int> pos, IEnumerable<int> neg)
        {
            isFalse = false;
            posPreds = new HashSet<int>(pos);
            negPreds = new HashSet<int>(neg);
            Normalize();
        }

        public static PredicateAbsConjunct And(PredicateAbsConjunct v1, PredicateAbsConjunct v2)
        {
            if (v1.isFalse || v2.isFalse) return new PredicateAbsConjunct(true);
            return new PredicateAbsConjunct(v1.posPreds.Union(v2.posPreds), v1.negPreds.Union(v2.negPreds));
        }

        public bool implies(PredicateAbsConjunct v)
        {
            if (isFalse) return true;
            if (v.isFalse) return false;
            return (posPreds.IsSupersetOf(v.posPreds) && negPreds.IsSupersetOf(v.negPreds));
        }

        public VCExpr ToVcExpr(Func<int, VCExpr> predToExpr, VCExpressionGenerator gen)
        {
            if (isFalse) return VCExpressionGenerator.False;
            var ret = VCExpressionGenerator.True;
            posPreds.Iter(p => ret = gen.AndSimp(ret, predToExpr(p)));
            negPreds.Iter(p => ret = gen.AndSimp(ret, gen.Not(predToExpr(p))));
            return ret;
        }

        public Expr ToExpr(Func<int, Expr> predToExpr)
        {
            if (isFalse) return Expr.False;
            Expr ret = Expr.True;
            posPreds.Iter(p => ret = Expr.And(ret, predToExpr(p)));
            negPreds.Iter(p => ret = Expr.And(ret, Expr.Not(predToExpr(p)))); 
            return ret;
        }

        public override string ToString()
        {
            if (isFalse)
                return "false";

            var ret = "";
            var first = true;
            foreach (var p in posPreds)
            {
                ret += string.Format("{0}{1}", first ? "" : " && ", PredicateAbs.PrePreds[tempProcName][p]);
                first = false;
            }
            foreach (var p in negPreds)
            {
                ret += string.Format("{0}!{1}", first ? "" : " && ", PredicateAbs.PrePreds[tempProcName][p]);
                first = false;
            }
            return ret;
        }
    }

    class FindSummaryPred : MutatingVCExprVisitor<bool>
    {
        public List<Tuple<string, bool, VCExprNAry>> summaryPreds;
        int assertId;

        public FindSummaryPred(VCExpressionGenerator gen, int assertId)
            : base(gen)
        {
            summaryPreds = new List<Tuple<string, bool, VCExprNAry>>();
            this.assertId = assertId;
        }

        protected override VCExpr/*!*/ UpdateModifiedNode(VCExprNAry/*!*/ originalNode,
                                              List<VCExpr/*!*/>/*!*/ newSubExprs,
            // has any of the subexpressions changed?
                                              bool changed,
                                              bool arg)
        {
            Contract.Ensures(Contract.Result<VCExpr>() != null);

            VCExpr ret;
            if (changed)
                ret = Gen.Function(originalNode.Op,
                                   newSubExprs, originalNode.TypeArguments);
            else
                ret = originalNode;

            VCExprNAry retnary = ret as VCExprNAry;
            if (retnary == null) return ret;
            var op = retnary.Op as VCExprBoogieFunctionOp;
            var selfSummary = false;

            if (op == null)
            {
                var lop = retnary.Op as VCExprLabelOp;
                if (lop == null) return ret;
                if (lop.pos) return ret;
                if (!lop.label.Equals("@" + assertId.ToString())) return ret;
                
                var subexpr = retnary[0] as VCExprNAry;
                if (subexpr == null) return ret;
                op = subexpr.Op as VCExprBoogieFunctionOp;
                if (op == null) return ret;

                selfSummary = true;
                retnary = subexpr;
            }

            string calleeName = op.Func.Name;

            if (!calleeName.EndsWith(AbstractHoudini.summaryPredSuffix))
                return ret;

            if (selfSummary)
            {
                // This summary pred would have been found twice
                var nlist = new List<Tuple<string, bool, VCExprNAry>>();
                foreach (var tup in summaryPreds)
                {
                    if (tup.Item3 != retnary) nlist.Add(tup);
                }
                summaryPreds = nlist;
            }

            summaryPreds.Add(Tuple.Create(calleeName.Substring(0, calleeName.Length - AbstractHoudini.summaryPredSuffix.Length), selfSummary, retnary));


            return ret;
        }

    }

    class AbstractHoudiniErrorReporter : ProverInterface.ErrorHandler
    {
        public Model model;

        public AbstractHoudiniErrorReporter()
        {
            model = null;
        }

        public override void OnModel(IList<string> labels, Model model)
        {
            Debug.Assert(model != null);
            //model.Write(Console.Out);
            this.model = model;
        }
    }


    public class AbsHoudiniInternalError : System.ApplicationException
    {
        public AbsHoudiniInternalError(string msg) : base(msg) { }

    };

    public class SimpleUtil
    {
        // Constructs a mapping from procedure names to the implementation
        public static Dictionary<string, Implementation> nameImplMapping(Program p)
        {
            var m = new Dictionary<string, Implementation>();
            foreach (Declaration d in p.TopLevelDeclarations)
            {
                if (d is Implementation)
                {
                    Implementation impl = d as Implementation;
                    m.Add(impl.Name, impl);
                }
            }

            return m;
        }

        // is "assert true"?
        public static bool isAssertTrue(Cmd cmd)
        {
            var acmd = cmd as AssertCmd;
            if (acmd == null) return false;
            var le = acmd.Expr as LiteralExpr;
            if (le == null) return false;
            if (le.IsTrue) return true;
            return false;
        }
    }

}
