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

    public class AbsHoudini
    {
        Dictionary<string, Function> existentialFunctions;
        Program program;
        Dictionary<string, Implementation> name2Impl;
        Dictionary<string, VCExpr> impl2VC;
        Dictionary<string, List<Tuple<string, Function, NAryExpr>>> impl2FuncCalls;
        // constant -> the naryexpr that it replaced
        Dictionary<string, NAryExpr> constant2FuncCall;

        // function -> its abstract value
        Dictionary<string, IAbstractDomain> function2Value;

        // impl -> functions assumed/asserted
        Dictionary<string, HashSet<string>> impl2functionsAsserted, impl2functionsAssumed;

        // funtions -> impls where assumed/asserted
        Dictionary<string, HashSet<string>> function2implAssumed, function2implAsserted;

        // impl -> handler, collector
        Dictionary<string, Tuple<ProverInterface.ErrorHandler, AbsHoudiniCounterexampleCollector>> impl2ErrorHandler;

        // Essentials: VCGen, Prover
        VCGen vcgen;
        ProverInterface prover;

        // Stats
        TimeSpan proverTime;
        int numProverQueries;

        public AbsHoudini(Program program, IAbstractDomain defaultElem)
        {
            this.program = program;
            this.impl2VC = new Dictionary<string, VCExpr>();
            this.impl2FuncCalls = new Dictionary<string, List<Tuple<string, Function, NAryExpr>>>();
            this.existentialFunctions = new Dictionary<string, Function>();
            this.name2Impl = new Dictionary<string, Implementation>();
            this.impl2functionsAsserted = new Dictionary<string, HashSet<string>>();
            this.impl2functionsAssumed = new Dictionary<string, HashSet<string>>();
            this.function2implAsserted = new Dictionary<string, HashSet<string>>();
            this.function2implAssumed = new Dictionary<string, HashSet<string>>();
            this.impl2ErrorHandler = new Dictionary<string, Tuple<ProverInterface.ErrorHandler, AbsHoudiniCounterexampleCollector>>();
            this.constant2FuncCall = new Dictionary<string, NAryExpr>();

            // Find the existential functions
            foreach (var func in program.Functions
                .Where(f => QKeyValue.FindBoolAttribute(f.Attributes, "existential")))
                existentialFunctions.Add(func.Name, func);

            this.function2Value = new Dictionary<string, IAbstractDomain>();
            foreach (var func in existentialFunctions.Values)
            {
                // Find if the function wishes to use a specific abstract domain
                var domain = QKeyValue.FindStringAttribute(func.Attributes, "absdomain");
                if (domain == null)
                {
                    function2Value[func.Name] = defaultElem.Bottom();
                }
                else
                {
                    function2Value[func.Name] = AbstractDomainFactory.GetInstance(domain);
                }
            }
            existentialFunctions.Keys.Iter(f => function2implAssumed.Add(f, new HashSet<string>()));
            existentialFunctions.Keys.Iter(f => function2implAsserted.Add(f, new HashSet<string>()));

            // type check
            existentialFunctions.Values.Iter(func =>
                {
                    if (func.OutParams.Count != 1 || !func.OutParams[0].TypedIdent.Type.IsBool)
                        throw new AbsHoudiniInternalError(string.Format("Existential function {0} must return bool", func.Name));
                    if(func.Body != null)
                        throw new AbsHoudiniInternalError(string.Format("Existential function {0} should not have a body", func.Name));
                    var args = new List<Type>();
                    func.InParams.Iter(v => args.Add(v.TypedIdent.Type));
                    string msg = "";
                    if (!function2Value[func.Name].TypeCheck(args, out msg))
                        throw new AbsHoudiniInternalError("TypeError: " + msg);
                });

            //if (CommandLineOptions.Clo.ProverKillTime > 0)
            //    CommandLineOptions.Clo.ProverOptions.Add(string.Format("TIME_LIMIT={0}", CommandLineOptions.Clo.ProverKillTime));

            Inline();

            this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, new List<Checker>());
            this.prover = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, CommandLineOptions.Clo.ProverKillTime);

            this.proverTime = TimeSpan.Zero;
            this.numProverQueries = 0;

            program.Implementations
                .Where(impl => !impl.SkipVerification)
                .Iter(impl => name2Impl.Add(impl.Name, impl));

            // Let's do VC Gen (and also build dependencies)
            name2Impl.Values.Iter(GenVC);
        }

        public VCGenOutcome ComputeSummaries()
        {
            var overallOutcome = new VCGenOutcome(ProverInterface.Outcome.Valid, new List<Counterexample>());

            // Compute SCCs and determine a priority order for impls
            var Succ = new Dictionary<string, HashSet<string>>();
            var Pred = new Dictionary<string, HashSet<string>>();
            name2Impl.Keys.Iter(s => Succ[s] = new HashSet<string>());
            name2Impl.Keys.Iter(s => Pred[s] = new HashSet<string>());

            foreach(var impl in name2Impl.Keys) {
                Succ[impl] = new HashSet<string>();
                impl2functionsAsserted[impl].Iter(f => 
                    function2implAssumed[f].Iter(succ =>
                        {
                            Succ[impl].Add(succ);
                            Pred[succ].Add(impl);
                        }));
            }

            var sccs = new StronglyConnectedComponents<string>(name2Impl.Keys,
                new Adjacency<string>(n => Pred[n]),
                new Adjacency<string>(n => Succ[n]));
            sccs.Compute();
            
            // impl -> priority
            var impl2Priority = new Dictionary<string, int>();
            int p = 0;
            foreach (var scc in sccs)
            {
                foreach (var impl in scc)
                {
                    impl2Priority.Add(impl, p);
                    p++;
                }
            }

            var worklist = new SortedSet<Tuple<int, string>>();
            name2Impl.Keys.Iter(k => worklist.Add(Tuple.Create(impl2Priority[k], k)));

            while (worklist.Any())
            {
                var impl = worklist.First().Item2;
                worklist.Remove(worklist.First());

                var gen = prover.VCExprGen;
                var terms = new List<Expr>();
                foreach (var tup in impl2FuncCalls[impl])
                {
                    var controlVar = tup.Item2;
                    var exprVars = tup.Item3;
                    var varList = new List<Expr>();
                    exprVars.Args.OfType<Expr>().Iter(v => varList.Add(v));
                    
                    var args = new List<Expr>();
                    controlVar.InParams.Iter(v => args.Add(Expr.Ident(v)));
                    Expr term = Expr.Eq(new NAryExpr(Token.NoToken, new FunctionCall(controlVar), args),
                                 function2Value[tup.Item1].Gamma(varList));

                    if (controlVar.InParams.Count != 0)
                    {
                        term = new ForallExpr(Token.NoToken, new List<Variable>(controlVar.InParams.ToArray()),
                            new Trigger(Token.NoToken, true, new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(controlVar), args) }),
                            term);
                    }
                    terms.Add(term);
                }
                var env = Expr.BinaryTreeAnd(terms);

                env.Typecheck(new TypecheckingContext((IErrorSink)null));
                var envVC = prover.Context.BoogieExprTranslator.Translate(env);

                var vc = gen.Implies(envVC, impl2VC[impl]);

                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("Verifying {0}: ", impl);
                    //Console.WriteLine("env: {0}", envVC);
                    var envFuncs = new HashSet<string>();
                    impl2FuncCalls[impl].Iter(tup => envFuncs.Add(tup.Item1));
                    envFuncs.Iter(f => PrintFunction(existentialFunctions[f]));
                }

                var handler = impl2ErrorHandler[impl].Item1;
                var collector = impl2ErrorHandler[impl].Item2;
                collector.Reset(impl);

                var start = DateTime.Now;

                prover.Push();
                prover.Assert(gen.Not(vc), true);
                prover.FlushAxiomsToTheoremProver();
                prover.Check();
                ProverInterface.Outcome proverOutcome = prover.CheckOutcomeCore(handler);

                //prover.BeginCheck(impl, vc, handler);
                //ProverInterface.Outcome proverOutcome = prover.CheckOutcomeCore(handler);

                var inc = (DateTime.Now - start);
                proverTime += inc;
                numProverQueries++;

                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Time taken = " + inc.TotalSeconds.ToString());

                if (proverOutcome == ProverInterface.Outcome.TimeOut || proverOutcome == ProverInterface.Outcome.OutOfMemory || proverOutcome == ProverInterface.Outcome.OutOfResource)
                {
                    // pick some function; make it true and keep going
                    bool changed = false;
                    foreach (var f in impl2functionsAsserted[impl])
                    {
                        function2Value[f] = function2Value[f].MakeTop(out changed);
                        if (changed) break;
                    }
                    if(!changed)
                        return new VCGenOutcome(proverOutcome, new List<Counterexample>());
                }

                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine(collector.numErrors > 0 ? "SAT" : "UNSAT");

                if (collector.numErrors > 0)
                {
                    var funcsChanged = collector.funcsChanged;
                    if (funcsChanged.Count == 0)
                    {
                        overallOutcome = new VCGenOutcome(ProverInterface.Outcome.Invalid, collector.errors);
                        break;
                    }

                    // propagate dependent guys back into the worklist, including self
                    var deps = new HashSet<string>();
                    deps.Add(impl);
                    funcsChanged.Iter(f => deps.UnionWith(function2implAssumed[f]));

                    deps.Iter(s => worklist.Add(Tuple.Create(impl2Priority[s], s)));
                }

                prover.Pop();
            }

            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Prover time = {0}", proverTime.TotalSeconds.ToString("F2"));
                Console.WriteLine("Number of prover queries = " + numProverQueries);
            }

            if (CommandLineOptions.Clo.PrintAssignment)
            {
                // Print the answer
                existentialFunctions.Values.Iter(PrintFunction);
            }

            return overallOutcome;
        }


        public IEnumerable<Function> GetAssignment()
        {
            var ret = new List<Function>();
            foreach (var func in existentialFunctions.Values)
            {
                var invars = new List<Expr>(func.InParams.OfType<Variable>().Select(v => Expr.Ident(v)));
                func.Body = function2Value[func.Name].Gamma(invars);
                ret.Add(func);
            }
            return ret;
        }

        private void PrintFunction(Function function)
        {
            var tt = new TokenTextWriter(Console.Out, /*pretty=*/ false);
            var invars = new List<Expr>(function.InParams.OfType<Variable>().Select(v => Expr.Ident(v)));
            function.Body = function2Value[function.Name].Gamma(invars);
            function.Emit(tt, 0);
            tt.Close();
        }

        public HashSet<string> HandleCounterExample(string impl, Counterexample error)
        {
            var funcsChanged = new HashSet<string>();
            // Find the failing assert -- need to do a join there
            // return the set of functions whose definition has changed
            var cex = ExtractState(impl, error);
            foreach (var tup in cex)
            {
                function2Value[tup.Item1] = function2Value[tup.Item1].Join(tup.Item2);
                funcsChanged.Add(tup.Item1);
            }
            return funcsChanged;
        }

        private List<Tuple<string, List<Model.Element>>> ExtractState(string impl, Counterexample error)
        {
            var lastBlock = error.Trace.Last() as Block;
            AssertCmd failingAssert = null;

            CallCounterexample callCounterexample = error as CallCounterexample;
            if (callCounterexample != null)
            {
                Procedure failingProcedure = callCounterexample.FailingCall.Proc;
                Requires failingRequires = callCounterexample.FailingRequires;
                failingAssert = lastBlock.Cmds.OfType<AssertRequiresCmd>().FirstOrDefault(ac => ac.Requires == failingRequires);
            }
            ReturnCounterexample returnCounterexample = error as ReturnCounterexample;
            if (returnCounterexample != null)
            {
                Ensures failingEnsures = returnCounterexample.FailingEnsures;
                failingAssert = lastBlock.Cmds.OfType<AssertEnsuresCmd>().FirstOrDefault(ac => ac.Ensures == failingEnsures);
            }
            AssertCounterexample assertCounterexample = error as AssertCounterexample;
            if (assertCounterexample != null)
            {
                failingAssert = lastBlock.Cmds.OfType<AssertCmd>().FirstOrDefault(ac => ac == assertCounterexample.FailingAssert);
            }

            Debug.Assert(failingAssert != null);
            return ExtractState(impl, failingAssert.Expr, error.Model);
        }

        private static int existentialConstCounter = 0;

        private List<Tuple<string, List<Model.Element>>> ExtractState(string impl, Expr expr, Model model)
        {
            var funcsUsed = FunctionCollector.Collect(expr);

            var ret = new List<Tuple<string, List<Model.Element>>>();

            foreach (var tup in funcsUsed.Where(t => t.Item2 == null))
            {
                var constant = tup.Item1;
                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                prover.Context.BoogieExprTranslator.Translate(func.Args).Iter(ve => vals.Add(getValue(ve, model)));
                ret.Add(Tuple.Create(funcName, vals));
            }

            foreach (var tup in funcsUsed.Where(t => t.Item2 != null))
            {
                var constant = tup.Item1;
                var boundExpr = tup.Item2;

                if (!constant2FuncCall.ContainsKey(constant.Name))
                    continue;

                // There are some bound variables (because the existential function was inside an \exists).
                // We must find an assignment for bound varibles 

                // First, peice apart the existential functions
                var cd = new Duplicator();
                var tup2 = ExistentialExprModelMassage.Massage(cd.VisitExpr(boundExpr.Body));
                var be = tup2.Item1;
                Expr env = Expr.True;
                foreach (var ahFunc in tup2.Item2)
                {
                    var tup3 = impl2FuncCalls[impl].First(t => t.Item2.Name == ahFunc.Name);
                    var varList = new List<Expr>();
                    tup3.Item3.Args.OfType<Expr>().Iter(v => varList.Add(v));

                    env = Expr.And(env, function2Value[tup3.Item1].Gamma(varList));
                }
                be = Expr.And(be, Expr.Not(env));

                // map formals to constants
                var formalToConstant = new Dictionary<string, Constant>();
                foreach (var f in boundExpr.Dummies.OfType<Variable>())
                    formalToConstant.Add(f.Name, new Constant(Token.NoToken, new TypedIdent(Token.NoToken, f.Name + "@subst@" + (existentialConstCounter++), f.TypedIdent.Type), false));
                be = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), be);
                formalToConstant.Values.Iter(v => prover.Context.DeclareConstant(v, false, null));

                var reporter = new AbstractHoudiniErrorReporter();
                var ve = prover.Context.BoogieExprTranslator.Translate(be);
                prover.Assert(ve, true);
                prover.Check();
                var proverOutcome = prover.CheckOutcomeCore(reporter);
                if (proverOutcome != ProverInterface.Outcome.Invalid)
                    continue;
                model = reporter.model;

                var func = constant2FuncCall[constant.Name];
                var funcName = (func.Fun as FunctionCall).FunctionName;
                var vals = new List<Model.Element>();
                foreach (var funcArg in func.Args.OfType<Expr>())
                {
                    var arg = Substituter.Apply(new Substitution(v => formalToConstant.ContainsKey(v.Name) ? Expr.Ident(formalToConstant[v.Name]) : Expr.Ident(v)), funcArg);
                    vals.Add(getValue(prover.Context.BoogieExprTranslator.Translate(arg), model));
                }
                ret.Add(Tuple.Create(funcName, vals));

            }

            return ret;
        }

        private Model.Element getValue(VCExpr arg, Model model)
        {


            if (arg is VCExprLiteral)
            {
                //return model.GetElement(arg.ToString());
                return model.MkElement(arg.ToString());
            }

            else if (arg is VCExprVar)
            {
                var el = model.TryGetFunc(prover.Context.Lookup(arg as VCExprVar));
                if (el != null)
                {
                    Debug.Assert(el.Arity == 0 && el.AppCount == 1);
                    return el.Apps.First().Result;
                }
                else
                {
                    // Variable not defined; assign arbitrary value
                    if (arg.Type.IsBool)
                        return model.MkElement("false");
                    else if (arg.Type.IsInt)
                        return model.MkIntElement(0);
                    else
                        return null;
                }
            }
            else if (arg is VCExprNAry && (arg as VCExprNAry).Op is VCExprBvOp)
            {
                // support for BV constants
                var bvc = (arg as VCExprNAry)[0] as VCExprLiteral;
                if (bvc != null)
                {
                    var ret = model.TryMkElement(bvc.ToString() + arg.Type.ToString());
                    if (ret != null && (ret is Model.BitVector)) return ret;
                }
            }

            object val;

            try
            {
                val = prover.Evaluate(arg);
            }
            catch (ProverInterface.VCExprEvaluationException)
            {
                Console.WriteLine("AbsHoudni: Error evaluating expression {0}", arg);
                throw;
            }

            if (val is int || val is bool || val is Microsoft.Basetypes.BigNum)
            {
                return model.MkElement(val.ToString());
            }
            else
            {
                Debug.Assert(false);
            }
            return null;
        }

        // Remove functions AbsHoudiniConstant from the expressions and substitute them with "true"
        class ExistentialExprModelMassage : StandardVisitor
        {
            List<Function> ahFuncs;

            public ExistentialExprModelMassage()
            {
                ahFuncs = new List<Function>();
            }

            public static Tuple<Expr, List<Function>> Massage(Expr expr)
            {
                var ee = new ExistentialExprModelMassage();
                expr = ee.VisitExpr(expr);
                return Tuple.Create(expr, ee.ahFuncs);
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall && (node.Fun as FunctionCall).FunctionName.StartsWith("AbsHoudiniConstant"))
                {
                    ahFuncs.Add((node.Fun as FunctionCall).Func);
                    return Expr.True;
                }

                return base.VisitNAryExpr(node);
            }
        }

        class FunctionCollector : ReadOnlyVisitor
        {
            public List<Tuple<Function, ExistsExpr>> functionsUsed;
            ExistsExpr existentialExpr;

            public FunctionCollector()
            {
                functionsUsed = new List<Tuple<Function, ExistsExpr>>();
                existentialExpr = null;
            }

            public static List<Tuple<Function, ExistsExpr>> Collect(Expr expr)
            {
                var fv = new FunctionCollector();
                fv.VisitExpr(expr);
                return fv.functionsUsed;
            }

            public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
            {
                var oldE = existentialExpr;

                if (node is ExistsExpr)
                    existentialExpr = (node as ExistsExpr);

                node = base.VisitQuantifierExpr(node);

                existentialExpr = oldE;
                return node;
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall)
                {
                    var collector = new VariableCollector();
                    collector.Visit(node);

                    if(existentialExpr != null && existentialExpr.Dummies.Intersect(collector.usedVars).Any())
                        functionsUsed.Add(Tuple.Create((node.Fun as FunctionCall).Func, existentialExpr));
                    else
                        functionsUsed.Add(Tuple.Create<Function, ExistsExpr>((node.Fun as FunctionCall).Func, null));
                }

                return base.VisitNAryExpr(node);
            }
        }

        class AbsHoudiniCounterexampleCollector : VerifierCallback
        {
            public HashSet<string> funcsChanged;
            public string currImpl;
            public int numErrors;
            public List<Counterexample> errors;

            AbsHoudini container;

            public AbsHoudiniCounterexampleCollector(AbsHoudini container)
            {
                this.container = container;
                Reset(null);
            }

            public void Reset(string impl)
            {
                funcsChanged = new HashSet<string>();
                currImpl = impl;
                numErrors = 0;
                errors = new List<Counterexample>();
            }

            public override void OnCounterexample(Counterexample ce, string reason)
            {
                numErrors++;
                errors.Add(ce);

                funcsChanged.UnionWith(
                    container.HandleCounterExample(currImpl, ce));
            }
        }

        private void GenVC(Implementation impl)
        {
            ModelViewInfo mvInfo;
            Dictionary<int, Absy> label2absy;
            var collector = new AbsHoudiniCounterexampleCollector(this);
            collector.OnProgress("HdnVCGen", 0, 0, 0.0);

            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Generating VC of {0}", impl.Name);
            }

            vcgen.ConvertCFG2DAG(impl);
            var gotoCmdOrigins = vcgen.PassifyImpl(impl, out mvInfo);

            // Inline functions
            (new InlineFunctionCalls()).VisitBlockList(impl.Blocks);

            
            StripOutermostForall(impl);
            //ExtractQuantifiedExprs(impl);
            ExtractBoolExprs(impl);

            //CommandLineOptions.Clo.PrintInstrumented = true;
            //using (var tt = new TokenTextWriter(Console.Out))
            //    impl.Emit(tt, 0);

            // Intercept the FunctionCalls of the existential functions, and replace them with Boolean constants
            var existentialFunctionNames = new HashSet<string>(existentialFunctions.Keys);
            var fv = new ReplaceFunctionCalls(existentialFunctionNames);
            fv.VisitBlockList(impl.Blocks);

            //using (var tt = new TokenTextWriter(Console.Out))
            //    impl.Emit(tt, 0);


            impl2functionsAsserted.Add(impl.Name, fv.functionsAsserted);
            impl2functionsAssumed.Add(impl.Name, fv.functionsAssumed);

            fv.functionsAssumed.Iter(f => function2implAssumed[f].Add(impl.Name));
            fv.functionsAsserted.Iter(f => function2implAsserted[f].Add(impl.Name));

            impl2FuncCalls.Add(impl.Name, fv.functionsUsed);
            fv.functionsUsed.Iter(tup => constant2FuncCall.Add(tup.Item2.Name, tup.Item3));

            var gen = prover.VCExprGen;
            VCExpr controlFlowVariableExpr = CommandLineOptions.Clo.UseLabels ? null : gen.Integer(Microsoft.Basetypes.BigNum.ZERO);

            var vcexpr = vcgen.GenerateVC(impl, controlFlowVariableExpr, out label2absy, prover.Context);
            if (!CommandLineOptions.Clo.UseLabels)
            {
                VCExpr controlFlowFunctionAppl = gen.ControlFlowFunctionApplication(gen.Integer(Microsoft.Basetypes.BigNum.ZERO), gen.Integer(Microsoft.Basetypes.BigNum.ZERO));
                VCExpr eqExpr = gen.Eq(controlFlowFunctionAppl, gen.Integer(Microsoft.Basetypes.BigNum.FromInt(impl.Blocks[0].UniqueId)));
                vcexpr = gen.Implies(eqExpr, vcexpr);
            }

            ProverInterface.ErrorHandler handler = null;
            if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Local)
                handler = new VCGen.ErrorReporterLocal(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, prover.Context, program);
            else
                handler = new VCGen.ErrorReporter(gotoCmdOrigins, label2absy, impl.Blocks, vcgen.incarnationOriginMap, collector, mvInfo, prover.Context, program);

            impl2ErrorHandler.Add(impl.Name, Tuple.Create(handler, collector));

            //Console.WriteLine("VC of {0}: {1}", impl.Name, vcexpr);

            // Create a macro so that the VC can sit with the theorem prover
            Macro macro = new Macro(Token.NoToken, impl.Name + "Macro", new List<Variable>(), new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false));
            prover.DefineMacro(macro, vcexpr);

            // Store VC
            impl2VC.Add(impl.Name, gen.Function(macro));

            // HACK: push the definitions of constants involved in function calls
            // It is possible that some constants only appear in function calls. Thus, when
            // they are replaced by Boolean constants, it is possible that (get-value) will 
            // fail if the expression involves such constants. All we need to do is make sure
            // these constants are declared, because otherwise, semantically we are doing
            // the right thing.
            foreach (var tup in fv.functionsUsed)
            {
                // Ignore ones with bound varibles
                if (tup.Item2.InParams.Count > 0) continue;
                var tt = prover.Context.BoogieExprTranslator.Translate(tup.Item3);
                tt = prover.VCExprGen.Or(VCExpressionGenerator.True, tt);
                prover.Assert(tt, true);
            }
        }

        // convert "foo(... forall e ...) to:
        //    (p iff forall e) ==> foo(... p ...) 
        // where p is a fresh boolean variable and foo is an existential constant
        private void ExtractQuantifiedExprs(Implementation impl)
        {
            var funcs = new HashSet<string>(existentialFunctions.Keys);
            foreach (var blk in impl.Blocks)
            {
                foreach (var acmd in blk.Cmds.OfType<AssertCmd>())
                {
                    var ret = ExtractQuantifiers.Extract(acmd.Expr, funcs);
                    acmd.Expr = ret.Item1;
                    impl.LocVars.AddRange(ret.Item2);
                }
            }
        }

        // convert "foo(... e ...) to:
        //    (p iff e) ==> foo(... p ...) 
        // where p is a fresh boolean variable, foo is an existential constant
        // and e is a Boolean-typed argument of foo
        private void ExtractBoolExprs(Implementation impl)
        {
            var funcs = new HashSet<string>(existentialFunctions.Keys);
            foreach (var blk in impl.Blocks)
            {
                foreach (var acmd in blk.Cmds.OfType<AssertCmd>())
                {
                    var ret = ExtractBoolArgs.Extract(acmd.Expr, funcs);
                    acmd.Expr = ret.Item1;
                    impl.LocVars.AddRange(ret.Item2);
                }
            }
        }

        // convert "assert e1 && forall x: e2" to
        //    assert e1 && e2[x <- x@bound]
        private void StripOutermostForall(Implementation impl)
        {
            var funcs = new HashSet<string>(existentialFunctions.Keys);
            foreach (var blk in impl.Blocks)
            {
                foreach (var acmd in blk.Cmds.OfType<AssertCmd>())
                {
                    var ret = StripQuantifiers.Run(acmd.Expr, funcs);
                    acmd.Expr = ret.Item1;
                    impl.LocVars.AddRange(ret.Item2);
                }
            }
        }

        private void Inline()
        {
            if (CommandLineOptions.Clo.InlineDepth < 0)
                return;

            var callGraph = BuildCallGraph();

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
            foreach (var proc in program.Procedures)
            {
                procToImpls[proc] = new HashSet<Implementation>();
            }
            foreach (var impl in program.Implementations)
            {
                if (impl.SkipVerification) continue;
                callGraph.AddSource(impl);
                procToImpls[impl.Proc].Add(impl);
            }
            foreach (var impl in program.Implementations)
            {
                if (impl.SkipVerification) continue;
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

    }

    class InlineFunctionCalls : StandardVisitor
    {
        public Stack<string> inlinedFunctionsStack;

        public InlineFunctionCalls()
        {
            inlinedFunctionsStack = new Stack<string>();
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            var fc = node.Fun as FunctionCall;
            if (fc != null && fc.Func.Body != null && QKeyValue.FindBoolAttribute(fc.Func.Attributes, "inline"))
            {
                if (inlinedFunctionsStack.Contains(fc.Func.Name))
                {
                    // recursion detected
                    throw new AbsHoudiniInternalError("Recursion detected in function declarations");
                }

                // create a substitution
                var subst = new Dictionary<Variable, Expr>();
                for (int i = 0; i < node.Args.Count; i++)
                {
                    subst.Add(fc.Func.InParams[i], node.Args[i]);
                }

                var e =
                    Substituter.Apply(new Substitution(v => subst.ContainsKey(v) ? subst[v] : Expr.Ident(v)), fc.Func.Body);

                inlinedFunctionsStack.Push(fc.Func.Name);

                e = base.VisitExpr(e);

                inlinedFunctionsStack.Pop();

                return e;
            }
            return base.VisitNAryExpr(node);
        }
    }

    class ReplaceFunctionCalls : StandardVisitor
    {
        public List<Tuple<string, Function, NAryExpr>> functionsUsed;
        public List<Function> boolConstants;

        public HashSet<string> functionsAssumed;
        public HashSet<string> functionsAsserted;
        HashSet<string> functionsToReplace;

        private bool inAssume;
        private bool inAssert;
        private bool inFunction;
        private List<Dictionary<string, Variable>> boundVars;
        private static int IdCounter = 0;

        public ReplaceFunctionCalls(HashSet<string> functionsToReplace)
        {
            this.functionsUsed = new List<Tuple<string, Function, NAryExpr>>();
            this.functionsToReplace = functionsToReplace;
            this.functionsAsserted = new HashSet<string>();
            this.functionsAssumed = new HashSet<string>();
            this.boolConstants = new List<Function>();
            this.boundVars = new List<Dictionary<string, Variable>>();

            inAssume = false;
            inAssert = false;
            inFunction = false;
        }

        public override Cmd VisitAssertCmd(AssertCmd node)
        {
            inAssert = true;
            var ret = base.VisitAssertCmd(node);
            inAssert = false;
            return ret;
        }

        public override Cmd VisitAssertEnsuresCmd(AssertEnsuresCmd node)
        {
            return this.VisitAssertCmd(node);
        }

        public override Cmd VisitAssertRequiresCmd(AssertRequiresCmd node)
        {
            return this.VisitAssertCmd(node);
        }

        public override Cmd VisitAssumeCmd(AssumeCmd node)
        {
            inAssume = true;
            var ret = base.VisitAssumeCmd(node);
            inAssume = false;
            return ret;
        }

        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            // gather the quantified variables
            var dummies = new Dictionary<string, Variable>();
            node.Dummies.Iter(v => dummies.Add(v.Name, v));

            boundVars.Add(dummies);

            node = base.VisitQuantifierExpr(node);

            boundVars.RemoveAt(boundVars.Count - 1);

            return node;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            var inF = inFunction;

            if (node.Fun is FunctionCall && functionsToReplace.Contains((node.Fun as FunctionCall).FunctionName))
            {                
                found((node.Fun as FunctionCall).FunctionName);
                inFunction = true;

                // collect all the variables used by this function
                var collector = new VariableCollector();
                collector.VisitExpr(node);

                // Find the outermost bound variables
                var bound = new List<Variable>();
                if(boundVars.Count > 0) 
                    bound.AddRange(collector.usedVars.Intersect(boundVars[0].Values));

                // create boolean function to replace this guy
                var constant = new Function(Token.NoToken, "AbsHoudiniConstant" + IdCounter, bound,
                    new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "r", Microsoft.Boogie.Type.Bool), false));
                IdCounter++;
                
                functionsUsed.Add(Tuple.Create((node.Fun as FunctionCall).FunctionName, constant, node));
                boolConstants.Add(constant);

                var args = new List<Expr>();
                bound.OfType<Variable>().Select(v => Expr.Ident(v)).Iter(v => args.Add(v));
                return new NAryExpr(Token.NoToken, new FunctionCall(constant), args);
            }
            var ret = base.VisitNAryExpr(node);

            inFunction = inF;

            return ret;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (inFunction)
            {
                // Inside functions we can only refer to the outermost bound variables
                for (int i = boundVars.Count - 1; i >= 1; i--)
                {
                    if (boundVars[i].ContainsKey(node.Name))
                        throw new AbsHoudiniInternalError("Existential functions can only refer to outermost bound variables in an expression");
                }
            }

            return base.VisitIdentifierExpr(node);
        }

        private void found(string func)
        {
            if (inAssume) functionsAssumed.Add(func);
            if (inAssert) functionsAsserted.Add(func);
        }

    }

    // convert "foo(... e ...) to:
    //    (p iff e) ==> foo(... p ...) 
    // where p is a fresh boolean variable, foo is an existential constant
    // and e is a Boolean-typed argument of foo
    class ExtractBoolArgs : StandardVisitor
    {
        static int freshConstCounter = 0;
        HashSet<string> existentialFunctions;
        HashSet<Constant> newConstants;

        private ExtractBoolArgs(HashSet<string> existentialFunctions)
        {
            this.existentialFunctions = existentialFunctions;
            this.newConstants = new HashSet<Constant>();
        }

        public static Tuple<Expr, IEnumerable<Constant>> Extract(Expr expr, HashSet<string> existentialFunctions)
        {
            var eq = new ExtractBoolArgs(existentialFunctions);
            expr = eq.VisitExpr(expr);
            return Tuple.Create(expr, eq.newConstants.AsEnumerable());
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is FunctionCall && existentialFunctions.Contains((node.Fun as FunctionCall).FunctionName))
            {
                var constants = new Dictionary<Constant, Expr>();
                for (int i = 0; i < node.Args.Count; i++)
                {
                    if (node.Args[i].Type == Type.Bool)
                    {
                        var constant = new Constant(Token.NoToken, new TypedIdent(Token.NoToken,
                            "boolArg@const" + freshConstCounter, Microsoft.Boogie.Type.Bool), false);
                        freshConstCounter++;
                        constants.Add(constant, node.Args[i]);
                        node.Args[i] = Expr.Ident(constant);
                    }
                }

                newConstants.UnionWith(constants.Keys);

                Expr ret = Expr.True;
                foreach (var tup in constants)
                {
                    ret = Expr.And(ret, Expr.Eq(Expr.Ident(tup.Key), tup.Value));
                }
                return Expr.Imp(ret, node);
            } 

            return base.VisitNAryExpr(node);
        }
    }


    // convert "foo(... forall e ...) to:
    //    (p iff forall e) ==> foo(... p ...) 
    // where p is a fresh boolean variable and foo is an existential constant
    class ExtractQuantifiers : StandardVisitor
    {
        static int freshConstCounter = 0;
        HashSet<string> existentialFunctions;
        bool insideExistential;
        Dictionary<Constant, Expr> newConstants;

        private ExtractQuantifiers(HashSet<string> existentialFunctions)
        {
            this.existentialFunctions = existentialFunctions;
            insideExistential = false;
            newConstants = new Dictionary<Constant, Expr>();
        }

        public static Tuple<Expr, IEnumerable<Constant>> Extract(Expr expr, HashSet<string> existentialFunctions)
        {
            var eq = new ExtractQuantifiers(existentialFunctions);
            expr = eq.VisitExpr(expr);
            Expr ret = Expr.True;
            foreach (var tup in eq.newConstants)
            {
                ret = Expr.And(ret, Expr.Eq(Expr.Ident(tup.Key), tup.Value));
            }
            ret = Expr.Imp(ret, expr);
            return Tuple.Create(ret, eq.newConstants.Keys.AsEnumerable());
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            var oldIE = insideExistential;

            if (node.Fun is FunctionCall && existentialFunctions.Contains((node.Fun as FunctionCall).FunctionName))
                insideExistential = true;

            var ret = base.VisitNAryExpr(node);

            insideExistential = oldIE;
            return ret;
        }

        public override Expr VisitExpr(Expr node)
        {
            if (node is QuantifierExpr)
            {
                return MyVisitQuantifierExpr(node as QuantifierExpr);
            }
            return base.VisitExpr(node);
        }

        public Expr MyVisitQuantifierExpr(QuantifierExpr node)
        {
            node = base.VisitQuantifierExpr(node);

            if (insideExistential)
            {
                var constant = new Constant(Token.NoToken, new TypedIdent(Token.NoToken,
                    "quant@const" + freshConstCounter, Microsoft.Boogie.Type.Bool), false);
                freshConstCounter++;

                newConstants.Add(constant, node);

                return Expr.Ident(constant);                
            }

            return node;
        }
    }

    // convert "assert e1 && forall x: e2" to
    //    assert e1 && e2[x <- x@bound]
    // only if e2 has an existential function
    class StripQuantifiers : StandardVisitor
    {
        static int boundVarCounter = 0;
        
        // 0 -> None, 1 -> Forall, 2 -> Exists, 3 -> Nested
        int insideQuantifier; 

        bool searchExistentialFunction;
        bool foundExistentialFunction;

        HashSet<string> existentialFunctions;
        Dictionary<string, LocalVariable> subst;
        List<LocalVariable> LocalsToAdd;

        private StripQuantifiers(HashSet<string> existentialFunctions)
        {
            this.existentialFunctions = existentialFunctions;
            insideQuantifier = 0;
            searchExistentialFunction = false;
            foundExistentialFunction = false;
            LocalsToAdd = new List<LocalVariable>();
            subst = null;
        }

        public static Tuple<Expr,List<LocalVariable>> Run(Expr expr, HashSet<string> existentialFunctions)
        {
            // check for type errors first
            var sq = new StripQuantifiers(existentialFunctions);
            var ret = sq.VisitExpr(expr);

            return Tuple.Create(ret, sq.LocalsToAdd);
        }

        public override Expr VisitExpr(Expr node)
        {
            if (node is QuantifierExpr)
            {
                return MyVisitQuantifierExpr(node as QuantifierExpr);
            }

            return base.VisitExpr(node);
        }

        private Expr MyVisitQuantifierExpr(QuantifierExpr node)
        {
            var oldIQ = insideQuantifier;
            Expr ret = node;

            // update "insideQuantifier"
            if (insideQuantifier == 0)
            {
                if (node is ForallExpr) insideQuantifier = 1;
                else insideQuantifier = 2;
            }
            else if (insideQuantifier > 0)
            {
                insideQuantifier = 3;
            }

            // Going inside Forall?
            if (insideQuantifier == 1)
            {
                // see if there is any existential function inside
                searchExistentialFunction = true;
                foundExistentialFunction = false;
                base.VisitQuantifierExpr(node);

                if (foundExistentialFunction)
                {
                    // create substitution to apply
                    subst = new Dictionary<string, LocalVariable>();
                    foreach (var bv in node.Dummies.OfType<Variable>())
                    {
                        var lv = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken,
                            bv + "@bound" + boundVarCounter, bv.TypedIdent.Type));
                        boundVarCounter++;
                        subst.Add(bv.Name, lv);
                        LocalsToAdd.Add(lv);
                    }

                    // apply the subst
                    var body = base.VisitExpr(node.Body);
                    ret = body;

                    subst = null;
                }
                else
                {
                    ret = base.VisitQuantifierExpr(node);
                }

                searchExistentialFunction = false;
                foundExistentialFunction = false;
            }
            else
            {
                ret = base.VisitQuantifierExpr(node);
            }

            insideQuantifier = oldIQ;
            return ret;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is FunctionCall && existentialFunctions.Contains((node.Fun as FunctionCall).FunctionName))
            {
                if (insideQuantifier == 3)
                    throw new AbsHoudiniInternalError("Existential function found inside exists, or nested foralls");

                if (searchExistentialFunction)
                    foundExistentialFunction = true;

            }

            return base.VisitNAryExpr(node);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (subst != null && subst.ContainsKey(node.Name))
                return Expr.Ident(subst[node.Name]);
            return base.VisitIdentifierExpr(node);
        }

    }

    public class Intervals : IAbstractDomain
    {
        // [lower, upper]
        int upper;
        int lower;
        // or: \bot
        bool isBottom;
        // number of times join has been performed
        int nJoin;
        // number of times before we widen
        readonly static int maxJoin = 5;

        public Intervals()
        {
            this.upper = 0;
            this.lower = 0;
            this.nJoin = 0;
            this.isBottom = true;
        }

        private Intervals(int lower, int upper, int nJoin)
        {
            this.upper = upper;
            this.lower = lower;
            this.nJoin = nJoin;
        }

        public IAbstractDomain Bottom()
        {
            return new Intervals();
        }

        public IAbstractDomain MakeTop(out bool changed)
        {
            if (lower == Int32.MinValue && upper == Int32.MaxValue)
            {
                changed = false;
                return this;
            }
            changed = true;
            return new Intervals(Int32.MinValue, Int32.MaxValue, 0);
        }

        public IAbstractDomain Join(List<Model.Element> states)
        {
            Debug.Assert(states.Count == 1);
            var state = states[0] as Model.Integer;
            if (state == null)
                throw new AbsHoudiniInternalError("Incorrect type, expected int");
            var intval = state.AsInt();

            if (isBottom)
            {
                return new Intervals(intval, intval, 1);
            }

            if(intval >= lower && intval <= upper)
                return this;

            if (nJoin > maxJoin)
            {
                // widen
                if (intval > upper)
                    return new Intervals(lower, Int32.MaxValue, 1);
                if(intval < lower)
                    return new Intervals(Int32.MinValue, upper, 1);

                Debug.Assert(false);
            }

            if (intval > upper)
                return new Intervals(lower, intval, nJoin + 1);
            if (intval < lower)
                return new Intervals(intval, upper, nJoin + 1);

            Debug.Assert(false);
            return null;
        }

        public Expr Gamma(List<Expr> vars)
        {
            Debug.Assert(vars.Count == 1);
            var v = vars[0];
            if (isBottom) return Expr.False;
            Expr ret = Expr.True;
            if (lower != Int32.MinValue)
                ret = Expr.And(ret, Expr.Ge(v, Expr.Literal(lower)));
            if (upper != Int32.MaxValue)
                ret = Expr.And(ret, Expr.Le(v, Expr.Literal(upper)));
            return ret;
        }

        public bool TypeCheck(List<Type> argTypes, out string msg)
        {
            msg = "";
            if (argTypes.Count != 1)
            {
                msg = "Illegal number of arguments";
                return false;
            }
            if (!argTypes[0].IsInt)
            {
                msg = "Illegal type, expecting int";
                return false;
            }
            return true;
        }
    }

    public class PredicateAbsFullElem : PredicateAbsElem
    {
        public PredicateAbsFullElem()
            : base(1000)
        { }
    }

    public class PredicateAbsElem : IAbstractDomain
    {
        public static class ExprExt
        {
            public static Expr AndSimp(Expr e1, Expr e2)
            {
                if (e1 == Expr.True) return e2;
                if (e2 == Expr.True) return e1;
                if (e1 == Expr.False || e2 == Expr.False) return Expr.False;
                return Expr.And(e1, e2);
            }

            public static Expr OrSimp(Expr e1, Expr e2)
            {
                if (e1 == Expr.False) return e2;
                if (e2 == Expr.False) return e1;
                if (e1 == Expr.True || e2 == Expr.True) return Expr.True;
                return Expr.Or(e1, e2); 
            }
        }

        class Disjunct
        {
            HashSet<int> pos;
            HashSet<int> neg;
            bool isTrue;

            public Disjunct()
            {
                isTrue = true;
                pos = new HashSet<int>();
                neg = new HashSet<int>();
            }

            public Disjunct(IEnumerable<int> pos, IEnumerable<int> neg, int bound)
            {
                this.isTrue = false;
                this.pos = new HashSet<int>(pos);
                this.neg = new HashSet<int>(neg);
                if (this.pos.Overlaps(this.neg))
                {
                    this.isTrue = true;
                    this.pos = new HashSet<int>();
                    this.neg = new HashSet<int>();
                }
                if (this.pos.Count + this.neg.Count > bound)
                {
                    // Set to true
                    this.isTrue = true;
                    this.pos = new HashSet<int>();
                    this.neg = new HashSet<int>();
                }

            }

            public Disjunct OR(Disjunct that, int bound)
            {
                if (isTrue)
                    return this;
                if (that.isTrue)
                    return that;

                return new Disjunct(this.pos.Concat(that.pos), this.neg.Concat(that.neg), bound);
            }

            public bool Implies(Disjunct that)
            {
                if (isTrue) return that.isTrue;
                if (that.isTrue) return true;

                return pos.IsSubsetOf(that.pos) && neg.IsSubsetOf(that.neg);
            }

            public Expr Gamma(List<Expr> vars)
            {
                if (isTrue) return Expr.True;
                Expr ret = Expr.False;
                pos.Iter(i => ret = ExprExt.OrSimp(ret, vars[i]));
                neg.Iter(i => ret = ExprExt.OrSimp(ret, Expr.Not(vars[i])));
                return ret;
            }
        }

        // Conjunction of Disjuncts
        List<Disjunct> conjuncts;
        int DisjunctBound;
        bool isFalse;

        public PredicateAbsElem()
        {
            this.conjuncts = new List<Disjunct>();
            this.isFalse = true;
            this.DisjunctBound = 3;
        }

        public PredicateAbsElem(int bound)
        {
            this.conjuncts = new List<Disjunct>();
            this.isFalse = true;
            this.DisjunctBound = bound;
        }

        public IAbstractDomain Bottom()
        {
            return new PredicateAbsElem(DisjunctBound);
        }

        public IAbstractDomain MakeTop(out bool changed)
        {
            if (conjuncts.Count == 0)
            {
                changed = false;
                return this;
            }
            changed = true;
            var ret = new PredicateAbsElem(DisjunctBound);
            ret.isFalse = false;
            return ret;
        }

        public IAbstractDomain Join(List<Model.Element> state)
        {
            if (state.Any(me => !(me is Model.Boolean)))
                throw new AbsHoudiniInternalError("Predicate Abstraction requires that each argument be of type bool");

            // quick return if this == true
            if (!this.isFalse && conjuncts.Count == 0)
                return this;

            var ret = new PredicateAbsElem(DisjunctBound);
            ret.isFalse = false;

            for (int i = 0; i < state.Count; i++)
            {
                var b = (state[i] as Model.Boolean).Value;
                Disjunct d = null;
                if (b) d = new Disjunct(new int[] { i }, new int[] { }, DisjunctBound);
                else d = new Disjunct(new int[] { }, new int[] { i }, DisjunctBound);

                if (isFalse)
                    ret.AddDisjunct(d);
                else
                {
                    conjuncts.Iter(c => ret.AddDisjunct(c.OR(d, DisjunctBound)));
                }
            }

            return ret;

        }

        public Expr Gamma(List<Expr> vars)
        {
            if (isFalse) return Expr.False;
            Expr ret = Expr.True;

            foreach (var c in conjuncts)
            {
                ret = ExprExt.AndSimp(ret, c.Gamma(vars));
            }

            return ret;
        }

        public bool TypeCheck(List<Type> argTypes, out string msg)
        {
            msg = "";
            if (argTypes.Any(t => !t.IsBool))
            {
                msg = "Illegal type, expecting bool";
                return false;
            }
            return true;
        }

        private void AddDisjunct(Disjunct d)
        {
            if (conjuncts.Any(c => c.Implies(d)))
                return;

            conjuncts.RemoveAll(c => d.Implies(c));
            conjuncts.Add(d);
        }
    }

    // [false -- (x == true) -- true]
    public class HoudiniConst : IAbstractDomain
    {
        bool isBottom;
        bool isTop;

        private HoudiniConst(bool isTop, bool isBottom)
        {
            this.isBottom = isBottom;
            this.isTop = isTop;
            Debug.Assert(!(isTop && isBottom));
        }

        public static HoudiniConst GetExtObj()
        {
            return new HoudiniConst(false, false);
        }

        public static HoudiniConst GetTop()
        {
            return new HoudiniConst(true, false);
        }

        public static HoudiniConst GetBottom()
        {
            return new HoudiniConst(false, true);
        }

        public IAbstractDomain Bottom()
        {
            return GetBottom();
        }

        public IAbstractDomain MakeTop(out bool changed)
        {
            changed = false;
            if (isTop) return this;
            changed = true;
            return GetTop();
        }

        public IAbstractDomain Join(List<Model.Element> states)
        {
            Debug.Assert(states.Count == 1);
            var state = states[0];

            if (isTop) return this;

            if (state is Model.Boolean)
            {
                if ((state as Model.Boolean).Value)
                    return GetExtObj();
            }

            return GetTop();
        }

        public Expr Gamma(List<Expr> vars)
        {
            Debug.Assert(vars.Count == 1);
            var v = vars[0];
            if (isBottom) return Expr.False;
            if (isTop) return Expr.True;
            return v;
        }

        public bool TypeCheck(List<Type> argTypes, out string msg)
        {
            msg = "";
            if (argTypes.Count != 1)
            {
                msg = "Illegal number of arguments, expecting 1";
                return false;
            }
            if (!argTypes[0].IsBool)
            {
                msg = "Illegal type, expecting bool";
                return false;
            }
            return true;
        }
    }

    // foo(x) = x < 2^j for some j <= 16
    public class PowDomain : IAbstractDomain
    {
        enum Val { FALSE, NEITHER, TRUE };
        Val tlevel;
        bool isBottom { get { return tlevel == Val.FALSE; } }
        bool isTop { get { return tlevel == Val.TRUE; } }

        readonly int Max = 16;

        int upper; // <= Max

        private PowDomain(Val tlevel) :
            this(tlevel, 0) { }

        private PowDomain(Val tlevel, int upper)
        {
            this.tlevel = tlevel;
            this.upper = upper;
        }

        public static IAbstractDomain GetBottom()
        {
            return new PowDomain(Val.FALSE) as IAbstractDomain;
        }

        public IAbstractDomain MakeTop(out bool changed)
        {
            if (isTop)
            {
                changed = false;
                return this;
            }
            changed = true;
            return new PowDomain(Val.TRUE);
        }

        IAbstractDomain IAbstractDomain.Bottom()
        {
            return GetBottom();
        }

        IAbstractDomain IAbstractDomain.Join(List<Model.Element> state)
        {
            if (isTop) return this;
            
            int v = 0;
            if (state[0] is Model.BitVector)
                v = (state[0] as Model.BitVector).AsInt();
            else if (state[0] is Model.Integer)
                v = (state[0] as Model.Integer).AsInt();
            else Debug.Assert(false);

            var nupper = upper;
            while ((1 << nupper) < v) nupper++;
            var ntlevel = Val.NEITHER;
            if (nupper > Max) ntlevel = Val.TRUE;
            return new PowDomain(ntlevel, nupper);
        }

        Expr IAbstractDomain.Gamma(List<Expr> vars)
        {
            if (isBottom) return Expr.False;
            if (isTop) return Expr.True;
            var v = vars[0];
            if (v.Type.IsBv)
            {
                var bits = v.Type.BvBits;
                if (!AbstractDomainFactory.bvslt.ContainsKey(bits))
                    throw new AbsHoudiniInternalError("No builtin function found for bv" + bits.ToString());
                var bvslt = AbstractDomainFactory.bvslt[bits];
                return new NAryExpr(Token.NoToken, new FunctionCall(bvslt), new List<Expr> { v,
                    new LiteralExpr(Token.NoToken, Basetypes.BigNum.FromInt(1 << (upper+1)), 32) });
            }
            else
            {
                return Expr.Lt(v, Expr.Literal(1 << (upper+1)));
            }
        }

        bool IAbstractDomain.TypeCheck(List<Type> argTypes, out string msg)
        {
            msg = "";
            if (argTypes.Count != 1)
            {
                msg = "Illegal number of arguments, expecting 1";
                return false;
            }
            if (argTypes.Any(tt => !tt.IsInt && !tt.IsBv))
            {
                msg = "Illegal type, expecting int or bv";
                return false;
            }
            return true;
        }
    }

    // foo(x_i) = all equalities that hold
    public class EqualitiesDomain : IAbstractDomain
    {
        bool isBottom;
        List<HashSet<int>> equalities;

        public EqualitiesDomain(bool isBottom, List<HashSet<int>> eq)
        {
            this.isBottom = isBottom;
            this.equalities = eq;
        }

        public static IAbstractDomain GetBottom()
        {
            return new EqualitiesDomain(true, new List<HashSet<int>>());
        }

        IAbstractDomain IAbstractDomain.Bottom()
        {
            return GetBottom();
        }

        public IAbstractDomain MakeTop(out bool changed)
        {
            if (equalities.Count == 0)
            {
                changed = false;
                return this;
            }
            changed = true;
            return new EqualitiesDomain(false, new List<HashSet<int>>());
        }

        IAbstractDomain IAbstractDomain.Join(List<Model.Element> state)
        {
            // find the guys that are equal
            var eq = new List<HashSet<int>>();
            for (int i = 0; i < state.Count; i++)
            {
                var added = false;
                foreach (var s in eq)
                {
                    var sv = s.First();
                    if (state[i].ToString() == state[sv].ToString())
                    {
                        s.Add(i);
                        added = true;
                        break;
                    }
                }
                if (!added) eq.Add(new HashSet<int>(new int[] { i }));
            }
            
            if (isBottom)
            {
                return new EqualitiesDomain(false, eq);
            }

            // intersect two partitions equalities and eq
            var m1 = GetMap(equalities, state.Count);
            var m2 = GetMap(eq, state.Count);

            for (int i = 0; i < state.Count; i++)
                m2[i] = new HashSet<int>(m2[i].Intersect(m1[i]));


            // map from representative to set
            var repToSet = new Dictionary<int, HashSet<int>>();

            for (int i = 0; i < state.Count; i++)
            {
                var rep = m2[i].Min();
                if (!repToSet.ContainsKey(rep))
                    repToSet[rep] = m2[i];
            }

            var ret = new List<HashSet<int>>();
            repToSet.Values.Iter(s => ret.Add(s));

            return new EqualitiesDomain(false, ret);
        }

        Expr IAbstractDomain.Gamma(List<Expr> vars)
        {
            if (isBottom) return Expr.False;
            Expr ret = Expr.True;
            foreach (var eq in equalities.Select(hs => hs.ToList()))
            {
                if (eq.Count == 1) continue;
                var prev = eq[0];
                for (int i = 1; i < eq.Count; i++)
                {
                    ret = Expr.And(ret, Expr.Eq(vars[prev], vars[eq[i]]));
                    prev = eq[i];
                }
            }
            return ret;
        }

        bool IAbstractDomain.TypeCheck(List<Type> argTypes, out string msg)
        {
            msg = "";
            if (argTypes.Count == 0) return true;
            var ot = argTypes[0];

            if (argTypes.Any(tt => !tt.Equals(ot)))
            {
                msg = string.Format("Illegal type, expecting type {0}, got {1}", ot, argTypes.First(tt => !tt.Equals(ot)));
                return false;
            }
            return true;
        }

        private HashSet<int>[] GetMap(List<HashSet<int>> eq, int n)
        {
            var ret = new HashSet<int>[n];
            foreach (var s in eq)
            {
                foreach (var i in s)
                    ret[i] = s;
            }
            return ret;
        }
    }

    // foo(a,b) \in {false, \not a, a ==> b, true}
    public class ImplicationDomain : IAbstractDomain
    {
        enum Val {FALSE, NOT_A, A_IMP_B, TRUE};
        Val val;

        private ImplicationDomain(Val val)
        {
            this.val = val;
        }

        public static ImplicationDomain GetBottom()
        {
            return new ImplicationDomain(Val.FALSE);
        }

        public IAbstractDomain Bottom()
        {
            return GetBottom();
        }

        public IAbstractDomain MakeTop(out bool changed)
        {
            if(val == Val.TRUE) {
                changed = false;
                return this;
            }
            changed = true;
            return new ImplicationDomain(Val.TRUE);
        }

        public IAbstractDomain Join(List<Model.Element> states)
        {
            Debug.Assert(states.Count == 2);
            var v1 = (states[0] as Model.Boolean).Value;
            var v2 = (states[1] as Model.Boolean).Value;

            if (val == Val.TRUE) return this;

            var that = Val.TRUE;
            if (!v1) that = Val.NOT_A;
            else if (!v1 || v2) that = Val.A_IMP_B;

            if (that == Val.TRUE || val == Val.FALSE)
                return new ImplicationDomain(that);

            // Now, neither this or that is FALSE or TRUE
            if (val == that)
                return this;

            Debug.Assert(val == Val.A_IMP_B || that == Val.A_IMP_B);
            return new ImplicationDomain(Val.A_IMP_B);
        }

        public Expr Gamma(List<Expr> vars)
        {
            Debug.Assert(vars.Count == 2);

            var v1 = vars[0];
            var v2 = vars[1];

            if (val == Val.FALSE) return Expr.False;
            if (val == Val.TRUE) return Expr.True;
            if (val == Val.NOT_A) return Expr.Not(v1);
            return Expr.Imp(v1, v2);
        }

        public bool TypeCheck(List<Type> argTypes, out string msg)
        {
            msg = "";
            if (argTypes.Count != 2)
            {
                msg = "Illegal number of arguments, expecting 2";
                return false;
            }
            if (argTypes.Any(tt => !tt.IsBool))
            {
                msg = "Illegal type, expecting bool";
                return false;
            }
            return true;
        }
    }

    public class ConstantProp : IAbstractDomain
    {
        object val;
        bool isBottom;
        bool isTop;

        private ConstantProp(object val, bool isTop, bool isBottom)
        {
            this.val = val;
            this.isBottom = isBottom;
            this.isTop = isTop;
            Debug.Assert(!(isTop && isBottom));
            Debug.Assert(val == null || (val is int) || (val is bool));
        }

        public static ConstantProp GetExtObj(object val)
        {
            Debug.Assert(val != null);
            return new ConstantProp(val, false, false);
        }

        public static ConstantProp GetTop()
        {
            return new ConstantProp(null, true, false);
        }

        public static ConstantProp GetBottom()
        {
            return new ConstantProp(null, false, true);
        }

        public IAbstractDomain MakeTop(out bool changed) {
            if (isTop)
            {
                changed = false;
                return this;
            }
            changed = true;
            return GetTop();
        }

        private ConstantProp Join(ConstantProp that)
        {
            if (isBottom) return that;
            if (isTop) return this;
            if (that.isBottom) return this;
            if (that.isTop) return that;

            if ((val is int) && !(that.val is int))
                throw new AbsHoudiniInternalError("Type mismatch in ExtObj");

            if ((val is bool) && !(that.val is bool))
                throw new AbsHoudiniInternalError("Type mismatch in ExtObj");

            if (val is int)
            {
                var v1 = (int)val;
                var v2 = (int)that.val;
                if (v1 != v2) return GetTop();
                return this;
            }
            else if (val is bool)
            {
                var v1 = (bool)val;
                var v2 = (bool)that.val;
                if (v1 != v2) return GetTop();
                return this;
            }
            throw new AbsHoudiniInternalError("Illegal val type in ExtObj");
        }

        public IAbstractDomain Bottom()
        {
            return GetBottom();
        }

        public IAbstractDomain Join(List<Model.Element> states)
        {
            Debug.Assert(states.Count == 1);
            var state = states[0];
            ConstantProp that = null;

            if (state is Model.Integer)
            {
                that = GetExtObj((state as Model.Integer).AsInt());
            }
            else if (state is Model.Boolean)
            {
                that = GetExtObj((state as Model.Boolean).Value);
            }
            else
            {
                throw new AbsHoudiniInternalError("Illegal type " + state.GetType().ToString());
            }

            return Join(that);
        }

        public Expr Gamma(List<Expr> vars)
        {
            Debug.Assert(vars.Count == 1);
            var v = vars[0];
            if (isBottom) return Expr.False;
            if (isTop) return Expr.True;
            if (val is int)
                return Expr.Eq(v, Expr.Literal((int)val));
            if (val is bool && (bool)val)
                return v;
            if (val is bool && !(bool)val)
                return Expr.Not(v);

            return null;
        }

        public bool TypeCheck(List<Type> argTypes, out string msg)
        {
            msg = "";
            if (argTypes.Count != 1)
            {
                msg = "Illegal number of arguments, expecting 1";
                return false;
            }
            if (!argTypes[0].IsInt && ! argTypes[0].IsBool)
            {
                msg = "Illegal type, expecting int or bool";
                return false;
            }
            return true;
        }
    }


    public class IndependentAttribute<T> : IAbstractDomain where T : class, IAbstractDomain
    {
        bool isBottom;
        int numVars;
        List<T> varVal;
        T underlyingInstance;

        public IndependentAttribute()
        {
            isBottom = true;
            numVars = 0;
            varVal = new List<T>();
            underlyingInstance = null;
        }

        public IAbstractDomain Bottom()
        {
            return new IndependentAttribute<T>();
        }

        public IAbstractDomain MakeTop(out bool changed)
        {
            var mt = new Func<IAbstractDomain>(() =>
                {
                    var ret = new IndependentAttribute<T>();
                    ret.isBottom = true;
                    ret.numVars = numVars;
                    ret.underlyingInstance = underlyingInstance;
                    ret.varVal = new List<T>();
                    bool tmp;
                    for (int i = 0; i < varVal.Count; i++)
                        ret.varVal.Add(varVal[i].MakeTop(out tmp) as T);
                    return ret;
                });

            if (!isBottom)
            {
                foreach (var t in varVal)
                {
                    var top = t.MakeTop(out changed);
                    if (changed)
                    {
                        return mt();
                    }
                }
            }
            else
            {
                changed = true;
                return mt();
            }

            changed = false;
            return this;
        }
        public IAbstractDomain Join(List<Model.Element> state)
        {
            SetUnderlyingInstance();

            if (!isBottom && numVars != state.Count)
            {
                throw new AbsHoudiniInternalError(
                    string.Format("Got illegal number of arguments ({0}), expected {1}", state.Count, numVars));
            }

            var ret = new IndependentAttribute<T>();
            ret.isBottom = false;
            ret.numVars = state.Count;
            for(int i = 0; i < state.Count; i++)
            {
                var sl = new List<Model.Element>();
                sl.Add(state[i]);
                T prev = isBottom ? underlyingInstance.Bottom() as T : varVal[i];
                ret.varVal.Add(prev.Join(sl) as T);
            }

            return ret;
        }

        public Expr Gamma(List<Expr> vars)
        {
            if (isBottom) return Expr.False;
            if (numVars != vars.Count)
                throw new AbsHoudiniInternalError(
                    string.Format("Got illegal number of arguments ({0}), expected {1}", vars.Count, numVars));

            Expr ret = Expr.True;
            for (int i = 0; i < numVars; i++)
            {
                var sl = new List<Expr>(); sl.Add(vars[i]);
                ret = Expr.And(ret, varVal[i].Gamma(sl));
            }

            return ret;
        }

        private void SetUnderlyingInstance()
        {
            if (underlyingInstance != null) return;
            var tt = typeof(T);
            underlyingInstance = AbstractDomainFactory.GetInstance(tt) as T;
        }

        public bool TypeCheck(List<Type> argTypes, out string msg)
        {
            SetUnderlyingInstance();

            msg = "";
            foreach(var t in argTypes) 
            {
                if(!underlyingInstance.TypeCheck(new List<Type>(new Type[] { t }), out msg))
                    return false;
            }
            return true;
        }
    }

    public class AbstractDomainFactory
    {
        // Type name -> Instance
        private static Dictionary<string, IAbstractDomain> abstractDomainInstances = new Dictionary<string, IAbstractDomain>();
        private static Dictionary<string, IAbstractDomain> abstractDomainInstancesFriendly = new Dictionary<string, IAbstractDomain>();
        
        // bitvector operations
        public static Dictionary<int, Function> bvslt = new Dictionary<int, Function>();

        public static void Register(string friendlyName, IAbstractDomain instance)
        {
            var Name = instance.GetType().FullName;
            Debug.Assert(!abstractDomainInstances.ContainsKey(Name));
            abstractDomainInstances.Add(Name, instance);
            abstractDomainInstancesFriendly.Add(friendlyName, instance);
        }

        public static IAbstractDomain GetInstance(System.Type type)
        {
            var Name = type.FullName;
            Debug.Assert(abstractDomainInstances.ContainsKey(Name));
            return abstractDomainInstances[Name] as IAbstractDomain;
        }

        public static IAbstractDomain GetInstance(string friendlyName)
        {
            if (!abstractDomainInstancesFriendly.ContainsKey(friendlyName))
            {
                Console.WriteLine("Domain {0} not found", friendlyName);
                Console.WriteLine("Supported domains are:");
                abstractDomainInstancesFriendly.Keys.Iter(tup => Console.WriteLine("  {0}", tup));
                throw new AbsHoudiniInternalError("Domain not found");
            }
            return abstractDomainInstancesFriendly[friendlyName] as IAbstractDomain;
        }

        public static void Initialize(Program program)
        {
            // Declare abstract domains
            var domains = new List<System.Tuple<string, IAbstractDomain>>(new System.Tuple<string, IAbstractDomain>[] {
                  System.Tuple.Create("HoudiniConst", HoudiniConst.GetBottom() as IAbstractDomain),
                  System.Tuple.Create("Intervals", new Intervals() as IAbstractDomain),
                  System.Tuple.Create("ConstantProp", ConstantProp.GetBottom() as IAbstractDomain),
                  System.Tuple.Create("PredicateAbs", new PredicateAbsElem() as IAbstractDomain),
                  System.Tuple.Create("PredicateAbsFull", new PredicateAbsFullElem() as IAbstractDomain),
                  System.Tuple.Create("ImplicationDomain", ImplicationDomain.GetBottom() as IAbstractDomain),
                  System.Tuple.Create("PowDomain", PowDomain.GetBottom() as IAbstractDomain),
                  System.Tuple.Create("EqualitiesDomain", EqualitiesDomain.GetBottom() as IAbstractDomain),
                  System.Tuple.Create("IA[HoudiniConst]", new IndependentAttribute<HoudiniConst>()  as IAbstractDomain),
                  System.Tuple.Create("IA[ConstantProp]", new IndependentAttribute<ConstantProp>()  as IAbstractDomain),
                  System.Tuple.Create("IA[Intervals]", new IndependentAttribute<Intervals>()  as IAbstractDomain),
                  System.Tuple.Create("IA[PowDomain]", new IndependentAttribute<PowDomain>() as IAbstractDomain),
              });

            domains.Iter(tup => AbstractDomainFactory.Register(tup.Item1, tup.Item2));
            program.Functions.Iter(RegisterFunction);
        }

        private static void RegisterFunction(Function func)
        {
            var attr = QKeyValue.FindStringAttribute(func.Attributes, "bvbuiltin");
            if (attr != null && attr == "bvslt" && func.InParams.Count == 2 && func.InParams[0].TypedIdent.Type.IsBv)
                bvslt.Add(func.InParams[0].TypedIdent.Type.BvBits, func);
        }
    }

    public interface IAbstractDomain
    {
        IAbstractDomain Bottom();
        IAbstractDomain MakeTop(out bool changed);
        IAbstractDomain Join(List<Model.Element> state);
        Expr Gamma(List<Expr> vars);
        bool TypeCheck(List<Type> argTypes, out string msg);
    }

    public class AbstractHoudini
    {
        // Input Program
        Program program;
        // Impl -> VC
        Dictionary<string, VCExpr> impl2VC;
        // Impl -> Vars at end of the impl
        Dictionary<string, List<VCExpr>> impl2EndStateVars;
        // Impl -> (callee,summary pred)
        Dictionary<string, List<Tuple<string, bool, VCExprVar, VCExprNAry>>> impl2CalleeSummaries;
        // pointer to summary class
        ISummaryElement summaryClass;
        // impl -> summary
        Dictionary<string, ISummaryElement> impl2Summary;
        // name -> impl
        Dictionary<string, Implementation> name2Impl;
        // Use Bilateral algorithm
        public static bool UseBilateralAlgo = true;
        public static int iterTimeLimit = -1; // ms

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
            this.impl2CalleeSummaries = new Dictionary<string, List<Tuple<string, bool, VCExprVar, VCExprNAry>>>();
            this.impl2Summary = new Dictionary<string, ISummaryElement>();
            this.name2Impl = SimpleUtil.nameImplMapping(program);

            if (CommandLineOptions.Clo.ProverKillTime > 0)
                CommandLineOptions.Clo.ProverOptions = CommandLineOptions.Clo.ProverOptions.Concat1(string.Format("TIME_LIMIT={0}", CommandLineOptions.Clo.ProverKillTime));

            this.vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, new List<Checker>());
            this.prover = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, -1);

            this.reporter = new AbstractHoudiniErrorReporter();

            this.proverTime = TimeSpan.Zero;
            this.numProverQueries = 0;

            if (CommandLineOptions.Clo.AbstractHoudini == "0")
                UseBilateralAlgo = false;
        }

        public void computeSummaries(ISummaryElement summaryClass)
        {
            // TODO: move this some place else
            PredicateAbs.FindUnsatPairs(prover.VCExprGen, prover);

            this.summaryClass = summaryClass;

            name2Impl.Values.Iter(attachEnsures);

            program.Implementations
                .Iter(impl => impl2Summary.Add(impl.Name, summaryClass.GetFlaseSummary(program, impl)));

            // Build call graph
            var Succ = new Dictionary<Implementation, HashSet<Implementation>>();
            var Pred = new Dictionary<Implementation, HashSet<Implementation>>();
            name2Impl.Values.Iter(impl => Succ.Add(impl, new HashSet<Implementation>()));
            name2Impl.Values.Iter(impl => Pred.Add(impl, new HashSet<Implementation>()));

            foreach (var impl in program.Implementations)
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
                foreach (var impl in program.Implementations)
                {
                    var nimpl = new Implementation(Token.NoToken, impl.Name, impl.TypeParameters,
                        impl.InParams, impl.OutParams, new List<Variable>(impl.LocVars), new List<Block>());
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

        public HashSet<string> GetPredicates()
        {
            var ret = new HashSet<string>();
            prover = ProverInterface.CreateProver(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend, -1);

            foreach (var tup in impl2Summary)
            {
                var s = tup.Value as PredicateAbs;
                if (s == null) continue;
                ret.UnionWith(s.GetPredicates(program, prover.VCExprGen, prover));
                // debug output
                //Console.WriteLine("Summary of {0}:", tup.Key);
                //Console.WriteLine("{0}", tup.Value);
            }

            prover.Close();
            CommandLineOptions.Clo.TheProverFactory.Close();
            return ret;
        }

        // Obtain the summary expression for a procedure: used programmatically by clients
        // of AbstractHoudini
        public Expr GetSummary(Program program, Procedure proc)
        {
            if (!impl2Summary.ContainsKey(proc.Name))
                return Expr.True;

            var vars = new Dictionary<string, Expr>();
            foreach (var g in program.GlobalVariables)
                vars.Add(g.Name, Expr.Ident(g));
            foreach (var v in proc.InParams.OfType<Variable>())
                vars.Add(v.Name, Expr.Ident(v));
            foreach (var v in proc.OutParams.OfType<Variable>())
                vars.Add(v.Name, Expr.Ident(v));

            return impl2Summary[proc.Name].GetSummaryExpr(
                v => { if (vars.ContainsKey(v)) return vars[v]; else return null; },
                v => { if (vars.ContainsKey(v)) return new OldExpr(Token.NoToken, vars[v]); else return null; });
        }

        public ISummaryElement GetSummaryLowLevel(Procedure proc)
        {
            if (!impl2Summary.ContainsKey(proc.Name)) return null;
            return impl2Summary[proc.Name];
        }

        // Produce a witness that proves that the inferred annotations are correct
        private void ProduceWitness(Dictionary<string, Implementation> copy)
        {
            if (WitnessFile == null)
                return;

            foreach (var proc in program.Procedures)
            {
                var nensures = new List<Ensures>();
                proc.Ensures.OfType<Ensures>()
                .Where(ens => !QKeyValue.FindBoolAttribute(ens.Attributes, "ah") &&
                    !QKeyValue.FindBoolAttribute(ens.Attributes, "pre") &&
                    !QKeyValue.FindBoolAttribute(ens.Attributes, "post") &&
                    QKeyValue.FindStringAttribute(ens.Attributes, "pre") == null &&
                    QKeyValue.FindStringAttribute(ens.Attributes, "post") == null)
                .Iter(ens => nensures.Add(ens));
                foreach (Ensures en in nensures)
                    en.Attributes = removeAttr("InlineAssume", en.Attributes);

                proc.Ensures = nensures;
            }

            var decls = new List<Declaration>(copy.Values);
            decls.AddRange(program.TopLevelDeclarations.Where(decl => !(decl is Implementation)));
            program.TopLevelDeclarations = decls;
            var name2Proc = new Dictionary<string, Procedure>();
            foreach (var proc in program.Procedures)
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

            using (var wt = new TokenTextWriter(WitnessFile, /*pretty=*/ false))
            {
                program.Emit(wt);
            }

            // Replace SummaryPreds with their definition
            foreach (var impl in program.Implementations)
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
                        foreach (var g in program.GlobalVariables)
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

            using (var wt = new TokenTextWriter(WitnessFile, /*pretty=*/ false))
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
            foreach (var proc in program.Procedures)
            {
                procToImpls[proc] = new HashSet<Implementation>();
            }
            foreach (var impl in program.Implementations)
            {
                if (impl.SkipVerification) continue;
                callGraph.AddSource(impl);
                procToImpls[impl.Proc].Add(impl);
            }
            foreach (var impl in program.Implementations)
            {
                if (impl.SkipVerification) continue;
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
                       GetVarMapping(name2Impl[tup.Item1], tup.Item4), prover.VCExprGen);
                env = gen.AndSimp(env, gen.Eq(tup.Item3, calleeSummary));
            }

            var prev = impl2Summary[impl.Name].Copy();
            var upper = impl2Summary[impl.Name].GetTrueSummary(program, impl);
            var sw = new Stopwatch();
            sw.Start();
            var lowerTime = TimeSpan.Zero;

            while(true)
            {
                var usedLower = true;
                var query = impl2Summary[impl.Name];
                sw.Restart();

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
                           GetVarMapping(name2Impl[tup.Item1], tup.Item4), prover.VCExprGen);
                    summaryExpr = gen.AndSimp(summaryExpr, gen.Eq(tup.Item3, ts));
                }
                //Console.WriteLine("Trying summary for {0}: {1}", impl.Name, summaryExpr);

                reporter.model = null;
                var vc = gen.AndSimp(env, summaryExpr);
                vc = gen.Implies(vc, impl2VC[impl.Name]);
                
                //Console.WriteLine("Checking: {0}", vc);
                if (CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Verifying {0} ({1}): {2}", impl.Name, usedLower ? "lower" : "ac", query);

                if (usedLower && lowerTime.TotalMilliseconds >= iterTimeLimit && iterTimeLimit >= 0)
                {
                    if (UseBilateralAlgo)
                    {
                        if (CommandLineOptions.Clo.Trace)
                            Console.WriteLine("Timeout/Spaceout while verifying " + impl.Name);
                        ret = prev.IsEqual(upper) ? false : true;
                        impl2Summary[impl.Name] = upper;
                        break;
                    }
                    else
                    {
                        if (CommandLineOptions.Clo.Trace)
                            Console.WriteLine("Timeout/Spaceout while verifying " + impl.Name);
                        var tt = impl2Summary[impl.Name].GetTrueSummary(program, impl);
                        ret = prev.IsEqual(tt) ? false : true; ;
                        impl2Summary[impl.Name] = tt;
                        break;
                    }
                }

                var start = DateTime.Now;

                //prover.Push();
                //prover.Assert(gen.Not(vc), true);
                //prover.FlushAxiomsToTheoremProver();
                //prover.Check();
                //ProverInterface.Outcome proverOutcome = prover.CheckOutcome(reporter);
                //prover.Pop();

                prover.BeginCheck(impl.Name, vc, reporter);
                ProverInterface.Outcome proverOutcome = prover.CheckOutcome(reporter);

                var inc = (DateTime.Now - start);
                proverTime += inc;
                numProverQueries++;

                sw.Stop();
                if (usedLower) lowerTime += sw.Elapsed;

                if(CommandLineOptions.Clo.Trace)
                    Console.WriteLine("Time taken = " + inc.TotalSeconds.ToString()); 

                if (UseBilateralAlgo)
                {
                    if (proverOutcome == ProverInterface.Outcome.TimeOut || proverOutcome == ProverInterface.Outcome.OutOfMemory || proverOutcome == ProverInterface.Outcome.OutOfResource)
                    {
                        if(CommandLineOptions.Clo.Trace)
                            Console.WriteLine("Timeout/Spaceout while verifying " + impl.Name);
                        ret = prev.IsEqual(upper) ? false : true;
                        impl2Summary[impl.Name] = upper;
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
                    if (proverOutcome == ProverInterface.Outcome.TimeOut || proverOutcome == ProverInterface.Outcome.OutOfMemory || proverOutcome == ProverInterface.Outcome.OutOfResource)
                    {
                        if (CommandLineOptions.Clo.Trace)
                            Console.WriteLine("Timeout/Spaceout while verifying " + impl.Name);
                        var tt = impl2Summary[impl.Name].GetTrueSummary(program, impl);
                        ret = prev.IsEqual(tt) ? false : true; ;
                        impl2Summary[impl.Name] = tt;
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
            foreach (var g in program.GlobalVariables)
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
            foreach (var g in program.GlobalVariables)
            {
                if (ret.ContainsKey(g.Name)) { cnt++; continue; }

                ret.Add(string.Format("{0}", g.Name), summaryPred[cnt]);
                cnt++;
            }

            // Constants
            foreach (var c in program.Constants)
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
            foreach (var g in program.GlobalVariables)
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
            foreach (var g in program.GlobalVariables)
            {
                if (ret.ContainsKey(g.Name)) { cnt++; continue; }

                ret.Add(string.Format("{0}", g.Name), getValue(implVars[cnt], model));
                cnt++;
            }

            // Constants
            foreach (var c in program.Constants)
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
                //return model.GetElement(arg.ToString());
                return model.MkElement(arg.ToString());
            }
            else if (arg is VCExprVar)
            {
                var el = model.TryGetFunc(prover.Context.Lookup(arg as VCExprVar));
                if (el != null)
                {
                    Debug.Assert(el.Arity == 0 && el.AppCount == 1);
                    return el.Apps.First().Result;
                }
                else
                {
                    // Variable not defined; assign arbitrary value
                    if (arg.Type.IsBool)
                        return model.MkElement("false");
                    else if (arg.Type.IsInt)
                        return model.MkIntElement(0);
                    else
                        return null;
                }
            }
            else
            {
                Debug.Assert(false);
                return null;
            }
        }

        private void attachEnsures(Implementation impl)
        {
            List<Variable> functionInterfaceVars = new List<Variable>();
            foreach (Variable v in vcgen.program.GlobalVariables)
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

            List<Expr> exprs = new List<Expr>();
            foreach (Variable v in vcgen.program.GlobalVariables)
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
            Dictionary<int, Absy> label2absy;

            if (CommandLineOptions.Clo.Trace)
            {
                Console.WriteLine("Generating VC of {0}", impl.Name);
            }

            vcgen.ConvertCFG2DAG(impl);
            vcgen.PassifyImpl(impl, out mvInfo);

            var gen = prover.VCExprGen;
            var vcexpr = vcgen.GenerateVC(impl, null, out label2absy, prover.Context);


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

            // It is possible that no assert is found in the procedure. It happens when the
            // procedure doesn't return.
            //Debug.Assert(found);

            // Grab summary predicates
            var visitor = new FindSummaryPred(prover.VCExprGen, assertId);
            vcexpr = visitor.Mutate(vcexpr, true);

            // Create a macro so that the VC can sit with the theorem prover
            Macro macro = new Macro(Token.NoToken, impl.Name + "Macro", new List<Variable>(), new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", Bpl.Type.Bool), false));
            prover.DefineMacro(macro, vcexpr);

            // Store VC
            impl2VC.Add(impl.Name, gen.Function(macro));

            //Console.WriteLine("VC of {0}: {1}", impl.Name, vcexpr);

            // check sanity: only one predicate for self-summary
            // (There may be none when the procedure doesn't return)
            Debug.Assert(visitor.summaryPreds.Count(tup => tup.Item2) <= 1);

            impl2CalleeSummaries.Add(impl.Name, new List<Tuple<string, bool, VCExprVar, VCExprNAry>>());
            visitor.summaryPreds.Iter(tup => impl2CalleeSummaries[impl.Name].Add(tup));
        }
    }

    public interface ISummaryElement
    {
        ISummaryElement Copy();
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

        #region ISummaryElement Members

        public ISummaryElement Copy()
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
            if (name != null)
                return name;

            return expr.ToString();
        }
    }

    public class PredicateAbs : ISummaryElement
    {
        public static Dictionary<string, List<NamedExpr>> PrePreds { get; private set; }
        public static Dictionary<string, HashSet<int>> PosPrePreds { get; private set; }
        public static Dictionary<string, List<NamedExpr>> PostPreds { get; private set; }
        public static Dictionary<Tuple<string, int>, List<PredicateAbsDisjunct>> UpperCandidates;
        private static HashSet<string> boolConstants;
        // {proc, pred-pair} -> polariry
        public static HashSet<Tuple<string, int, int, bool, bool>> unsatPrePredPairs;
        public static HashSet<Tuple<string, int, int, bool, bool>> unsatPostPredPairs;

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
            PosPrePreds = new Dictionary<string, HashSet<int>>();

            boolConstants = new HashSet<string>();
            UpperCandidates = new Dictionary<Tuple<string, int>, List<PredicateAbsDisjunct>>();

            program.Constants
                .Where(c => c.TypedIdent.Type.IsBool)
                .Iter(c => boolConstants.Add(c.Name));

            // Add template pre-post to all procedures
            var preT = new List<NamedExpr>();
            var postT = new List<NamedExpr>();
            var posPreT = new HashSet<int>();
            var tempP = new HashSet<Procedure>();
            foreach (var proc in
                program.Procedures
                .Where(proc => QKeyValue.FindBoolAttribute(proc.Attributes, "template")))
            {
                tempP.Add(proc);
                foreach (var ens in proc.Ensures.OfType<Ensures>())
                {
                    var pos = QKeyValue.FindBoolAttribute(ens.Attributes, "positive");

                    if (QKeyValue.FindBoolAttribute(ens.Attributes, "pre"))
                    {
                        preT.Add(new NamedExpr(null, ens.Condition));
                        if (pos) posPreT.Add(preT.Count - 1);
                    }

                    if (QKeyValue.FindBoolAttribute(ens.Attributes, "post"))
                        postT.Add(new NamedExpr(null, ens.Condition));

                    var s = QKeyValue.FindStringAttribute(ens.Attributes, "pre");
                    if (s != null)
                    {
                        preT.Add(new NamedExpr(s, ens.Condition));
                        if (pos) posPreT.Add(preT.Count - 1);
                    }

                    s = QKeyValue.FindStringAttribute(ens.Attributes, "post");
                    if (s != null)
                        postT.Add(new NamedExpr(s, ens.Condition));
                }
            }

            program.RemoveTopLevelDeclarations(decl => tempP.Contains(decl));
            var upperPreds = new Dictionary<string, List<Expr>>();

            foreach (var impl in program.Implementations)
            {
                PrePreds.Add(impl.Name, new List<NamedExpr>());
                PostPreds.Add(impl.Name, new List<NamedExpr>());
                PosPrePreds.Add(impl.Name, new HashSet<int>());

                // Add "false" as the first post predicate
                //PostPreds[impl.Name].Add(new NamedExpr(Expr.False));

                preT.Iter(e => PrePreds[impl.Name].Add(e));
                postT.Iter(e => PostPreds[impl.Name].Add(e));
                PosPrePreds[impl.Name].UnionWith(posPreT);

                // Pick up per-procedure pre-post
                var nens = new List<Ensures>();
                foreach (var ens in impl.Proc.Ensures.OfType<Ensures>())
                {
                    string s = null;
                    var pos = QKeyValue.FindBoolAttribute(ens.Attributes, "positive");
                    
                    if (QKeyValue.FindBoolAttribute(ens.Attributes, "pre"))
                    {
                        PrePreds[impl.Name].Add(new NamedExpr(ens.Condition));
                        PosPrePreds[impl.Name].Add(PrePreds[impl.Name].Count - 1);
                    }
                    else if (QKeyValue.FindBoolAttribute(ens.Attributes, "post"))
                    {
                        PostPreds[impl.Name].Add(new NamedExpr(ens.Condition));
                    }
                    else if ((s = QKeyValue.FindStringAttribute(ens.Attributes, "pre")) != null)
                    {
                        PrePreds[impl.Name].Add(new NamedExpr(s, ens.Condition));
                        PosPrePreds[impl.Name].Add(PrePreds[impl.Name].Count - 1);
                    }
                    else if ((s = QKeyValue.FindStringAttribute(ens.Attributes, "post")) != null)
                    {
                        PostPreds[impl.Name].Add(new NamedExpr(s, ens.Condition));
                    }
                    else if (QKeyValue.FindBoolAttribute(ens.Attributes, "upper"))
                    {
                        var key = impl.Name;
                        if (!upperPreds.ContainsKey(key))
                            upperPreds.Add(key, new List<Expr>());
                        upperPreds[key].Add(ens.Condition);
                    }
                    else
                    {
                        nens.Add(ens);
                    }
                }
                impl.Proc.Ensures = nens;
            }

            foreach (var tup in upperPreds)
            {
                var procName = tup.Key;
                var candidates = tup.Value;
                if (!candidates.Any()) continue;

                var strToPost = new Dictionary<string, int>();
                for (int i = 0; i < PostPreds[procName].Count; i++)
                {
                    strToPost.Add(PostPreds[procName][i].expr.ToString(), i);
                }

                foreach (var expr in candidates)
                {
                    if (strToPost.ContainsKey(expr.ToString()))
                    {
                        var key = Tuple.Create(procName, strToPost[expr.ToString()]);
                        if (!UpperCandidates.ContainsKey(key))
                            UpperCandidates.Add(key, new List<PredicateAbsDisjunct>());
                        UpperCandidates[key].Add(new PredicateAbsDisjunct(true, procName));
                    }
                    else
                    {
                        // Try parsing the expression as (pre-conjunct ==> post-pred)
                        var parsed = ParseExpr(expr, procName);
                        if (parsed != null && strToPost.ContainsKey(parsed.Item2.ToString()))
                        {
                            var key = Tuple.Create(procName, strToPost[parsed.Item2.ToString()]);
                            if (!UpperCandidates.ContainsKey(key))
                                UpperCandidates.Add(key, new List<PredicateAbsDisjunct>());
                            UpperCandidates[key].Add(parsed.Item1);
                        }
                    }
                }

            }
            //Console.WriteLine("Running Abstract Houdini");
            //PostPreds.Iter(expr => Console.WriteLine("\tPost: {0}", expr));
            //PrePreds.Iter(expr => Console.WriteLine("\tPre: {0}", expr));
        }

        // Try parsing the expression as (pre-conjunct ==> post-pred)
        private static Tuple<PredicateAbsDisjunct, Expr> ParseExpr(Expr expr, string procName)
        {
            Expr postExpr = null;
            Expr preExpr = null;

            // Decompose outer Implies
            var nexpr = expr as NAryExpr;
            if (nexpr != null && (nexpr.Fun is BinaryOperator)
                && (nexpr.Fun as BinaryOperator).Op == BinaryOperator.Opcode.Imp
                && (nexpr.Args.Count == 2))
            {
                postExpr = nexpr.Args[1];
                preExpr = nexpr.Args[0];
            }
            else
            {
                if(CommandLineOptions.Clo.Trace) Console.WriteLine("Failed to parse {0} (ignoring)", expr);
                return null;
            }


            var atoms = DecomposeOuterAnd(preExpr);
            var pos = new HashSet<int>();
            var neg = new HashSet<int>();

            foreach (var atom in atoms)
            {
                var index = PrePreds[procName].FindIndex(ne => ne.expr.ToString() == atom.ToString());
                if (index == -1)
                {
                    index = PrePreds[procName].FindIndex(ne => Expr.Not(ne.expr).ToString() == atom.ToString());
                    if (index == -1)
                    {
                        if(CommandLineOptions.Clo.Trace) Console.WriteLine("Failed to parse {0} (ignoring)", atom);
                        return null;
                    }
                    else
                    {
                        neg.Add(index);
                    }
                }
                else
                {
                    pos.Add(index);
                }
            }

            var conj = new PredicateAbsConjunct(pos, neg, procName);
            var conjls = new List<PredicateAbsConjunct>();
            conjls.Add(conj);

            return Tuple.Create(new PredicateAbsDisjunct(conjls, procName), postExpr);
        }

        // blah && blah ==> {blah, blah}
        static IEnumerable<Expr> DecomposeOuterAnd(Expr expr)
        {
            var ret = new List<Expr>();

            var nexpr = expr as NAryExpr;
            if (nexpr == null
                || !(nexpr.Fun is BinaryOperator)
                || (nexpr.Fun as BinaryOperator).Op != BinaryOperator.Opcode.And)
            {
                    ret.Add(expr);
            }
            else
            {
                foreach (Expr a in nexpr.Args)
                    ret.AddRange(DecomposeOuterAnd(a));
            }

            return ret;
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
                if (nary.Fun is MapSelect && nary.Args.Count == 2)
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

        private static VCExpr ToVcVar(string v, Dictionary<string, VCExpr> incarnations, bool tryOld)
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

        public static void FindUnsatPairs(VCExpressionGenerator gen, ProverInterface prover)
        {
            unsatPrePredPairs = new HashSet<Tuple<string, int, int, bool, bool>>();
            unsatPostPredPairs = new HashSet<Tuple<string, int, int, bool, bool>>(); 

            var cachePos = new HashSet<Tuple<string, string>>();
            var cacheNeg = new HashSet<Tuple<string, string>>();
            var record = new Action<object, string, int, int, bool, bool>(
                (map, proc, e1, e2, p1, p2) => {
                    var key = Tuple.Create(proc, e1, e2, p1, p2);
                    if (map == PrePreds)
                        unsatPrePredPairs.Add(key);
                    else
                        unsatPostPredPairs.Add(key);
                }
            );

            var predMaps = new List<Dictionary<string, List<NamedExpr>>>();
            predMaps.Add(PrePreds); predMaps.Add(PostPreds);

            foreach (var map in predMaps)
            {
                foreach (var proc in map.Keys)
                {
                    for (int i = 0; i < 2 * map[proc].Count(); i++)
                    {
                        var p1 = (i % 2); // polarity
                        var e1 = map[proc][i / 2].expr;
                        if (p1 == 0) e1 = Expr.Not(e1);

                        for (int j = 2 * ((i / 2) + 1); j < 2 * map[proc].Count(); j++)
                        {
                            var p2 = (j % 2); // polarity
                            var e2 = map[proc][j / 2].expr;
                            if (p2 == 0) e2 = Expr.Not(e2);

                            var key = Tuple.Create(e1.ToString(), e2.ToString());
                            if (cachePos.Contains(key))
                            {
                                record(map, proc, i / 2, j / 2, p1 == 1, p2 == 1);
                                continue;
                            }
                            else if (cacheNeg.Contains(key))
                            {
                                continue;
                            }

                            if (!CheckIfUnsat(e1, e2, gen, prover))
                            {
                                cacheNeg.Add(key);
                                continue;
                            }
                            cachePos.Add(key);
                            record(map, proc, i / 2, j / 2, p1 == 1, p2 == 1);

                            if (CommandLineOptions.Clo.Trace)
                                Console.WriteLine("Proved UNSAT: {0}    {1}", e1, e2);
                        }
                    }
                }
            }
        }

        // Is a ^ b UNSAT?
        private static bool CheckIfUnsat(Expr a, Expr b, VCExpressionGenerator gen, ProverInterface prover)
        {
            var gatherLitA = new GatherLiterals();
            var gatherLitB = new GatherLiterals();

            gatherLitA.Visit(a);
            gatherLitB.Visit(b);

            var seta = new HashSet<Variable>();
            var setb = new HashSet<Variable>();
            gatherLitA.literals.Iter(tup => seta.Add(tup.Item1));
            gatherLitB.literals.Iter(tup => setb.Add(tup.Item1));
            seta.IntersectWith(setb);
            if (!seta.Any()) return false;
            
            // Create fresh variables
            return CheckIfUnsat(Expr.And(a, b), gen, prover);
        }

        // Is a UNSAT?
        private static bool CheckIfUnsat(Expr a, VCExpressionGenerator gen, ProverInterface prover)
        {
            var gatherLitA = new GatherLiterals();
            gatherLitA.Visit(a);

            // Create fresh variables
            var counter = 0;
            var incarnations = new Dictionary<string, VCExpr>();
            foreach (var literal in gatherLitA.literals)
            {
                if (incarnations.ContainsKey(literal.Item2.ToString()))
                    continue;

                //if(!literal.Item1.TypedIdent.Type.IsInt && !literal.Item1.TypedIdent.Type.IsBool)
                var v = gen.Variable("UNSATCheck" + counter, literal.Item1.TypedIdent.Type);
                incarnations.Add(literal.Item2.ToString(), v);
                counter++;
            }

            var vc1 = ToVcExpr(a, incarnations, gen);
            var vc = gen.LabelPos("Temp", vc1);

            // check
            prover.AssertAxioms();
            prover.Push();
            prover.Assert(vc, true);
            prover.Check();
            var outcome = prover.CheckOutcomeCore(new AbstractHoudiniErrorReporter());
            prover.Pop();

            if (outcome == ProverInterface.Outcome.Valid)
                return true;
            return false;
        }


        class GatherLiterals : ReadOnlyVisitor
        {
            public List<Tuple<Variable, Expr>> literals;
            bool inOld;

            public GatherLiterals()
            {
                literals = new List<Tuple<Variable, Expr>>();
                inOld = false;
            }

            public override Expr VisitOldExpr(OldExpr node)
            {
                var prev = inOld;
                inOld = true;
                var ret = base.VisitOldExpr(node);
                inOld = prev;
                return ret;
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (inOld)
                    literals.Add(Tuple.Create(node.Decl, new OldExpr(Token.NoToken, node) as Expr));
                else
                    literals.Add(Tuple.Create(node.Decl, node as Expr));

                return node;
            }
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
            if (elem is Model.DatatypeValue && (elem as Model.DatatypeValue).Arguments.Length == 1 &&
                (elem as Model.DatatypeValue).ConstructorName == "-" &&
                (elem as Model.DatatypeValue).Arguments[0] is Model.Integer)
            {
                // negative number as "-" @ int
                return Microsoft.Basetypes.BigNum.FromInt(-1 * ((elem as Model.DatatypeValue).Arguments[0] as Model.Integer).AsInt());
            }
            throw new NotImplementedException("Cannot yet handle this Model.Element type");
        }

        private Model.Element ToElem(object val)
        {
            if (val is bool || val is int || val is Basetypes.BigNum)
                return model.MkElement(val.ToString());
            throw new NotImplementedException("Cannot yet handle this value type");
        }

        // replace v by old(v)
        private static Expr MakeOld(Expr expr)
        {
            var substalways = new Substitution(v => new OldExpr(Token.NoToken, Expr.Ident(v)));
            var substold = new Substitution(v => Expr.Ident(v));

            return Substituter.ApplyReplacingOldExprs(substalways, substold, expr);
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

        private static VCExpr ToVcExpr(Expr expr, Dictionary<string, VCExpr> incarnations, VCExpressionGenerator gen)
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
                if (nary.Fun is MapSelect && nary.Args.Count == 2)
                {
                    return gen.Select(ToVcExpr(nary.Args[0], incarnations, gen), ToVcExpr(nary.Args[1], incarnations, gen));
                }
                Debug.Assert(false, "No other op is handled");
            }
            throw new NotImplementedException(string.Format("Expr of type {0} is not handled", expr.GetType().ToString()));
        }

        private static VCExprOp Translate(BinaryOperator op)
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

        // If "false" is a post-predicate, then remove its "pre" constraint from all others, whenever possible
        public void Simplify()
        {
            // find "false"
            var findex = PostPreds[procName].FindIndex(ne => (ne.expr is LiteralExpr) && (ne.expr as LiteralExpr).IsFalse);
            if (findex < 0) return;
            if (value[findex].isTrue)
            {
                // procedure doesn't return
                for (int i = 0; i < value.Length; i++)
                    if (i != findex) value[i] = new PredicateAbsDisjunct(false, procName);
                return;
            }
            if (value[findex].isFalse)
                return;

            for (int i = 0; i < value.Length; i++)
                if (i != findex) value[i].Subtract(value[findex]);
        }

        public HashSet<string> GetPredicates(Program program, VCExpressionGenerator gen, ProverInterface prover)
        {
            var ret = new HashSet<string>();
            if (isFalse) return ret;
            Simplify();

            // Find the free expressions
            var proc = program.Procedures.FirstOrDefault(p => p.Name == procName);
            Contract.Assert(proc != null);
            Expr freeSummary = Expr.True;
            foreach (var req in proc.Requires.OfType<Requires>().Where(req => req.Free))
            {
                freeSummary = Expr.And(freeSummary, MakeOld(req.Condition));
            }
            foreach (var ens in proc.Ensures.OfType<Ensures>().Where(ens => ens.Free))
            {
                freeSummary = Expr.And(freeSummary, ens.Condition);
            }
            
            for (int i = 0; i < PostPreds[procName].Count; i++)
            {
                if (value[i].isFalse) continue;
                if (PostPreds[procName][i].expr is LiteralExpr && (PostPreds[procName][i].expr as LiteralExpr).IsFalse)
                    continue;

                if (value[i].isTrue)
                    ret.Add(PostPreds[procName][i].expr.ToString());
                else
                {
                    foreach (var c in value[i].GetConjuncts())
                    {
                        var s = Expr.Imp(c.ToExpr(j => PrePreds[procName][j].expr), PostPreds[procName][i].expr);
                        if (CheckIfUnsat(Expr.And(freeSummary, Expr.Not(s)), gen, prover))
                            continue;
                        ret.Add(s.ToString());
                    }
                }
            }
            return ret;
        }

        public override string ToString()
        {
            var ret = "";
            if (isFalse) return "false";
            var first = true;

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

        public ISummaryElement Copy()
        {
            var ret = new PredicateAbs(procName);
            ret.isFalse = isFalse;
            ret.value = new PredicateAbsDisjunct[value.Length];
            for (int i = 0; i < value.Length; i++)
                ret.value[i] = value[i];
            return ret;
        }

        public ISummaryElement GetFlaseSummary(Program program, Implementation impl)
        {
            return new PredicateAbs(impl.Name);
        }

        public ISummaryElement GetTrueSummary(Program program, Implementation impl)
        {
            var ret = new PredicateAbs(impl.Name);
            ret.isFalse = false;
            for (int i = 0; i < PostPreds[this.procName].Count; i++) ret.value[i] = new PredicateAbsDisjunct(false, impl.Name);

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

                var newDisj = new PredicateAbsDisjunct(true, procName);
                if (!postPredsVal[i])
                {
                    newDisj = new PredicateAbsDisjunct(indexSeq.Where(j => !prePredsVal[j]), indexSeq.Where(j => prePredsVal[j] && !PosPrePreds[procName].Contains(j)), procName);
                }

                if (isFalse)
                    value[i] = newDisj;
                else
                    value[i] = PredicateAbsDisjunct.And(value[i], newDisj);
            }

            /*
            // do beta(model)
            var that = new PredicateAbsDisjunct[PostPreds[procName].Count];
            for (int i = 0; i < PostPreds[procName].Count; i++)
            {
                if (postPredsVal[i])
                    that[i] = new PredicateAbsDisjunct(true, procName);
                else if (i == 0)
                {
                    Debug.Assert(PostPreds[procName][0].ToString() == "false");
                    var newDisj = new PredicateAbsDisjunct(true, procName);
                    newDisj = new PredicateAbsDisjunct(indexSeq.Where(j => !prePredsVal[j]), indexSeq.Where(j => prePredsVal[j]), procName);
                    that[i] = newDisj;
                }
                else
                {
                    // false
                    that[i] = new PredicateAbsDisjunct(false, procName);
                }
            }

            // Do join
            for (int i = 0; i < PostPreds[procName].Count; i++)
            {
                if (isFalse)
                    value[i] = that[i];
                else
                {
                    if (i == 0)
                        value[i] = PredicateAbsDisjunct.And(value[i], that[i]);
                    else
                    {
                        var c1 = PredicateAbsDisjunct.And(value[i], that[i]);
                        var c2 = PredicateAbsDisjunct.And(value[i], that[0]);
                        var c3 = PredicateAbsDisjunct.And(value[0], that[i]);
                        value[i] = PredicateAbsDisjunct.Or(c1, c2);
                        value[i] = PredicateAbsDisjunct.Or(value[i], c3);
                    }
                }
            }
            */
            isFalse = false;

            //Console.WriteLine("Result of Join: {0}", this.ToString());
        }

        // Precondition: the upper guys are just {true/false/upper-candidate} ==> post-pred
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
                value[i] = PredicateAbsDisjunct.Or(value[i], other.value[i]);
            }
        }

        public bool IsEqual(ISummaryElement other)
        {
            var that = other as PredicateAbs;
            if (isFalse && that.isFalse) return true;
            if (isFalse || that.isFalse) return false;
            for (int i = 0; i < PostPreds[procName].Count; i++)
            {
                if (!PredicateAbsDisjunct.syntacticLessThan(value[i], that.value[i]) ||
                    !PredicateAbsDisjunct.syntacticLessThan(that.value[i], value[i]))
                    return false;
            }
            return true;
        }

        // Precondition: the upper guys are just {true/false/upper-candidate} ==> post-pred
        // Postcondition: the returned value is also of this form (for just one post-pred)
        public ISummaryElement AbstractConsequence(ISummaryElement iupper)
        {
            var upper = iupper as PredicateAbs;

            for (int i = 0; i < PostPreds[this.procName].Count; i++)
            {
                if (upper.value[i].isTrue) continue;
                if (!UpperCandidates.ContainsKey(Tuple.Create(procName, i))) continue;

                foreach (var candidate in UpperCandidates[Tuple.Create(procName, i)])
                {
                    if (PredicateAbsDisjunct.syntacticLessThan(candidate, upper.value[i]))
                        continue;
                    if (!this.isFalse && !PredicateAbsDisjunct.syntacticLessThan(candidate, this.value[i]))
                        continue;

                    var ret = new PredicateAbs(this.procName);
                    ret.isFalse = false;
                    for (int j = 0; j < PostPreds[this.procName].Count; j++)
                        ret.value[j] = new PredicateAbsDisjunct(false, this.procName);

                    ret.value[i] = candidate;

                    return ret;
                }
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

    public class PredicateAbsDisjunct
    {
        List<PredicateAbsConjunct> conjuncts;
        string ProcName;
        public bool isTrue {get; private set;}
        public bool isFalse
        {
            get
            {
                if (isTrue) return false;
                return conjuncts.Count == 0;
            }
        }

        public PredicateAbsDisjunct(bool isTrue, string ProcName)
        {
            this.isTrue = isTrue;
            this.ProcName = ProcName;
            conjuncts = new List<PredicateAbsConjunct>();
        }

        public PredicateAbsDisjunct(List<PredicateAbsConjunct> conjuncts, string ProcName)
        {
            isTrue = false;
            this.conjuncts = conjuncts;
            this.ProcName = ProcName;
        }

        // Disjunct of singleton conjuncts
        public PredicateAbsDisjunct(IEnumerable<int> pos, IEnumerable<int> neg, string ProcName)
        {
            this.ProcName = ProcName;
            conjuncts = new List<PredicateAbsConjunct>();
            isTrue = false;
            pos.Iter(p => conjuncts.Add(PredicateAbsConjunct.Singleton(p, true, ProcName)));
            neg.Iter(p => conjuncts.Add(PredicateAbsConjunct.Singleton(p, false, ProcName)));
        }

        // Does d1 describe a smaller set of states than d2? This is true when every conjunct of d1
        // is smaller than some conjunct of d2
        public static bool syntacticLessThan(PredicateAbsDisjunct d1, PredicateAbsDisjunct d2)
        {
            if (d2.isTrue) return true;
            if (d1.isTrue) return false;
            if (d1.isFalse) return true;
            if (d2.isFalse) return false;

            foreach (var c1 in d1.conjuncts)
            {
                if (d2.conjuncts.Any(c2 => PredicateAbsConjunct.syntacticLessThan(c1, c2)))
                    continue;
                else
                    return false;
            }
            return true;
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

            return new PredicateAbsDisjunct(result, v1.ProcName);
        }

        public static PredicateAbsDisjunct Or(PredicateAbsDisjunct v1, PredicateAbsDisjunct v2)
        {
            if (v1.isTrue) return v1;
            if (v2.isTrue) return v2;
            if (v1.isFalse) return v2;
            if (v2.isFalse) return v1;

            var result = new List<PredicateAbsConjunct>();
            v1.conjuncts.Iter(c => result.Add(c));

            foreach (var c in v2.conjuncts)
            {
                if (result.Any(cprime => c.implies(cprime))) continue;
                var tmp = new List<PredicateAbsConjunct>();
                tmp.Add(c);
                result.Where(cprime => !cprime.implies(c)).Iter(cprime => tmp.Add(cprime));
                result = tmp;
            }

            return new PredicateAbsDisjunct(result, v1.ProcName);
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

        public void Subtract(PredicateAbsDisjunct that)
        {
            var ncon = new List<PredicateAbsConjunct>();
            foreach (var c1 in conjuncts)
            {
                if (that.conjuncts.Any(c2 => c1.implies(c2)))
                    continue;
                ncon.Add(c1);
            }
            conjuncts = ncon;
        }

        public IEnumerable<PredicateAbsConjunct> GetConjuncts()
        {
            return conjuncts;
        }

    }

    public class PredicateAbsConjunct
    {
        static int ConjunctBound = 3;

        public bool isFalse { get; private set; }
        HashSet<int> posPreds;
        HashSet<int> negPreds;
        string ProcName;

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

        // Do this step only once in a while?
        private void StrongNormalize()
        {
            if (isFalse) return;

            var candidates = new List<Tuple<int, bool>>();
            posPreds.Iter(p => candidates.Add(Tuple.Create(p, true)));
            negPreds.Iter(p => candidates.Add(Tuple.Create(p, false)));
            var drop = new HashSet<int>();
            for (int i = 0; i < candidates.Count; i++)
            {
                for (int j = 0; j < candidates.Count; j++)
                {
                    if (i == j) continue;

                    var key = Tuple.Create(ProcName, candidates[i].Item1, candidates[j].Item1,
                        candidates[i].Item2, candidates[j].Item2);
                    if (PredicateAbs.unsatPrePredPairs.Contains(key))
                    {
                        isFalse = true;
                        posPreds = new HashSet<int>();
                        negPreds = new HashSet<int>();
                        return;
                    }

                    key = Tuple.Create(ProcName, candidates[i].Item1, candidates[j].Item1,
                        candidates[i].Item2, !candidates[j].Item2);

                    if (PredicateAbs.unsatPrePredPairs.Contains(key))
                        drop.Add(candidates[j].Item1);
                }
            }

            posPreds.ExceptWith(drop);
            negPreds.ExceptWith(drop);
        }

        public PredicateAbsConjunct(bool isFalse, string ProcName)
        {
            posPreds = new HashSet<int>();
            negPreds = new HashSet<int>();
            this.isFalse = isFalse;
            this.ProcName = ProcName;
        }

        // do we know that c1 is surely less than or equal to c2? That is, c1 describes a smaller
        // concretization. We check that c2 is a sub-conjunct of c1
        public static bool syntacticLessThan(PredicateAbsConjunct c1, PredicateAbsConjunct c2)
        {
            if (c1.isFalse) return true;
            if (c2.isFalse) return false;
            return (c2.posPreds.IsSubsetOf(c1.posPreds) && c2.negPreds.IsSubsetOf(c1.negPreds));
        }

        public static PredicateAbsConjunct Singleton(int v, bool isPositive, string ProcName)
        {
            if (isPositive)
                return new PredicateAbsConjunct(new int[] { v }, new HashSet<int>(), ProcName);
            else
                return new PredicateAbsConjunct(new HashSet<int>(), new int[] { v }, ProcName);
        }

        public PredicateAbsConjunct(IEnumerable<int> pos, IEnumerable<int> neg, string ProcName)
        {
            isFalse = false;
            posPreds = new HashSet<int>(pos);
            negPreds = new HashSet<int>(neg);
            this.ProcName = ProcName;
            Normalize();
        }

        public static PredicateAbsConjunct And(PredicateAbsConjunct v1, PredicateAbsConjunct v2)
        {
            if (v1.isFalse || v2.isFalse) return new PredicateAbsConjunct(true, v1.ProcName);
            var ret =  new PredicateAbsConjunct(v1.posPreds.Union(v2.posPreds), v1.negPreds.Union(v2.negPreds), v1.ProcName);
            ret.StrongNormalize();
            return ret;
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
            var pp = posPreds.ToList(); pp.Sort();
            var np = negPreds.ToList(); np.Sort();
            pp.Iter(p => ret = Expr.And(ret, predToExpr(p)));
            np.Iter(p => ret = Expr.And(ret, Expr.Not(predToExpr(p)))); 
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
                ret += string.Format("{0}{1}", first ? "" : " && ", PredicateAbs.PrePreds[ProcName][p]);
                first = false;
            }
            foreach (var p in negPreds)
            {
                ret += string.Format("{0}!{1}", first ? "" : " && ", PredicateAbs.PrePreds[ProcName][p]);
                first = false;
            }
            return ret;
        }
    }

    class FindSummaryPred : MutatingVCExprVisitor<bool>
    {
        public List<Tuple<string, bool, VCExprVar, VCExprNAry>> summaryPreds;
        int assertId;
        private static int CounterId = 0;

        public FindSummaryPred(VCExpressionGenerator gen, int assertId)
            : base(gen)
        {
            summaryPreds = new List<Tuple<string, bool, VCExprVar, VCExprNAry>>();
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

            if (op == null)
            {
                var lop = retnary.Op as VCExprLabelOp;
                if (lop == null) return ret;
                if (lop.pos) return ret;
                if (!lop.label.Equals("@" + assertId.ToString())) return ret;
                
                //var subexpr = retnary[0] as VCExprNAry;
                //if (subexpr == null) return ret;
                //op = subexpr.Op as VCExprBoogieFunctionOp;
                //if (op == null) return ret;

                var subexpr = retnary[0] as VCExprVar;
                if (subexpr == null) return ret;
                if (!subexpr.Name.StartsWith("AbstractHoudiniControl")) return ret;

                for (int i = 0; i < summaryPreds.Count; i++)
                {
                    if (summaryPreds[i].Item3 == subexpr)
                        summaryPreds[i] = Tuple.Create(summaryPreds[i].Item1, true, summaryPreds[i].Item3, summaryPreds[i].Item4);
                }
                return ret;
            }

            string calleeName = op.Func.Name;

            if (!calleeName.EndsWith(AbstractHoudini.summaryPredSuffix))
                return ret;

            var controlConst = Gen.Variable("AbstractHoudiniControl" + CounterId, Microsoft.Boogie.Type.Bool);
            CounterId++;

            summaryPreds.Add(Tuple.Create(calleeName.Substring(0, calleeName.Length - AbstractHoudini.summaryPredSuffix.Length), false, controlConst, retnary));

            return controlConst;
            //return ret;
        }

    }

    class FindExistentialFunctions : MutatingVCExprVisitor<bool>
    {
        public List<Tuple<string, VCExprVar, VCExprNAry>> funcCalls;
        private HashSet<string> existentialFunctions;
        private static int CounterId = 0;

        public FindExistentialFunctions(VCExpressionGenerator gen, HashSet<string> existentialFunctions)
            : base(gen)
        {
            funcCalls = new List<Tuple<string, VCExprVar, VCExprNAry>>();
            this.existentialFunctions = existentialFunctions;
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
            if (op == null) return ret;

            string calleeName = op.Func.Name;

            if (!existentialFunctions.Contains(calleeName))
                return ret;

            var controlConst = Gen.Variable("AbsHoudiniControl" + CounterId, Microsoft.Boogie.Type.Bool);
            CounterId++;

            funcCalls.Add(Tuple.Create(calleeName, controlConst, retnary));

            return controlConst;
        }

    }

    class AbstractHoudiniErrorReporter : ProverInterface.ErrorHandler
    {
        public Model model;

        public AbstractHoudiniErrorReporter()
        {
            model = null;
        }

        public override void OnModel(IList<string> labels, Model model, ProverInterface.Outcome proverOutcome)
        {
            Debug.Assert(model != null);
            if(CommandLineOptions.Clo.PrintErrorModel >= 1) model.Write(Console.Out);
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
            foreach (var impl in p.Implementations)
            {
                m.Add(impl.Name, impl);
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
