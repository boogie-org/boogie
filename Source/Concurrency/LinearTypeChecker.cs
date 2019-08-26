using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public enum LinearKind
    {
        ORDINARY,
        LINEAR,
        LINEAR_IN,
        LINEAR_OUT
    }

    public class LinearQualifier
    {
        public string domainName;
        public LinearKind kind;
        public LinearQualifier(string domainName, LinearKind kind)
        {
            this.domainName = domainName;
            this.kind = kind;
        }
    }

    public class LinearDomain
    {
        public string domainName;
        public Function mapConstBool;
        public Function mapConstInt;
        public Function mapOrBool;
        public Function mapImpBool;
        public Function mapEqInt;
        public Function mapAddInt;
        public Function mapIteInt;
        public Function mapLeInt;
        public List<Axiom> axioms;
        public Type elementType;
        public MapType mapTypeBool;
        public MapType mapTypeInt;
        public Dictionary<Type, Function> collectors;

        public LinearDomain(Program program, string domainName, Dictionary<Type, Function> collectors)
        {
            this.domainName = domainName;
            this.collectors = collectors;
            this.axioms = new List<Axiom>();

            MapType setType = (MapType)collectors.First().Value.OutParams[0].TypedIdent.Type;
            this.elementType = setType.Arguments[0];
            this.mapTypeBool = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.elementType }, Type.Bool);
            this.mapTypeInt = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.elementType }, Type.Int);

            MapConstBool();
            MapConstInt();
            MapOrBool();
            MapImpBool();
            MapEqInt();
            MapAddInt();
            MapIteInt();
            MapLeInt();

            foreach (var axiom in axioms)
            {
                axiom.Expr.Resolve(new ResolutionContext(null));
                axiom.Expr.Typecheck(new TypecheckingContext(null));
            }
        }

        private struct AxiomVariable
        {
            public readonly BoundVariable Bound;
            public readonly IdentifierExpr Ident;
            public AxiomVariable(string name, Type type)
            {
                Bound = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));
                Ident = Expr.Ident(Bound);
            }
        }

        private void MapConstBool()
        {
            this.mapConstBool = new Function(Token.NoToken, "linear_" + domainName + "_MapConstBool",
                                              new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Bool), true) },
                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapConstBool.AddAttribute("builtin", "MapConst");
            }
            else
            {
                AxiomVariable x = new AxiomVariable("x", elementType);
                var trueTerm = Expr.Select(ExprHelper.FunctionCall(mapConstBool, Expr.True), x.Ident);
                var trueAxiomExpr = new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, trueTerm);
                trueAxiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, trueAxiomExpr));
                var falseTerm = Expr.Select(ExprHelper.FunctionCall(mapConstBool, Expr.False), x.Ident);
                var falseAxiomExpr = new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, falseTerm));
                falseAxiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, falseAxiomExpr));
            }
        }

        private void MapConstInt()
        {
            this.mapConstInt = new Function(Token.NoToken, "linear_" + domainName + "_MapConstInt",
                                                      new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Int), true) },
                                                      new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeInt), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapConstInt.AddAttribute("builtin", "MapConst");
            }
            else
            {
                AxiomVariable a = new AxiomVariable("a", Type.Int);
                AxiomVariable x = new AxiomVariable("x", elementType);
                var lhsTerm = Expr.Select(ExprHelper.FunctionCall(mapConstInt, a.Ident), x.Ident);
                var axiomExpr = new ForallExpr(Token.NoToken, new List<Variable> { a.Bound, x.Bound }, Expr.Eq(lhsTerm, a.Ident));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }

        private void MapOrBool()
        {
            this.mapOrBool = new Function(Token.NoToken, "linear_" + domainName + "_MapOr",
                                          new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool), true),
                                                               new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool), true) },
                                          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapOrBool.AddAttribute("builtin", "MapOr");
            }
            else
            {
                AxiomVariable a = new AxiomVariable("a", mapTypeBool);
                AxiomVariable b = new AxiomVariable("b", mapTypeBool);
                AxiomVariable x = new AxiomVariable("x", elementType);
                var mapApplTerm = ExprHelper.FunctionCall(mapOrBool, a.Ident, b.Ident);
                var lhsTerm = Expr.Select(mapApplTerm, x.Ident);
                var rhsTerm = Expr.Or(Expr.Select(a.Ident, x.Ident), Expr.Select(b.Ident, x.Ident));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a.Bound, b.Bound }, null,
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }),
                                               new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, Expr.Eq(lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }

        private void MapImpBool()
        {
            this.mapImpBool = new Function(Token.NoToken, "linear_" + domainName + "_MapImp",
                                                       new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool), true),
                                                                new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool), true) },
                                                       new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapImpBool.AddAttribute("builtin", "MapImp");
            }
            else
            {
                AxiomVariable a = new AxiomVariable("a", mapTypeBool);
                AxiomVariable b = new AxiomVariable("b", mapTypeBool);
                AxiomVariable x = new AxiomVariable("x", elementType);
                var mapApplTerm = ExprHelper.FunctionCall(mapImpBool, a.Ident, b.Ident);
                var lhsTerm = Expr.Select(mapApplTerm, x.Ident);
                var rhsTerm = Expr.Imp(Expr.Select(a.Ident, x.Ident), Expr.Select(b.Ident, x.Ident));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a.Bound, b.Bound }, null,
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }),
                                               new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, Expr.Eq(lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }

        private void MapEqInt()
        {
            this.mapEqInt = new Function(Token.NoToken, "linear_" + domainName + "_MapEq",
                                              new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeInt), true),
                                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt), true) },
                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapEqInt.AddAttribute("builtin", "MapEq");
            }
            else
            {
                AxiomVariable a = new AxiomVariable("a", mapTypeInt);
                AxiomVariable b = new AxiomVariable("b", mapTypeInt);
                AxiomVariable x = new AxiomVariable("x", elementType);
                var mapApplTerm = ExprHelper.FunctionCall(mapEqInt, a.Ident, b.Ident);
                var lhsTerm = Expr.Select(mapApplTerm, x.Ident);
                var rhsTerm = Expr.Eq(Expr.Select(a.Ident, x.Ident), Expr.Select(b.Ident, x.Ident));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a.Bound, b.Bound }, null,
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }),
                                               new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, Expr.Eq(lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }

        private void MapAddInt()
        {
            this.mapAddInt = new Function(Token.NoToken, "linear_" + domainName + "_MapAdd",
                                                      new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeInt), true),
                                                               new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt), true) },
                                                      new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeInt), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapAddInt.AddAttribute("builtin", "MapAdd");
            }
            else
            {
                AxiomVariable a = new AxiomVariable("a", mapTypeInt);
                AxiomVariable b = new AxiomVariable("b", mapTypeInt);
                AxiomVariable x = new AxiomVariable("x", elementType);
                var mapApplTerm = ExprHelper.FunctionCall(mapAddInt, a.Ident, b.Ident);
                var lhsTerm = Expr.Select(mapApplTerm, x.Ident);
                var rhsTerm = Expr.Add(Expr.Select(a.Ident, x.Ident), Expr.Select(b.Ident, x.Ident));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a.Bound, b.Bound }, null,
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }),
                                               new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, Expr.Eq(lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }

        private void MapIteInt()
        {
            this.mapIteInt = new Function(Token.NoToken, "linear_" + domainName + "_MapIteInt",
                                                      new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool), true),
                                                               new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt), true),
                                                               new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeInt), true) },
                                                      new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "d", mapTypeInt), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapIteInt.AddAttribute("builtin", "MapIte");
            }
            else
            {
                AxiomVariable a = new AxiomVariable("a", mapTypeBool);
                AxiomVariable b = new AxiomVariable("b", mapTypeInt);
                AxiomVariable c = new AxiomVariable("c", mapTypeInt);
                AxiomVariable x = new AxiomVariable("x", elementType);
                var mapApplTerm = ExprHelper.FunctionCall(mapIteInt, a.Ident, b.Ident, c.Ident);
                var lhsTerm = Expr.Select(mapApplTerm, x.Ident);
                var rhsTerm = ExprHelper.IfThenElse(Expr.Select(a.Ident, x.Ident), Expr.Select(b.Ident, x.Ident), Expr.Select(c.Ident, x.Ident));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a.Bound, b.Bound, c.Bound }, null,
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }),
                                               new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, Expr.Eq(lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }

        private void MapLeInt()
        {
            this.mapLeInt = new Function(Token.NoToken, "linear_" + domainName + "_MapLe",
                                                      new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeInt), true),
                                                               new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt), true) },
                                                      new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapLeInt.AddAttribute("builtin", "MapLe");
            }
            else
            {
                AxiomVariable a = new AxiomVariable("a", mapTypeInt);
                AxiomVariable b = new AxiomVariable("b", mapTypeInt);
                AxiomVariable x = new AxiomVariable("x", elementType);
                var mapApplTerm = ExprHelper.FunctionCall(mapLeInt, a.Ident, b.Ident);
                var lhsTerm = Expr.Select(mapApplTerm, x.Ident);
                var rhsTerm = Expr.Le(Expr.Select(a.Ident, x.Ident), Expr.Select(b.Ident, x.Ident));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a.Bound, b.Bound }, null,
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }),
                                               new ForallExpr(Token.NoToken, new List<Variable> { x.Bound }, Expr.Eq(lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }
    }

    /// <summary>
    /// Type checker for linear type annotations.
    /// 
    /// The functionality is basically grouped into four parts (see #region's).
    /// 1) TypeCheck parses linear type attributes, sets up the data structures,
    ///    and performs a dataflow check on procedure implementations.
    /// 2) Program transformation(s) to inject logical disjointness annotations.
    /// 3) Generation of linearity-invariant checker procedures for atomic actions.
    /// 4) Erasure procedure to remove all linearity attributes
    ///    (invoked after all other CIVL transformations).
    /// </summary>
    public class LinearTypeChecker : ReadOnlyVisitor
    {
        public Program program;
        public CheckingContext checkingContext;
        public Dictionary<string, LinearDomain> linearDomains;
        public Dictionary<string, Variable> domainNameToHoleVar;

        private CivlTypeChecker ctc;

        private Dictionary<Absy, HashSet<Variable>> availableLinearVars;
        private Dictionary<Variable, LinearQualifier> inParamToLinearQualifier;
        private Dictionary<Variable, string> outParamToDomainName;
        private Dictionary<Variable, string> globalVarToDomainName;

        // Only used in visitor implementation
        private Dictionary<string, Dictionary<Type, Function>> domainNameToCollectors;
        private Dictionary<Variable, string> varToDomainName;

        public LinearTypeChecker(Program program, CivlTypeChecker ctc)
        {
            this.program = program;
            this.ctc = ctc;
            this.checkingContext = new CheckingContext(null);
            this.domainNameToCollectors = new Dictionary<string, Dictionary<Type, Function>>();
            this.availableLinearVars = new Dictionary<Absy, HashSet<Variable>>();
            this.inParamToLinearQualifier = new Dictionary<Variable, LinearQualifier>();
            this.outParamToDomainName = new Dictionary<Variable, string>();
            this.globalVarToDomainName = new Dictionary<Variable, string>();
            this.linearDomains = new Dictionary<string, LinearDomain>();
            this.domainNameToHoleVar = new Dictionary<string, Variable>();
            this.varToDomainName = new Dictionary<Variable, string>();
        }

        private void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
        }

        public string FindDomainName(Variable v)
        {
            if (globalVarToDomainName.ContainsKey(v))
                return globalVarToDomainName[v];
            if (inParamToLinearQualifier.ContainsKey(v))
                return inParamToLinearQualifier[v].domainName;
            if (outParamToDomainName.ContainsKey(v))
                return outParamToDomainName[v];
            string domainName = QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR);
            if (domainName != null)
                return domainName;
            domainName = QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_IN);
            if (domainName != null)
                return domainName;
            return QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_OUT);
        }

        public LinearKind FindLinearKind(Variable v)
        {
            if (globalVarToDomainName.ContainsKey(v))
                return LinearKind.LINEAR;
            if (inParamToLinearQualifier.ContainsKey(v))
                return inParamToLinearQualifier[v].kind;
            if (outParamToDomainName.ContainsKey(v))
                return LinearKind.LINEAR;

            if (QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR) != null)
            {
                return LinearKind.LINEAR;
            }
            else if (QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_IN) != null)
            {
                return LinearKind.LINEAR_IN;
            }
            else if (QKeyValue.FindStringAttribute(v.Attributes, CivlAttributes.LINEAR_OUT) != null)
            {
                return LinearKind.LINEAR_OUT;
            }
            else
            {
                return LinearKind.ORDINARY;
            }
        }

        public Formal LinearDomainInFormal(string domainName)
        { return new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "linear_" + domainName + "_in", linearDomains[domainName].mapTypeBool), true); }

        public LocalVariable LinearDomainAvailableLocal(string domainName)
        { return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "linear_" + domainName + "_available", linearDomains[domainName].mapTypeBool)); }

        private GlobalVariable LinearDomainHoleGlobal(string domainName)
        { return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "linear_" + domainName + "_hole", linearDomains[domainName].mapTypeBool)); }

        public void TypeCheck()
        {
            this.VisitProgram(program);
            foreach (var variable in varToDomainName.Keys)
            {
                string domainName = FindDomainName(variable);
                if (!domainNameToCollectors.ContainsKey(domainName) ||
                   !domainNameToCollectors[domainName].ContainsKey(variable.TypedIdent.Type))
                {
                    Error(variable, "Missing collector for linear variable " + variable.Name);
                }
            }
            foreach (string domainName in domainNameToCollectors.Keys)
            {
                var collectors = domainNameToCollectors[domainName];
                if (collectors.Count == 0) continue;
                this.linearDomains[domainName] = new LinearDomain(program, domainName, collectors);
            }
            foreach (Absy absy in this.availableLinearVars.Keys)
            {
                availableLinearVars[absy].RemoveWhere(v => v is GlobalVariable);
            }
        }

        #region Visitor Implementation
        public override Program VisitProgram(Program node)
        {
            foreach (GlobalVariable g in program.GlobalVariables)
            {
                string domainName = FindDomainName(g);
                if (domainName != null)
                {
                    globalVarToDomainName[g] = domainName;
                }
            }
            return base.VisitProgram(node);
        }

        public override Function VisitFunction(Function node)
        {
            string domainName = QKeyValue.FindStringAttribute(node.Attributes, CivlAttributes.LINEAR);
            if (domainName != null)
            {
                if (!domainNameToCollectors.ContainsKey(domainName))
                {
                    domainNameToCollectors[domainName] = new Dictionary<Type, Function>();
                }
                if (node.InParams.Count == 1 && node.OutParams.Count == 1)
                {
                    Type inType = node.InParams[0].TypedIdent.Type;
                    MapType outType = node.OutParams[0].TypedIdent.Type as MapType;
                    if (domainNameToCollectors[domainName].ContainsKey(inType))
                    {
                        Error(node, string.Format("A collector for domain for input type has already been defined"));
                    }
                    else if (outType == null || outType.Arguments.Count != 1 || !outType.Result.Equals(Type.Bool))
                    {
                        Error(node, "Output of a linear domain collector should be of set type");
                    }
                    else
                    {
                        domainNameToCollectors[domainName][inType] = node;
                    }
                }
                else
                {
                    Error(node, "Linear domain collector should have one input and one output parameter");
                }
            }
            return base.VisitFunction(node);
        }
        public override Implementation VisitImplementation(Implementation node)
        {
            if (ctc.procToAtomicAction.ContainsKey(node.Proc))
                return node;
            if (ctc.procToAtomicAction.Values.SelectMany(a => a.layerToActionCopy.Values).Select(a => a.impl).Contains(node))
                return node;

            node.PruneUnreachableBlocks();
            node.ComputePredecessorsForBlocks();
            GraphUtil.Graph<Block> graph = Program.GraphFromImpl(node);
            graph.ComputeLoops();

            HashSet<Variable> start = new HashSet<Variable>(globalVarToDomainName.Keys);
            for (int i = 0; i < node.InParams.Count; i++)
            {
                Variable v = node.Proc.InParams[i];
                string domainName = FindDomainName(v);
                if (domainName != null)
                {
                    var kind = FindLinearKind(v);
                    inParamToLinearQualifier[node.InParams[i]] = new LinearQualifier(domainName, kind);
                    if (kind == LinearKind.LINEAR || kind == LinearKind.LINEAR_IN)
                    {
                        start.Add(node.InParams[i]);
                    }
                }
            }
            for (int i = 0; i < node.OutParams.Count; i++)
            {
                string domainName = FindDomainName(node.Proc.OutParams[i]);
                if (domainName != null)
                {
                    outParamToDomainName[node.OutParams[i]] = domainName;
                }
            }

            var oldErrorCount = checkingContext.ErrorCount;
            var impl = base.VisitImplementation(node);
            if (oldErrorCount < checkingContext.ErrorCount)
                return impl;

            Stack<Block> dfsStack = new Stack<Block>();
            HashSet<Block> dfsStackAsSet = new HashSet<Block>();
            availableLinearVars[node.Blocks[0]] = start;
            dfsStack.Push(node.Blocks[0]);
            dfsStackAsSet.Add(node.Blocks[0]);
            while (dfsStack.Count > 0)
            {
                Block b = dfsStack.Pop();
                dfsStackAsSet.Remove(b);
                HashSet<Variable> end = PropagateAvailableLinearVarsAcrossBlock(b);
                if (b.TransferCmd is ReturnCmd)
                {
                    foreach (GlobalVariable g in globalVarToDomainName.Keys.Except(end))
                    {
                        Error(b.TransferCmd, string.Format("Global variable {0} must be available at a return", g.Name));
                    }
                    foreach (Variable v in node.InParams)
                    {
                        if (FindDomainName(v) == null || FindLinearKind(v) == LinearKind.LINEAR_IN || end.Contains(v)) continue;
                        Error(b.TransferCmd, string.Format("Input variable {0} must be available at a return", v.Name));
                    }
                    foreach (Variable v in node.OutParams)
                    {
                        if (FindDomainName(v) == null || end.Contains(v)) continue;
                        Error(b.TransferCmd, string.Format("Output variable {0} must be available at a return", v.Name));
                    }
                    continue;
                }
                GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    if (!availableLinearVars.ContainsKey(target))
                    {
                        availableLinearVars[target] = new HashSet<Variable>(end);
                        dfsStack.Push(target);
                        dfsStackAsSet.Add(target);
                    }
                    else
                    {
                        var savedAvailableVars = new HashSet<Variable>(availableLinearVars[target]);
                        availableLinearVars[target].IntersectWith(end);
                        if (savedAvailableVars.IsProperSupersetOf(availableLinearVars[target]) && !dfsStackAsSet.Contains(target))
                        {
                            dfsStack.Push(target);
                            dfsStackAsSet.Add(target);
                        }
                    }
                }
            }

            if (graph.Reducible)
            {
                foreach (Block header in graph.Headers)
                {
                    foreach (GlobalVariable g in globalVarToDomainName.Keys.Except(availableLinearVars[header]))
                    {
                        Error(header, string.Format("Global variable {0} must be available at a loop head", g.Name));
                    }
                }
            }
            return impl;
        }
        private void AddAvailableVars(CallCmd callCmd, HashSet<Variable> start)
        {
            foreach (IdentifierExpr ie in callCmd.Outs)
            {
                if (FindDomainName(ie.Decl) == null) continue;
                start.Add(ie.Decl);
            }
            for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
            {
                if (callCmd.Ins[i] is IdentifierExpr ie)
                {
                    Variable v = callCmd.Proc.InParams[i];
                    if (FindDomainName(v) == null) continue;
                    if (FindLinearKind(v) == LinearKind.LINEAR_OUT)
                    {
                        start.Add(ie.Decl);
                    }
                }
            }
        }
        private void AddAvailableVars(ParCallCmd parCallCmd, HashSet<Variable> start)
        {
            foreach (CallCmd callCmd in parCallCmd.CallCmds)
            {
                AddAvailableVars(callCmd, start);
            }
        }
        private HashSet<Variable> PropagateAvailableLinearVarsAcrossBlock(Block b)
        {
            HashSet<Variable> start = new HashSet<Variable>(availableLinearVars[b]);
            foreach (Cmd cmd in b.Cmds)
            {
                if (cmd is AssignCmd assignCmd)
                {
                    for (int i = 0; i < assignCmd.Lhss.Count; i++)
                    {
                        if (FindDomainName(assignCmd.Lhss[i].DeepAssignedVariable) == null) continue;
                        IdentifierExpr ie = assignCmd.Rhss[i] as IdentifierExpr;
                        if (!start.Contains(ie.Decl))
                        {
                            Error(ie, "unavailable source for a linear read");
                        }
                        else
                        {
                            start.Remove(ie.Decl);
                        }
                    }
                    foreach (AssignLhs assignLhs in assignCmd.Lhss)
                    {
                        if (FindDomainName(assignLhs.DeepAssignedVariable) == null) continue;
                        start.Add(assignLhs.DeepAssignedVariable);
                    }
                }
                else if (cmd is CallCmd callCmd)
                {
                    foreach (GlobalVariable g in globalVarToDomainName.Keys.Except(start))
                    {
                        Error(cmd, string.Format("Global variable {0} must be available at a call", g.Name));
                    }
                    for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
                    {
                        Variable param = callCmd.Proc.InParams[i];
                        if (FindDomainName(param) == null) continue;
                        IdentifierExpr ie = callCmd.Ins[i] as IdentifierExpr;
                        LinearKind paramKind = FindLinearKind(param);
                        if (start.Contains(ie.Decl))
                        {
                            if (callCmd.IsAsync || paramKind == LinearKind.LINEAR_IN)
                            {
                                start.Remove(ie.Decl);
                            }
                        }
                        else
                        {
                            if (paramKind == LinearKind.LINEAR_OUT)
                            {
                                start.Add(ie.Decl);
                            }
                            else
                            {
                                Error(ie, "unavailable source for a linear read");
                            }
                        }
                    }
                    AddAvailableVars(callCmd, start);
                    availableLinearVars[callCmd] = new HashSet<Variable>(start);
                }
                else if (cmd is ParCallCmd parCallCmd)
                {
                    foreach (GlobalVariable g in globalVarToDomainName.Keys.Except(start))
                    {
                        Error(cmd, string.Format("Global variable {0} must be available at a call", g.Name));
                    }
                    foreach (CallCmd parCallCallCmd in parCallCmd.CallCmds)
                    {
                        for (int i = 0; i < parCallCallCmd.Proc.InParams.Count; i++)
                        {
                            Variable param = parCallCallCmd.Proc.InParams[i];
                            if (FindDomainName(param) == null) continue;
                            IdentifierExpr ie = parCallCallCmd.Ins[i] as IdentifierExpr;
                            LinearKind paramKind = FindLinearKind(param);
                            if (start.Contains(ie.Decl))
                            {
                                if (paramKind == LinearKind.LINEAR_IN)
                                {
                                    start.Remove(ie.Decl);
                                }
                            }
                            else
                            {
                                if (paramKind == LinearKind.LINEAR_OUT)
                                {
                                    start.Add(ie.Decl);
                                }
                                else
                                {
                                    Error(ie, "unavailable source for a linear read");
                                }
                            }
                        }
                    }
                    AddAvailableVars(parCallCmd, start);
                    availableLinearVars[parCallCmd] = new HashSet<Variable>(start);
                }
                else if (cmd is HavocCmd havocCmd)
                {
                    foreach (IdentifierExpr ie in havocCmd.Vars)
                    {
                        if (FindDomainName(ie.Decl) == null) continue;
                        start.Remove(ie.Decl);
                    }
                }
                else if (cmd is YieldCmd)
                {
                    foreach (GlobalVariable g in globalVarToDomainName.Keys.Except(start))
                    {
                        Error(cmd, string.Format("Global variable {0} must be available at a yield", g.Name));
                    }
                    availableLinearVars[cmd] = new HashSet<Variable>(start);
                }
            }
            return start;
        }
        public override Variable VisitVariable(Variable node)
        {
            string domainName = FindDomainName(node);
            if (domainName != null)
            {
                varToDomainName[node] = domainName;
                LinearKind kind = FindLinearKind(node);
                if (kind != LinearKind.LINEAR)
                {
                    if (node is GlobalVariable || node is LocalVariable || (node is Formal formal && !formal.InComing))
                    {
                        Error(node, "Variable must be declared linear (as opposed to linear_in or linear_out)");
                    }
                }
            }
            return base.VisitVariable(node);
        }
        public override Cmd VisitAssignCmd(AssignCmd node)
        {
            HashSet<Variable> rhsVars = new HashSet<Variable>();
            for (int i = 0; i < node.Lhss.Count; i++)
            {
                AssignLhs lhs = node.Lhss[i];
                Variable lhsVar = lhs.DeepAssignedVariable;
                string domainName = FindDomainName(lhsVar);
                if (domainName == null) continue;
                if (!(lhs is SimpleAssignLhs))
                {
                    Error(node, string.Format("Only simple assignment allowed on linear variable {0}", lhsVar.Name));
                    continue;
                }
                IdentifierExpr rhs = node.Rhss[i] as IdentifierExpr;
                if (rhs == null)
                {
                    Error(node, string.Format("Only variable can be assigned to linear variable {0}", lhsVar.Name));
                    continue;
                }
                string rhsDomainName = FindDomainName(rhs.Decl);
                if (rhsDomainName == null)
                {
                    Error(node, string.Format("Only linear variable can be assigned to linear variable {0}", lhsVar.Name));
                    continue;
                }
                if (domainName != rhsDomainName)
                {
                    Error(node, string.Format("Linear variable of domain {0} cannot be assigned to linear variable of domain {1}", rhsDomainName, domainName));
                    continue;
                }
                if (rhsVars.Contains(rhs.Decl))
                {
                    Error(node, string.Format("Linear variable {0} can occur only once in the right-hand-side of an assignment", rhs.Decl.Name));
                    continue;
                }
                rhsVars.Add(rhs.Decl);
            }
            return base.VisitAssignCmd(node);
        }
        public override Cmd VisitCallCmd(CallCmd node)
        {
            HashSet<Variable> inVars = new HashSet<Variable>();
            for (int i = 0; i < node.Proc.InParams.Count; i++)
            {
                Variable formal = node.Proc.InParams[i];
                string domainName = FindDomainName(formal);
                if (domainName == null) continue;
                IdentifierExpr actual = node.Ins[i] as IdentifierExpr;
                if (actual == null)
                {
                    Error(node, string.Format("Only variable can be passed to linear parameter {0}", formal.Name));
                    continue;
                }
                string actualDomainName = FindDomainName(actual.Decl);
                if (actualDomainName == null)
                {
                    Error(node, string.Format("Only a linear argument can be passed to linear parameter {0}", formal.Name));
                    continue;
                }
                if (domainName != actualDomainName)
                {
                    Error(node, "The domains of formal and actual parameters must be the same");
                    continue;
                }
                if (actual.Decl is GlobalVariable)
                {
                    Error(node, "Only local linear variable can be an actual input parameter of a procedure call");
                    continue;
                }
                if (inVars.Contains(actual.Decl))
                {
                    Error(node, string.Format("Linear variable {0} can occur only once as an input parameter", actual.Decl.Name));
                    continue;
                }
                inVars.Add(actual.Decl);
            }
            for (int i = 0; i < node.Proc.OutParams.Count; i++)
            {
                IdentifierExpr actual = node.Outs[i];
                string actualDomainName = FindDomainName(actual.Decl);
                if (actualDomainName == null) continue;
                Variable formal = node.Proc.OutParams[i];
                string domainName = FindDomainName(formal);
                if (domainName == null)
                {
                    Error(node, "Only a linear variable can be passed to a linear parameter");
                    continue;
                }
                if (domainName != actualDomainName)
                {
                    Error(node, "The domains of formal and actual parameters must be the same");
                    continue;
                }
                if (actual.Decl is GlobalVariable)
                {
                    Error(node, "Only local linear variable can be actual output parameter of a procedure call");
                    continue;
                }
            }
            return base.VisitCallCmd(node);
        }
        public override Cmd VisitParCallCmd(ParCallCmd node)
        {
            HashSet<Variable> parallelCallInvars = new HashSet<Variable>();
            foreach (CallCmd callCmd in node.CallCmds)
            {
                for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
                {
                    Variable formal = callCmd.Proc.InParams[i];
                    string domainName = FindDomainName(formal);
                    if (domainName == null) continue;
                    IdentifierExpr actual = callCmd.Ins[i] as IdentifierExpr;
                    if (parallelCallInvars.Contains(actual.Decl))
                    {
                        Error(node, string.Format("Linear variable {0} can occur only once as an input parameter of a parallel call", actual.Decl.Name));
                    }
                    else
                    {
                        parallelCallInvars.Add(actual.Decl);
                    }
                }
            }
            return base.VisitParCallCmd(node);
        }

        public override Requires VisitRequires(Requires requires)
        {
            return requires;
        }

        public override Ensures VisitEnsures(Ensures ensures)
        {
            return ensures;
        }
        #endregion

        #region Program Transformation
        public void Transform()
        {
            // The disjointness expressions injected below include an additional placeholder variable (a "hole")
            // which is substituted in yield checker implementations.
            foreach (string domainName in linearDomains.Keys)
            {
                GlobalVariable g = LinearDomainHoleGlobal(domainName);
                program.AddTopLevelDeclaration(g);
                domainNameToHoleVar[domainName] = g;
            }

            foreach (var impl in program.Implementations)
            {
                foreach (Block b in impl.Blocks)
                {
                    List<Cmd> newCmds = new List<Cmd>();
                    for (int i = 0; i < b.Cmds.Count; i++)
                    {
                        Cmd cmd = b.Cmds[i];
                        newCmds.Add(cmd);
                        if (cmd is CallCmd || cmd is ParCallCmd || cmd is YieldCmd)
                        {
                            AddDisjointnessExpr(newCmds, cmd);
                        }
                    }
                    b.Cmds = newCmds;
                }

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
                            List<Cmd> newCmds = new List<Cmd>();
                            AddDisjointnessExpr(newCmds, header);
                            newCmds.AddRange(header.Cmds);
                            header.Cmds = newCmds;
                        }
                    }
                }
            }

            foreach (var proc in program.Procedures)
            {
                Dictionary<string, HashSet<Variable>> domainNameToInputScope = new Dictionary<string, HashSet<Variable>>();
                Dictionary<string, HashSet<Variable>> domainNameToOutputScope = new Dictionary<string, HashSet<Variable>>();
                foreach (var domainName in linearDomains.Keys)
                {
                    domainNameToInputScope[domainName] = new HashSet<Variable>();
                    domainNameToOutputScope[domainName] = new HashSet<Variable>();
                }
                foreach (Variable v in globalVarToDomainName.Keys)
                {
                    var domainName = globalVarToDomainName[v];
                    domainNameToInputScope[domainName].Add(v);
                    domainNameToOutputScope[domainName].Add(v);
                }
                foreach (Variable v in proc.InParams)
                {
                    var domainName = FindDomainName(v);
                    if (domainName == null) continue;
                    if (!this.linearDomains.ContainsKey(domainName)) continue;
                    domainNameToInputScope[domainName].Add(v);
                }
                foreach (Variable v in proc.OutParams)
                {
                    var domainName = FindDomainName(v);
                    if (domainName == null) continue;
                    if (!this.linearDomains.ContainsKey(domainName)) continue;
                    domainNameToOutputScope[domainName].Add(v);
                }
                // TODO: Also add linear and linear_out parameters to domainNameToOutputScope?
                //       This should still be sound and strengthen the generated postcondition.
                foreach (var domainName in linearDomains.Keys)
                {
                    Expr req = DisjointnessExpr(domainName, domainNameToInputScope[domainName]);
                    Expr ens = DisjointnessExpr(domainName, domainNameToOutputScope[domainName]);
                    if (!req.Equals(Expr.True))
                        proc.Requires.Add(new Requires(true, req));
                    if (!ens.Equals(Expr.True))
                        proc.Ensures.Add(new Ensures(true, ens));
                }
            }

            foreach (LinearDomain domain in linearDomains.Values)
            {
                program.AddTopLevelDeclaration(domain.mapConstBool);
                program.AddTopLevelDeclaration(domain.mapConstInt);
                program.AddTopLevelDeclaration(domain.mapEqInt);
                program.AddTopLevelDeclaration(domain.mapImpBool);
                program.AddTopLevelDeclaration(domain.mapOrBool);
                program.AddTopLevelDeclaration(domain.mapAddInt);
                program.AddTopLevelDeclaration(domain.mapLeInt);
                program.AddTopLevelDeclaration(domain.mapIteInt);
                foreach (Axiom axiom in domain.axioms)
                {
                    program.AddTopLevelDeclaration(axiom);
                }
            }

            //int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
            //CommandLineOptions.Clo.PrintUnstructured = 1;
            //PrintBplFile("lsd.bpl", program, false, false);
            //CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
        }

        public IEnumerable<Variable> AvailableLinearVars(Absy absy)
        {
            if (availableLinearVars.ContainsKey(absy))
            {
                return availableLinearVars[absy];
            }
            else
            {
                return new HashSet<Variable>();
            }
        }

        private void AddDisjointnessExpr(List<Cmd> newCmds, Absy absy)
        {
            Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
            foreach (var domainName in linearDomains.Keys)
            {
                domainNameToScope[domainName] = new HashSet<Variable>();
            }
            foreach (Variable v in AvailableLinearVars(absy))
            {
                var domainName = FindDomainName(v);
                domainNameToScope[domainName].Add(v);
            }
            foreach (Variable v in globalVarToDomainName.Keys)
            {
                var domainName = FindDomainName(v);
                domainNameToScope[domainName].Add(v);
            }
            foreach (string domainName in linearDomains.Keys)
            {
                Expr expr = DisjointnessExpr(domainName, domainNameToHoleVar[domainName], domainNameToScope[domainName]);
                if (!expr.Equals(Expr.True))
                    newCmds.Add(new AssumeCmd(Token.NoToken, expr));
            }
        }

        private Expr SubsetExpr(LinearDomain domain, Expr ie, Variable partition, int partitionCount)
        {
            Expr e = ExprHelper.FunctionCall(domain.mapConstInt, Expr.Literal(partitionCount));
            e = ExprHelper.FunctionCall(domain.mapEqInt, Expr.Ident(partition), e);
            e = ExprHelper.FunctionCall(domain.mapImpBool, ie, e);
            e = Expr.Eq(e, ExprHelper.FunctionCall(domain.mapConstBool, Expr.True));
            return e;
        }

        private Expr DisjointnessExpr(string domainName, Variable holeVar, HashSet<Variable> scope)
        {
            int count = 0;
            List<Expr> subsetExprs = new List<Expr>();

            if (scope.Count == 0 || (holeVar == null && scope.Count == 1))
            {
                return Expr.True;
            }

            LinearDomain domain = linearDomains[domainName];
            BoundVariable partition = new BoundVariable(
              Token.NoToken,
              new TypedIdent(Token.NoToken,
                             string.Format("partition_{0}", domainName),
                             domain.mapTypeInt));

            if (holeVar != null)
            {
                subsetExprs.Add(SubsetExpr(domain, Expr.Ident(holeVar), partition, count));
                count++;
            }

            foreach (Variable v in scope)
            {
                Expr ie = ExprHelper.FunctionCall(domain.collectors[v.TypedIdent.Type], Expr.Ident(v));
                subsetExprs.Add(SubsetExpr(domain, ie, partition, count));
                count++;
            }
            var expr = new ExistsExpr(Token.NoToken,
                                      new List<Variable> { partition },
                                      Expr.And(subsetExprs));
            expr.Resolve(new ResolutionContext(null));
            expr.Typecheck(new TypecheckingContext(null));

            return expr;
        }

        public Expr DisjointnessExpr(string domainName, HashSet<Variable> scope)
        {
            return DisjointnessExpr(domainName, null, scope);
        }
        #endregion

        #region Linearity Invariant Checker
        public static void AddCheckers(LinearTypeChecker linearTypeChecker, CivlTypeChecker civlTypeChecker, List<Declaration> decls)
        {
            if (civlTypeChecker.procToAtomicAction.Count == 0)
                return;

            foreach (var action in civlTypeChecker.procToAtomicAction.Values
                .SelectMany(a => a.layerToActionCopy.Values))
            {
                AddChecker(action, linearTypeChecker, decls);
            }
        }

        private static void AddChecker(AtomicActionCopy action, LinearTypeChecker linearTypeChecker, List<Declaration> decls)
        {
            // Note: The implementation should be used as the variables in the
            //       gate are bound to implementation and not to the procedure.
            Implementation impl = action.impl;
            List<Variable> inputs = impl.InParams;
            List<Variable> outputs = impl.OutParams;

            // Linear out vars
            List<Variable> outVars;
            {
                LinearKind[] validKinds = { LinearKind.LINEAR, LinearKind.LINEAR_OUT };
                outVars = inputs.
                    Union(outputs).
                    Union(action.modifiedGlobalVars).
                    Where(x => validKinds.Contains(linearTypeChecker.FindLinearKind(x)))
                    .ToList();
            }

            if (outVars.Count == 0) return;

            // Linear in vars
            List<Variable> inVars;
            {
                LinearKind[] validKinds = { LinearKind.LINEAR, LinearKind.LINEAR_IN };
                inVars = inputs.
                    Union(action.modifiedGlobalVars).
                    Where(x => validKinds.Contains(linearTypeChecker.FindLinearKind(x)))
                    .ToList();
            }

            List<Requires> requires = action.gate.Select(a => new Requires(false, a.Expr)).ToList();
            List<Ensures> ensures = new List<Ensures>();

            // Generate linearity checks
            IEnumerable<string> domainNames = outVars.
                Select(linearTypeChecker.FindDomainName).Distinct();
            foreach (var domainName in domainNames)
            {
                LinearDomain domain = linearTypeChecker.linearDomains[domainName];
                Expr inMultiset = linearTypeChecker.PermissionMultiset(domain, inVars, true);
                Expr outMultiset = linearTypeChecker.PermissionMultiset(domain, outVars);
                Expr subsetExpr = ExprHelper.FunctionCall(domain.mapLeInt, outMultiset, inMultiset);
                Expr eqExpr = Expr.Eq(subsetExpr, ExprHelper.FunctionCall(domain.mapConstBool, Expr.True));

                Ensures ensureCheck = new Ensures(action.proc.tok, false, eqExpr, null);
                ensureCheck.ErrorData = string.Format("Linearity invariant for domain {0} is not preserved by {1}.",
                    domainName, action.proc.Name);
                ResolutionContext rc = new ResolutionContext(null);
                rc.StateMode = ResolutionContext.State.Two;
                ensureCheck.Resolve(rc);
                ensureCheck.Typecheck(new TypecheckingContext(null));
                ensures.Add(ensureCheck);
            }

            // Create blocks
            List<Block> blocks = new List<Block>();
            {
                CallCmd cmd = new CallCmd(Token.NoToken, impl.Name,
                    inputs.Select(Expr.Ident).ToList<Expr>(),
                    outputs.Select(Expr.Ident).ToList());
                cmd.Proc = action.proc;
                Block block = new Block(Token.NoToken, "entry", new List<Cmd> { cmd }, new ReturnCmd(Token.NoToken));
                blocks.Add(block);
            }

            // Create the whole check procedure
            string checkerName = string.Format("LinearityChecker_{0}", action.proc.Name);
            Procedure linCheckerProc = new Procedure(Token.NoToken, checkerName, new List<TypeVariable>(),
                inputs, outputs, requires, action.proc.Modifies, ensures);
            Implementation linCheckImpl = new Implementation(Token.NoToken, checkerName,
                new List<TypeVariable>(), inputs, outputs, new List<Variable> { }, blocks);
            linCheckImpl.Proc = linCheckerProc;
            decls.Add(linCheckImpl);
            decls.Add(linCheckerProc);
        }

        private Expr PermissionMultiset(LinearDomain domain, IEnumerable<Variable> vars, bool useOldExpr = false)
        {
            Expr mapConstInt0 = ExprHelper.FunctionCall(domain.mapConstInt, Expr.Literal(0));
            Expr mapConstInt1 = ExprHelper.FunctionCall(domain.mapConstInt, Expr.Literal(1));

            var terms = vars.
                    Where(x => FindDomainName(x) == domain.domainName).
                    Select(x => ExprHelper.FunctionCall(domain.mapIteInt,
                        CollectedLinearVariable(x, domain.collectors[x.TypedIdent.Type], useOldExpr),
                        mapConstInt1,
                        mapConstInt0)).
                    ToList<Expr>();

            if (terms.Count == 0)
                return mapConstInt0;
            return terms.Aggregate((x, y) => ExprHelper.FunctionCall(domain.mapAddInt, x, y));
        }

        private Expr CollectedLinearVariable(Variable v, Function collector, bool useOldExpr = false)
        {
            Expr arg = Expr.Ident(v);
            if (useOldExpr)
                arg = ExprHelper.Old(arg);
            return ExprHelper.FunctionCall(collector, arg);
        }
        #endregion

        #region Annotation Eraser
        public void EraseLinearAnnotations()
        {
            new LinearTypeEraser().VisitProgram(program);
        }

        public class LinearTypeEraser : ReadOnlyVisitor
        {
            public override Variable VisitVariable(Variable node)
            {
                CivlAttributes.RemoveLinearAttribute(node);
                return base.VisitVariable(node);
            }

            public override Function VisitFunction(Function node)
            {
                CivlAttributes.RemoveLinearAttribute(node);
                return base.VisitFunction(node);
            }
        }
        #endregion
    }
}
