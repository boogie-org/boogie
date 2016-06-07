using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Microsoft.Boogie
{
    public class LinearEraser : ReadOnlyVisitor
    {
        private QKeyValue RemoveLinearAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveLinearAttribute(iter.Next);
            return (iter.Key == "linear" || iter.Key == "linear_in" || iter.Key == "linear_out") ? iter.Next : iter;
        }

        public override Variable VisitVariable(Variable node)
        {
            node.Attributes = RemoveLinearAttribute(node.Attributes);
            return base.VisitVariable(node);
        }

        public override Function VisitFunction(Function node)
        {
            node.Attributes = RemoveLinearAttribute(node.Attributes);
            return base.VisitFunction(node);
        }
    }

    public enum LinearKind {
        LINEAR,
        LINEAR_IN,
        LINEAR_OUT
    }

    public class LinearTypeChecker : ReadOnlyVisitor
    {
        public Program program;
        public int errorCount;
        public CheckingContext checkingContext;
        public Dictionary<string, Dictionary<Type, Function>> domainNameToCollectors;
        private Dictionary<Absy, HashSet<Variable>> availableLinearVars;
        public Dictionary<Variable, LinearQualifier> inParamToLinearQualifier;
        public Dictionary<Variable, string> outParamToDomainName;
        public Dictionary<Variable, string> varToDomainName;
        public Dictionary<Variable, string> globalVarToDomainName;
        public Dictionary<string, LinearDomain> linearDomains;

        public LinearTypeChecker(Program program)
        {
            this.program = program;
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.domainNameToCollectors = new Dictionary<string, Dictionary<Type, Function>>();
            this.availableLinearVars = new Dictionary<Absy, HashSet<Variable>>();
            this.inParamToLinearQualifier = new Dictionary<Variable, LinearQualifier>();
            this.outParamToDomainName = new Dictionary<Variable, string>();
            this.varToDomainName = new Dictionary<Variable, string>();
            this.globalVarToDomainName = new Dictionary<Variable, string>();
            this.linearDomains = new Dictionary<string, LinearDomain>();
        }
        public void TypeCheck()
        {
            this.VisitProgram(program);
            foreach (string domainName in domainNameToCollectors.Keys)
            {
                var collectors = domainNameToCollectors[domainName];
                if (collectors.Count == 0) continue;
                this.linearDomains[domainName] = new LinearDomain(program, domainName, collectors);
            }
            Dictionary<Absy, HashSet<Variable>> newAvailableLinearVars = new Dictionary<Absy, HashSet<Variable>>();
            foreach (Absy absy in this.availableLinearVars.Keys)
            {
                HashSet<Variable> vars = new HashSet<Variable>();
                foreach (Variable var in this.availableLinearVars[absy])
                {
                    if (var is GlobalVariable) continue;
                    string domainName = FindDomainName(var);
                    if (this.linearDomains.ContainsKey(domainName))
                    {
                        vars.Add(var);
                    }
                }
                newAvailableLinearVars[absy] = vars;
            }
            this.availableLinearVars = newAvailableLinearVars;
            var temp = new Dictionary<Variable, string>();
            foreach (Variable v in outParamToDomainName.Keys)
            {
                if (linearDomains.ContainsKey(outParamToDomainName[v]))
                    temp[v] = outParamToDomainName[v];
            }
            this.outParamToDomainName = temp;
            temp = new Dictionary<Variable, string>();
            foreach (Variable v in varToDomainName.Keys)
            {
                if (linearDomains.ContainsKey(varToDomainName[v]))
                    temp[v] = varToDomainName[v];
            }
            this.varToDomainName = temp;
            temp = new Dictionary<Variable, string>();
            foreach (Variable v in globalVarToDomainName.Keys)
            {
                if (linearDomains.ContainsKey(globalVarToDomainName[v]))
                    temp[v] = globalVarToDomainName[v];
            }
            this.globalVarToDomainName = temp;
        }
        private void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
            errorCount++;
        }
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
            string domainName = QKeyValue.FindStringAttribute(node.Attributes, "linear");
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
            
            var oldErrorCount = this.errorCount;
            var impl = base.VisitImplementation(node);
            if (oldErrorCount < this.errorCount)
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
        public void AddAvailableVars(CallCmd callCmd, HashSet<Variable> start)
        {
            foreach (IdentifierExpr ie in callCmd.Outs)
            {
                if (FindDomainName(ie.Decl) == null) continue;
                start.Add(ie.Decl);
            }
            for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
            {
                IdentifierExpr ie = callCmd.Ins[i] as IdentifierExpr;
                if (ie == null) continue;
                Variable v = callCmd.Proc.InParams[i];
                if (FindDomainName(v) == null) continue;
                if (FindLinearKind(v) == LinearKind.LINEAR_OUT)
                {
                    start.Add(ie.Decl);
                }
            }
        }
        public void AddAvailableVars(ParCallCmd parCallCmd, HashSet<Variable> start)
        {
            foreach (CallCmd callCmd in parCallCmd.CallCmds)
            {
                AddAvailableVars(callCmd, start);
            }
        }
        private HashSet<Variable> PropagateAvailableLinearVarsAcrossBlock(Block b) {
            HashSet<Variable> start = new HashSet<Variable>(availableLinearVars[b]);
            foreach (Cmd cmd in b.Cmds)
            {
                if (cmd is AssignCmd)
                {
                    AssignCmd assignCmd = (AssignCmd)cmd;
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
                else if (cmd is CallCmd)
                {
                    foreach (GlobalVariable g in globalVarToDomainName.Keys.Except(start))
                    {
                        Error(cmd, string.Format("Global variable {0} must be available at a call", g.Name));
                    }
                    CallCmd callCmd = (CallCmd)cmd;
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
                    availableLinearVars[callCmd] = new HashSet<Variable>(start);
                    AddAvailableVars(callCmd, start);
                }
                else if (cmd is ParCallCmd)
                {
                    foreach (GlobalVariable g in globalVarToDomainName.Keys.Except(start))
                    {
                        Error(cmd, string.Format("Global variable {0} must be available at a call", g.Name));
                    }
                    ParCallCmd parCallCmd = (ParCallCmd)cmd;
                    foreach (CallCmd callCmd in parCallCmd.CallCmds)
                    {
                        for (int i = 0; i < callCmd.Proc.InParams.Count; i++)
                        {
                            Variable param = callCmd.Proc.InParams[i];
                            if (FindDomainName(param) == null) continue;
                            IdentifierExpr ie = callCmd.Ins[i] as IdentifierExpr;
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
                    availableLinearVars[parCallCmd] = new HashSet<Variable>(start);
                    AddAvailableVars(parCallCmd, start);
                }
                else if (cmd is HavocCmd)
                {
                    HavocCmd havocCmd = (HavocCmd)cmd;
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
        public string FindDomainName(Variable v)
        {
            if (globalVarToDomainName.ContainsKey(v))
                return globalVarToDomainName[v];
            if (inParamToLinearQualifier.ContainsKey(v))
                return inParamToLinearQualifier[v].domainName;
            if (outParamToDomainName.ContainsKey(v))
                return outParamToDomainName[v];
            string domainName = QKeyValue.FindStringAttribute(v.Attributes, "linear");
            if (domainName != null)
                return domainName;
            domainName = QKeyValue.FindStringAttribute(v.Attributes, "linear_in");
            if (domainName != null)
                return domainName;
            return QKeyValue.FindStringAttribute(v.Attributes, "linear_out");
        }
        public LinearKind FindLinearKind(Variable v)
        {
            if (globalVarToDomainName.ContainsKey(v))
                return LinearKind.LINEAR;
            if (inParamToLinearQualifier.ContainsKey(v))
                return inParamToLinearQualifier[v].kind;
            if (outParamToDomainName.ContainsKey(v))
                return LinearKind.LINEAR;

            if (QKeyValue.FindStringAttribute(v.Attributes, "linear") != null)
            {
                return LinearKind.LINEAR;
            }
            else if (QKeyValue.FindStringAttribute(v.Attributes, "linear_in") != null)
            { 
                return LinearKind.LINEAR_IN; 
            }
            else if (QKeyValue.FindStringAttribute(v.Attributes, "linear_out") != null)
            {
                return LinearKind.LINEAR_OUT;
            }
            else
            {
                Debug.Assert(false);
                return LinearKind.LINEAR;
            }
        }
        public override Variable VisitVariable(Variable node)
        {
            string domainName = FindDomainName(node);
            if (domainName != null)
            {
                if (!domainNameToCollectors.ContainsKey(domainName))
                {
                    domainNameToCollectors[domainName] = new Dictionary<Type,Function>();
                }
                LinearKind kind = FindLinearKind(node);
                if (kind != LinearKind.LINEAR)
                {
                    if (node is GlobalVariable || node is LocalVariable || (node is Formal && !(node as Formal).InComing))
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
                SimpleAssignLhs salhs = lhs as SimpleAssignLhs;
                if (salhs == null)
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

        private void AddDisjointnessExpr(List<Cmd> newCmds, Absy absy, Dictionary<string, Variable> domainNameToInputVar)
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
                newCmds.Add(new AssumeCmd(Token.NoToken, DisjointnessExpr(domainName, domainNameToInputVar[domainName], domainNameToScope[domainName])));
            }
        }

        public void Transform()
        {
            foreach (var impl in program.Implementations)
            {
                Dictionary<string, Variable> domainNameToInputVar = new Dictionary<string, Variable>();
                foreach (string domainName in linearDomains.Keys)
                {
                    var domain = linearDomains[domainName];
                    Formal f = new Formal(
                      Token.NoToken,
                      new TypedIdent(Token.NoToken, 
                        "linear_" + domainName + "_in",
                        new MapType(Token.NoToken, new List<TypeVariable>(), 
                          new List<Type> { domain.elementType }, Type.Bool)), true);
                    impl.InParams.Add(f);
                    domainNameToInputVar[domainName] = f;
                }

                foreach (Block b in impl.Blocks)
                {
                    List<Cmd> newCmds = new List<Cmd>();
                    for (int i = 0; i < b.Cmds.Count; i++)
                    {
                        Cmd cmd = b.Cmds[i];
                        newCmds.Add(cmd);
                        if (cmd is CallCmd)
                        {
                            CallCmd callCmd = cmd as CallCmd;
                            if (callCmd.IsAsync)
                            {
                                foreach (var domainName in linearDomains.Keys)
                                {
                                    var domain = linearDomains[domainName];
                                    var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new List<Expr> { Expr.False });
                                    expr.Resolve(new ResolutionContext(null));
                                    expr.Typecheck(new TypecheckingContext(null));
                                    callCmd.Ins.Add(expr);
                                }
                            }
                            else
                            {
                                Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
                                foreach (var domainName in linearDomains.Keys)
                                {
                                    domainNameToExpr[domainName] = Expr.Ident(domainNameToInputVar[domainName]);
                                }
                                foreach (Variable v in AvailableLinearVars(callCmd))
                                {
                                    var domainName = FindDomainName(v);
                                    var domain = linearDomains[domainName];
                                    if (!domain.collectors.ContainsKey(v.TypedIdent.Type)) continue;
                                    Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]), new List<Expr> { Expr.Ident(v) });
                                    var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new List<Expr> { ie, domainNameToExpr[domainName] });
                                    expr.Resolve(new ResolutionContext(null));
                                    expr.Typecheck(new TypecheckingContext(null));
                                    domainNameToExpr[domainName] = expr;
                                }
                                foreach (var domainName in linearDomains.Keys)
                                {
                                    callCmd.Ins.Add(domainNameToExpr[domainName]);
                                }
                            }
                        }
                        else if (cmd is ParCallCmd)
                        {
                            ParCallCmd parCallCmd = (ParCallCmd)cmd;
                            foreach (CallCmd callCmd in parCallCmd.CallCmds)
                            {
                                foreach (var domainName in linearDomains.Keys)
                                {
                                    var domain = linearDomains[domainName];
                                    var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new List<Expr> { Expr.False });
                                    expr.Resolve(new ResolutionContext(null));
                                    expr.Typecheck(new TypecheckingContext(null));
                                    callCmd.Ins.Add(expr);
                                }
                            }
                        }
                        else if (cmd is YieldCmd)
                        {
                            AddDisjointnessExpr(newCmds, cmd, domainNameToInputVar);
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
                            AddDisjointnessExpr(newCmds, header, domainNameToInputVar);
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
                foreach (var domainName in linearDomains.Keys)
                {
                    proc.Requires.Add(new Requires(true, DisjointnessExpr(domainName, domainNameToInputScope[domainName])));
                    var domain = linearDomains[domainName];
                    Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "linear_" + domainName + "_in", new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { domain.elementType }, Type.Bool)), true);
                    proc.InParams.Add(f);
                    proc.Ensures.Add(new Ensures(true, DisjointnessExpr(domainName, f, domainNameToOutputScope[domainName])));
                }
            }
            
            foreach (LinearDomain domain in linearDomains.Values)
            {
                program.AddTopLevelDeclaration(domain.mapConstBool);
                program.AddTopLevelDeclaration(domain.mapConstInt);
                program.AddTopLevelDeclaration(domain.mapEqInt);
                program.AddTopLevelDeclaration(domain.mapImpBool);
                program.AddTopLevelDeclaration(domain.mapOrBool);
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

        private Expr SubsetExpr(LinearDomain domain, Expr ie, Variable partition, int partitionCount)
        {
            Expr e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstInt), new List<Expr> { new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(partitionCount)) });
            e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapEqInt), new List<Expr> { Expr.Ident(partition), e });
            e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapImpBool), new List<Expr> { ie, e });
            e = Expr.Eq(e, new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new List<Expr> { Expr.True }));
            return e;
        }

        private Expr SubsetExprs(LinearDomain domain, HashSet<Variable> scope, Variable partition, int count, Expr expr)
        {
            foreach (Variable v in scope)
            {
                if (!domain.collectors.ContainsKey(v.TypedIdent.Type)) continue;
                Expr ie = new NAryExpr(Token.NoToken, new FunctionCall(domain.collectors[v.TypedIdent.Type]), new List<Expr> { Expr.Ident(v) });
                expr = Expr.And(SubsetExpr(domain, ie, partition, count), expr);
                count++;
            }
            expr = new ExistsExpr(Token.NoToken, new List<Variable> { partition }, expr);
            expr.Resolve(new ResolutionContext(null));
            expr.Typecheck(new TypecheckingContext(null));
            return expr;
        }

        public Expr DisjointnessExpr(string domainName, Variable inputVar, HashSet<Variable> scope)
        {
            LinearDomain domain = linearDomains[domainName];
            BoundVariable partition = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("partition_{0}", domainName), new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { domain.elementType }, Microsoft.Boogie.Type.Int)));
            return SubsetExprs(domain, scope, partition, 1, SubsetExpr(domain, Expr.Ident(inputVar), partition, 0));
        }

        public Expr DisjointnessExpr(string domainName, HashSet<Variable> scope)
        {
            LinearDomain domain = linearDomains[domainName];
            BoundVariable partition = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("partition_{0}", domainName), new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { domain.elementType }, Microsoft.Boogie.Type.Int)));
            return SubsetExprs(domain, scope, partition, 0, Expr.True);
        }
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
        public Function mapEqInt;
        public Function mapConstInt;
        public Function mapOrBool;
        public Function mapImpBool;
        public Function mapConstBool;
        public List<Axiom> axioms;
        public Type elementType;
        public Dictionary<Type, Function> collectors;

        public LinearDomain(Program program, string domainName, Dictionary<Type, Function> collectors)
        {
            this.axioms = new List<Axiom>();
            this.collectors = collectors;
            MapType setType = (MapType)collectors.First().Value.OutParams[0].TypedIdent.Type;
            this.elementType = setType.Arguments[0];
            MapType mapTypeBool = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.elementType }, Type.Bool);
            MapType mapTypeInt = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { this.elementType }, Type.Int);
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
                BoundVariable a = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool));
                IdentifierExpr aie = Expr.Ident(a);
                BoundVariable b = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool));
                IdentifierExpr bie = Expr.Ident(b);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = Expr.Ident(x);
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapOrBool), new List<Expr> { aie, bie } );
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { mapApplTerm, xie } );
                var rhsTerm = Expr.Or(new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { aie, xie } ),
                                      new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { bie, xie} ));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a, b }, null, 
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }), 
                                               new ForallExpr(Token.NoToken, new List<Variable> { x }, Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }

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
                BoundVariable a = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool));
                IdentifierExpr aie = Expr.Ident(a);
                BoundVariable b = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool));
                IdentifierExpr bie = Expr.Ident(b);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = Expr.Ident(x);
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapImpBool), new List<Expr> { aie, bie });
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { mapApplTerm, xie });
                var rhsTerm = Expr.Imp(new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { aie, xie }),
                                       new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { bie, xie }));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a, b }, null,
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }), 
                                               new ForallExpr(Token.NoToken, new List<Variable> { x }, Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }

            this.mapConstBool = new Function(Token.NoToken, "linear_" + domainName + "_MapConstBool",
                                              new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Bool), true) },
                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapConstBool.AddAttribute("builtin", "MapConst");
            }
            else
            {
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = Expr.Ident(x);
                var trueTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), 
                                           new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(mapConstBool), new List<Expr> { Expr.True }), xie });
                var trueAxiomExpr = new ForallExpr(Token.NoToken, new List<Variable> { x }, trueTerm);
                trueAxiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, trueAxiomExpr));
                var falseTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                                           new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(mapConstBool), new List<Expr> { Expr.False }), xie }); 
                var falseAxiomExpr = new ForallExpr(Token.NoToken, new List<Variable> { x }, Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, falseTerm));
                falseAxiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, falseAxiomExpr));
            }

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
                BoundVariable a = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeInt));
                IdentifierExpr aie = Expr.Ident(a);
                BoundVariable b = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt));
                IdentifierExpr bie = Expr.Ident(b);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = Expr.Ident(x);
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapEqInt), new List<Expr> { aie, bie });
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { mapApplTerm, xie });
                var rhsTerm = Expr.Eq(new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { aie, xie }),
                                      new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { bie, xie }));
                var axiomExpr = new ForallExpr(Token.NoToken, new List<TypeVariable>(), new List<Variable> { a, b }, null, 
                                               new Trigger(Token.NoToken, true, new List<Expr> { mapApplTerm }), 
                                               new ForallExpr(Token.NoToken, new List<Variable> { x }, Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }

            this.mapConstInt = new Function(Token.NoToken, "linear_" + domainName + "_MapConstInt",
                                          new List<Variable> { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Int), true) },
                                          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeInt), false));
            if (CommandLineOptions.Clo.UseArrayTheory)
            {
                this.mapConstInt.AddAttribute("builtin", "MapConst");
            }
            else
            {
                BoundVariable a = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "a", Type.Int));
                IdentifierExpr aie = Expr.Ident(a);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = Expr.Ident(x);
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(mapConstInt), new List<Expr> { aie }), xie });
                var axiomExpr = new ForallExpr(Token.NoToken, new List<Variable> { a, x }, Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, aie));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }

            foreach (var axiom in axioms)
            {
                axiom.Expr.Resolve(new ResolutionContext(null));
                axiom.Expr.Typecheck(new TypecheckingContext(null));
            }
        }
    }
}
