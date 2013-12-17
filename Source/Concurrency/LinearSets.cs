using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Boogie
{
    public class LinearEraser : StandardVisitor
    {
        private QKeyValue RemoveLinearAttribute(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = RemoveLinearAttribute(iter.Next);
            return (QKeyValue.FindStringAttribute(iter, "linear") == null) ? iter : iter.Next;
        }

        public override Variable VisitVariable(Variable node)
        {
            node.Attributes = RemoveLinearAttribute(node.Attributes);
            return base.VisitVariable(node);
        }
    }

    public class LinearTypeChecker : StandardVisitor
    {
        public Program program;
        public int errorCount;
        public CheckingContext checkingContext;
        public Dictionary<string, Type> domainNameToType;
        public Dictionary<Absy, HashSet<Variable>> availableLinearVars;
        public Dictionary<Variable, string> inoutParamToDomainName;
        public Dictionary<Variable, string> varToDomainName;
        public Dictionary<Variable, string> globalVarToDomainName;
        public Dictionary<string, LinearDomain> linearDomains;

        public LinearTypeChecker(Program program)
        {
            this.program = program;
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.domainNameToType = new Dictionary<string, Type>();
            this.availableLinearVars = new Dictionary<Absy, HashSet<Variable>>();
            this.inoutParamToDomainName = new Dictionary<Variable, string>();
            this.varToDomainName = new Dictionary<Variable, string>();
            this.linearDomains = new Dictionary<string, LinearDomain>();
        }
        public void TypeCheck()
        {
            this.VisitProgram(program);
            foreach (string domainName in domainNameToType.Keys)
            {
                this.linearDomains[domainName] = new LinearDomain(program, domainName, domainNameToType[domainName]);
            }
        }
        private void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
            errorCount++;
        }
        public override Program VisitProgram(Program node)
        {
            globalVarToDomainName = new Dictionary<Variable, string>();
            foreach (GlobalVariable g in program.GlobalVariables())
            {
                string domainName = FindDomainName(g);
                if (domainName != null)
                {
                    globalVarToDomainName[g] = domainName;
                }
            }
            return base.VisitProgram(node);
        }
        public override Implementation VisitImplementation(Implementation node)
        {
            HashSet<Variable> start = new HashSet<Variable>(globalVarToDomainName.Keys);
            for (int i = 0; i < node.InParams.Count; i++)
            {
                string domainName = FindDomainName(node.Proc.InParams[i]);
                if (domainName != null)
                {
                    inoutParamToDomainName[node.InParams[i]] = domainName;
                    start.Add(node.InParams[i]);
                }
            }
            for (int i = 0; i < node.OutParams.Count; i++)
            {
                string domainName = FindDomainName(node.Proc.OutParams[i]);
                if (domainName != null)
                {
                    inoutParamToDomainName[node.OutParams[i]] = domainName;
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
            return impl;
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
                        if (start.Contains(ie.Decl))
                        {
                            start.Remove(ie.Decl);
                        }
                        else
                        {
                            Error(ie, "unavailable source for a linear read");
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
                        if (FindDomainName(callCmd.Proc.InParams[i]) == null) continue;
                        IdentifierExpr ie = callCmd.Ins[i] as IdentifierExpr;
                        if (start.Contains(ie.Decl))
                        {
                            start.Remove(ie.Decl);
                        }
                        else
                        {
                            Error(ie, "unavailable source for a linear read");
                        }
                    }
                    availableLinearVars[callCmd] = new HashSet<Variable>(start);
                    foreach (IdentifierExpr ie in callCmd.Outs)
                    {
                        if (FindDomainName(ie.Decl) == null) continue;
                        start.Add(ie.Decl);
                    }
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
                            if (FindDomainName(callCmd.Proc.InParams[i]) == null) continue;
                            IdentifierExpr ie = callCmd.Ins[i] as IdentifierExpr;
                            if (start.Contains(ie.Decl))
                            {
                                start.Remove(ie.Decl);
                            }
                            else
                            {
                                Error(ie, "unavailable source for a linear read");
                            }
                        }
                    }
                    availableLinearVars[parCallCmd] = new HashSet<Variable>(start);
                    foreach (CallCmd callCmd in parCallCmd.CallCmds)
                    {
                        foreach (IdentifierExpr ie in callCmd.Outs)
                        {
                            if (FindDomainName(ie.Decl) == null) continue;
                            start.Add(ie.Decl);
                        }
                    }
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
            if (inoutParamToDomainName.ContainsKey(v))
                return inoutParamToDomainName[v];
            return QKeyValue.FindStringAttribute(v.Attributes, "linear");
        }
        public override Variable VisitVariable(Variable node)
        {
            string domainName = FindDomainName(node);
            if (domainName != null)
            {
                Type type = node.TypedIdent.Type;
                MapType mapType = type as MapType;
                if (mapType != null)
                {
                    if (mapType.Arguments.Count == 1 && mapType.Result.Equals(Type.Bool))
                    {
                        type = mapType.Arguments[0];
                        if (type is MapType)
                        {
                            Error(node, "the domain of a linear set must be a scalar type");
                            return base.VisitVariable(node);
                        }
                    }
                    else
                    {
                        Error(node, "a linear domain can be attached to either a set or a scalar type");
                        return base.VisitVariable(node);
                    }
                }
                if (domainNameToType.ContainsKey(domainName) && !domainNameToType[domainName].Equals(type))
                {
                    Error(node, string.Format("Linear domain {0} must be consistently attached to variables of one type", domainName));
                }
                else
                {
                    domainNameToType[domainName] = type;
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
        private void AddDisjointnessExpr(List<Cmd> newCmds, Absy absy, Dictionary<string, Variable> domainNameToInputVar)
        {
            Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
            foreach (var domainName in linearDomains.Keys)
            {
                domainNameToScope[domainName] = new HashSet<Variable>();
                domainNameToScope[domainName].Add(domainNameToInputVar[domainName]);
            }
            foreach (Variable v in availableLinearVars[absy])
            {
                var domainName = FindDomainName(v);
                domainNameToScope[domainName].Add(v);
            }
            foreach (string domainName in linearDomains.Keys)
            {
                newCmds.Add(new AssumeCmd(Token.NoToken, DisjointnessExpr(domainName, domainNameToScope[domainName])));
            }
        }

        public void Transform()
        {
            foreach (var decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null) continue;
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
                                    domainNameToExpr[domainName] = new IdentifierExpr(Token.NoToken, domainNameToInputVar[domainName]);
                                }
                                foreach (Variable v in availableLinearVars[callCmd])
                                {
                                    var domainName = FindDomainName(v);
                                    var domain = linearDomains[domainName];
                                    IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                                    var expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), 
                                                            new List<Expr> { v.TypedIdent.Type is MapType ? ie : Singleton(ie, domainName), domainNameToExpr[domainName] });
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

            foreach (var decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc == null) continue;

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
                    domainNameToInputScope[domainName].Add(v);
                }
                foreach (Variable v in proc.OutParams)
                {
                    var domainName = FindDomainName(v);
                    if (domainName == null) continue;
                    domainNameToOutputScope[domainName].Add(v);
                }
                foreach (var domainName in linearDomains.Keys)
                {
                    proc.Requires.Add(new Requires(true, DisjointnessExpr(domainName, domainNameToInputScope[domainName])));
                    var domain = linearDomains[domainName];
                    Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "linear_" + domainName + "_in", new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { domain.elementType }, Type.Bool)), true);
                    proc.InParams.Add(f);
                    domainNameToOutputScope[domainName].Add(f);
                    proc.Ensures.Add(new Ensures(true, DisjointnessExpr(domainName, domainNameToOutputScope[domainName])));
                }
            }
            
            foreach (LinearDomain domain in linearDomains.Values)
            {
                program.TopLevelDeclarations.Add(domain.mapConstBool);
                program.TopLevelDeclarations.Add(domain.mapConstInt);
                program.TopLevelDeclarations.Add(domain.mapEqInt);
                program.TopLevelDeclarations.Add(domain.mapImpBool);
                program.TopLevelDeclarations.Add(domain.mapOrBool);
                foreach (Axiom axiom in domain.axioms)
                {
                    program.TopLevelDeclarations.Add(axiom);
                }
            }

            //int oldPrintUnstructured = CommandLineOptions.Clo.PrintUnstructured;
            //CommandLineOptions.Clo.PrintUnstructured = 1;
            //PrintBplFile("lsd.bpl", program, false, false);
            //CommandLineOptions.Clo.PrintUnstructured = oldPrintUnstructured;
        }

        public Expr Singleton(Expr e, string domainName)
        {
            var domain = linearDomains[domainName];
            return Expr.Store(new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new List<Expr> { Expr.False }), e, Expr.True);
        }

        List<Expr> MkExprs(params Expr[] args)
        {
            return new List<Expr>(args);
        }

        public Expr DisjointnessExpr(string domainName, HashSet<Variable> scope)
        {
            LinearDomain domain = linearDomains[domainName];
            BoundVariable partition = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("partition_{0}", domainName), new MapType(Token.NoToken, new List<TypeVariable>(), new List<Type> { domain.elementType }, Microsoft.Boogie.Type.Int)));
            Expr disjointExpr = Expr.True;
            int count = 0;
            foreach (Variable v in scope)
            {
                IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                Expr e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstInt), new List<Expr>{ new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(count++)) } );
                e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapEqInt), new List<Expr> { new IdentifierExpr(Token.NoToken, partition), e } );
                e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapImpBool), new List<Expr> { v.TypedIdent.Type is MapType ? ie : Singleton(ie, domainName), e } );
                e = Expr.Binary(BinaryOperator.Opcode.Eq, e, new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new List<Expr> { Expr.True }));
                disjointExpr = Expr.Binary(BinaryOperator.Opcode.And, e, disjointExpr);
            }
            var expr = new ExistsExpr(Token.NoToken, new List<Variable> { partition }, disjointExpr);
            expr.Resolve(new ResolutionContext(null));
            expr.Typecheck(new TypecheckingContext(null));
            return expr;
        }
    }

    public class LinearDomain
    {
        public Microsoft.Boogie.Type elementType;
        public Function mapEqInt;
        public Function mapConstInt;
        public Function mapOrBool;
        public Function mapImpBool;
        public Function mapConstBool;
        public List<Axiom> axioms;

        public LinearDomain(Program program, string domainName, Type elementType)
        {
            this.elementType = elementType;
            this.axioms = new List<Axiom>();

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
                IdentifierExpr aie = new IdentifierExpr(Token.NoToken, a);
                BoundVariable b = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool));
                IdentifierExpr bie = new IdentifierExpr(Token.NoToken, b);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = new IdentifierExpr(Token.NoToken, x);
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapOrBool), new List<Expr> { aie, bie } );
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { mapApplTerm, xie } );
                var rhsTerm = Expr.Binary(BinaryOperator.Opcode.Or,
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { aie, xie } ),
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
                IdentifierExpr aie = new IdentifierExpr(Token.NoToken, a);
                BoundVariable b = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool));
                IdentifierExpr bie = new IdentifierExpr(Token.NoToken, b);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = new IdentifierExpr(Token.NoToken, x);
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapImpBool), new List<Expr> { aie, bie });
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { mapApplTerm, xie });
                var rhsTerm = Expr.Binary(BinaryOperator.Opcode.Imp,
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { aie, xie }),
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
                IdentifierExpr xie = new IdentifierExpr(Token.NoToken, x);
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
                IdentifierExpr aie = new IdentifierExpr(Token.NoToken, a);
                BoundVariable b = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt));
                IdentifierExpr bie = new IdentifierExpr(Token.NoToken, b);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = new IdentifierExpr(Token.NoToken, x);
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapEqInt), new List<Expr> { aie, bie });
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { mapApplTerm, xie });
                var rhsTerm = Expr.Binary(BinaryOperator.Opcode.Eq,
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new List<Expr> { aie, xie }),
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
                IdentifierExpr aie = new IdentifierExpr(Token.NoToken, a);
                BoundVariable x = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "x", elementType));
                IdentifierExpr xie = new IdentifierExpr(Token.NoToken, x);
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
