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
        private QKeyValue Remove(QKeyValue iter)
        {
            if (iter == null) return null;
            iter.Next = Remove(iter.Next);
            return (QKeyValue.FindStringAttribute(iter, "linear") == null) ? iter : iter.Next;
        }

        public override Variable VisitVariable(Variable node)
        {
            node.Attributes = Remove(node.Attributes);
            return base.VisitVariable(node);
        }
    }

    public class LinearTypechecker : StandardVisitor
    {
        public Program program;
        public int errorCount;
        public CheckingContext checkingContext;
        public Dictionary<string, Type> domainNameToType;
        public Dictionary<Absy, HashSet<Variable>> availableLocalLinearVars;
        public Dictionary<Variable, string> inoutParamToDomainName;
        public Dictionary<Variable, string> varToDomainName;
        public Dictionary<string, LinearDomain> linearDomains;

        public LinearTypechecker(Program program)
        {
            this.program = program;
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.domainNameToType = new Dictionary<string, Type>();
            this.parallelCallInvars = new HashSet<Variable>();
            this.availableLocalLinearVars = new Dictionary<Absy, HashSet<Variable>>();
            this.inoutParamToDomainName = new Dictionary<Variable, string>();
            this.varToDomainName = new Dictionary<Variable, string>();
            this.linearDomains = new Dictionary<string, LinearDomain>();
        }
        public void Typecheck()
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
        public override Implementation VisitImplementation(Implementation node)
        {
            HashSet<Variable> start = new HashSet<Variable>();
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
            availableLocalLinearVars[node.Blocks[0]] = start;
            dfsStack.Push(node.Blocks[0]);
            dfsStackAsSet.Add(node.Blocks[0]);
            while (dfsStack.Count > 0)
            {
                Block b = dfsStack.Pop();
                dfsStackAsSet.Remove(b);
                HashSet<Variable> end = PropagateAvailableLinearVarsAcrossBlock(b);
                if (b.TransferCmd is ReturnCmd)
                {
                    foreach (Variable v in node.OutParams)
                    {
                        if (FindDomainName(v) == null || end.Contains(v)) continue;
                        Error(b, "output variable must be available at a return");
                    }
                }
                if (b.TransferCmd is ReturnCmd) continue;
                GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    if (!availableLocalLinearVars.ContainsKey(target))
                    {
                        availableLocalLinearVars[target] = new HashSet<Variable>(end);
                        dfsStack.Push(target);
                        dfsStackAsSet.Add(target);
                    }
                    else
                    {
                        var savedAvailableVars = new HashSet<Variable>(availableLocalLinearVars[target]);
                        availableLocalLinearVars[target].IntersectWith(end);
                        if (savedAvailableVars.IsProperSupersetOf(availableLocalLinearVars[target]) && !dfsStackAsSet.Contains(target))
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
            HashSet<Variable> start = new HashSet<Variable>(availableLocalLinearVars[b]);
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
                    CallCmd callCmd = (CallCmd)cmd;
                    while (callCmd != null)
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
                        callCmd = callCmd.InParallelWith;
                    }
                    callCmd = (CallCmd)cmd;
                    availableLocalLinearVars[callCmd] = new HashSet<Variable>(start);
                    while (callCmd != null)
                    {
                        foreach (IdentifierExpr ie in callCmd.Outs)
                        {
                            if (FindDomainName(ie.Decl) == null) continue;
                            start.Add(ie.Decl);
                        }
                        callCmd = callCmd.InParallelWith;
                    }
                }
                else if (cmd is HavocCmd)
                {
                    HavocCmd havocCmd = (HavocCmd) cmd;
                    foreach (IdentifierExpr ie in havocCmd.Vars)
                    {
                        if (FindDomainName(ie.Decl) == null) continue;
                        start.Remove(ie.Decl);
                    }
                }
                else if (cmd is YieldCmd)
                {
                    availableLocalLinearVars[cmd] = new HashSet<Variable>(start);
                }
            }
            return start;
        }
        public string FindDomainName(Variable v)
        {
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
                    Error(node, "a linear domain must be consistently attached to variables of a particular type");
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
                string domainName = FindDomainName(lhs.DeepAssignedVariable);
                if (domainName == null) continue;
                SimpleAssignLhs salhs = lhs as SimpleAssignLhs;
                if (salhs == null)
                {
                    Error(node, "Only simple assignment allowed on linear sets");
                    continue;
                }
                if (salhs.DeepAssignedVariable is GlobalVariable)
                {
                    Error(node, "Linear global variable cannot be written to");
                    continue;
                }
                IdentifierExpr rhs = node.Rhss[i] as IdentifierExpr;
                if (rhs == null)
                {
                    Error(node, "Only variable can be assigned to a linear variable");
                    continue; 
                }
                string rhsDomainName = FindDomainName(rhs.Decl);
                if (rhsDomainName == null)
                {
                    Error(node, "Only linear variable can be assigned to another linear variable");
                    continue;
                }
                if (domainName != rhsDomainName)
                {
                    Error(node, "Variable of one domain being assigned to a variable of another domain");
                    continue;
                }
                if (rhsVars.Contains(rhs.Decl))
                {
                    Error(node, "A linear variable can occur only once in the rhs");
                    continue;
                }
                if (rhs.Decl is GlobalVariable)
                {
                    Error(node, "Linear global variable cannot be read from");
                    continue;
                }
                rhsVars.Add(rhs.Decl);
            }
            return base.VisitAssignCmd(node);
        }
        HashSet<Variable> parallelCallInvars;
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
                    Error(node, "Only variable can be assigned to a linear variable");
                    continue;
                }
                string actualDomainName = FindDomainName(actual.Decl);
                if (actualDomainName == null)
                {
                    Error(node, "Only a linear argument can be passed to a linear parameter");
                    continue;
                }
                if (domainName != actualDomainName)
                {
                    Error(node, "The domains of formal and actual parameters must be the same");
                    continue;
                }
                if (parallelCallInvars.Contains(actual.Decl))
                {
                    Error(node, "A linear set can occur only once as an in parameter");
                    continue;
                }
                if (actual.Decl is GlobalVariable)
                {
                    Error(node, "Only local linear variable can be an actual input parameter of a procedure call");
                    continue;
                }
                inVars.Add(actual.Decl);
                parallelCallInvars.Add(actual.Decl);
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
            if (node.InParallelWith != null)
            {
                VisitCallCmd(node.InParallelWith);
            }
            foreach (Variable v in inVars)
            {
                parallelCallInvars.Remove(v);
            }
            return base.VisitCallCmd(node);
        }

        private void AddDisjointnessExpr(CmdSeq newCmds, Absy absy, Dictionary<string, Variable> domainNameToInputVar)
        {
            Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
            foreach (var domainName in linearDomains.Keys)
            {
                domainNameToScope[domainName] = new HashSet<Variable>();
                domainNameToScope[domainName].Add(domainNameToInputVar[domainName]);
            }
            foreach (Variable v in program.GlobalVariables())
            {
                var domainName = FindDomainName(v);
                if (domainName == null) continue;
                domainNameToScope[domainName].Add(v);
            }
            foreach (Variable v in availableLocalLinearVars[absy])
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
                    Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, domainName + "_in", new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(domain.elementType), Type.Bool)), true);
                    impl.InParams.Add(f);
                    domainNameToInputVar[domainName] = f;
                }

                foreach (Block b in impl.Blocks)
                {
                    CmdSeq newCmds = new CmdSeq();
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
                                    callCmd.Ins.Add(new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new ExprSeq(Expr.False)));
                                }
                            }
                            else if (callCmd.InParallelWith != null)
                            {
                                while (callCmd != null)
                                {
                                    foreach (var domainName in linearDomains.Keys)
                                    {
                                        var domain = linearDomains[domainName];
                                        callCmd.Ins.Add(new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new ExprSeq(Expr.False)));
                                    }
                                    callCmd = callCmd.InParallelWith;
                                }
                            }
                            else
                            {
                                Dictionary<string, Expr> domainNameToExpr = new Dictionary<string, Expr>();
                                foreach (var domainName in linearDomains.Keys)
                                {
                                    domainNameToExpr[domainName] = new IdentifierExpr(Token.NoToken, domainNameToInputVar[domainName]);
                                }
                                foreach (Variable v in availableLocalLinearVars[callCmd])
                                {
                                    var domainName = FindDomainName(v);
                                    var domain = linearDomains[domainName];
                                    IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                                    domainNameToExpr[domainName] = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new ExprSeq(v.TypedIdent.Type is MapType ? ie : Singleton(ie, domainName), domainNameToExpr[domainName]));
                                }
                                foreach (var domainName in linearDomains.Keys)
                                {
                                    callCmd.Ins.Add(domainNameToExpr[domainName]);
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
                            CmdSeq newCmds = new CmdSeq();
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
                foreach (Variable v in program.GlobalVariables())
                {
                    var domainName = FindDomainName(v);
                    if (domainName == null) continue;
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
                    Formal f = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, domainName + "_in", new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(domain.elementType), Type.Bool)), true);
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
            return Expr.Store(new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new ExprSeq(Expr.False)), e, Expr.True);
        }

        List<AssignLhs> MkAssignLhss(params Variable[] args)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            foreach (Variable arg in args)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, arg)));
            }
            return lhss;
        }

        List<Expr> MkExprs(params Expr[] args)
        {
            return new List<Expr>(args);
        }

        public Expr DisjointnessExpr(string domainName, HashSet<Variable> scope)
        {
            LinearDomain domain = linearDomains[domainName];
            BoundVariable partition = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("partition_{0}", domainName), new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(domain.elementType), Microsoft.Boogie.Type.Int)));
            Expr disjointExpr = Expr.True;
            int count = 0;
            foreach (Variable v in scope)
            {
                IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                Expr e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstInt), new ExprSeq(new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(count++))));
                e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapEqInt), new ExprSeq(new IdentifierExpr(Token.NoToken, partition), e));
                e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapImpBool), new ExprSeq(v.TypedIdent.Type is MapType ? ie : Singleton(ie, domainName), e));
                e = Expr.Binary(BinaryOperator.Opcode.Eq, e, new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new ExprSeq(Expr.True)));
                disjointExpr = Expr.Binary(BinaryOperator.Opcode.And, e, disjointExpr);
            }
            return new ExistsExpr(Token.NoToken, new VariableSeq(partition), disjointExpr);
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

            MapType mapTypeBool = new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(this.elementType), Type.Bool);
            MapType mapTypeInt = new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(this.elementType), Type.Int);
            this.mapOrBool = new Function(Token.NoToken, domainName + "_linear_MapOr",
                                          new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool), true),
                                                          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool), true)),
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
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapOrBool), new ExprSeq(aie, bie));
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(mapApplTerm, xie));
                var rhsTerm = Expr.Binary(BinaryOperator.Opcode.Or,
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(aie, xie)),
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(bie, xie)));
                var axiomExpr = new ForallExpr(Token.NoToken, new TypeVariableSeq(), new VariableSeq(a, b), null, 
                                               new Trigger(Token.NoToken, true, new ExprSeq(mapApplTerm)), 
                                               new ForallExpr(Token.NoToken, new VariableSeq(x), Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }

            this.mapImpBool = new Function(Token.NoToken, domainName + "_linear_MapImp",
                                              new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool), true),
                                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool), true)),
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
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapImpBool), new ExprSeq(aie, bie));
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(mapApplTerm, xie));
                var rhsTerm = Expr.Binary(BinaryOperator.Opcode.Imp,
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(aie, xie)),
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(bie, xie)));
                var axiomExpr = new ForallExpr(Token.NoToken, new TypeVariableSeq(), new VariableSeq(a, b), null,
                                               new Trigger(Token.NoToken, true, new ExprSeq(mapApplTerm)), 
                                               new ForallExpr(Token.NoToken, new VariableSeq(x), Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }

            this.mapConstBool = new Function(Token.NoToken, domainName + "_linear_MapConstBool",
                                              new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Bool), true)),
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
                                           new ExprSeq(new NAryExpr(Token.NoToken, new FunctionCall(mapConstBool), new ExprSeq(Expr.True)), xie));
                var trueAxiomExpr = new ForallExpr(Token.NoToken, new VariableSeq(x), trueTerm);
                trueAxiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, trueAxiomExpr));
                var falseTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                                           new ExprSeq(new NAryExpr(Token.NoToken, new FunctionCall(mapConstBool), new ExprSeq(Expr.False)), xie)); 
                var falseAxiomExpr = new ForallExpr(Token.NoToken, new VariableSeq(x), Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, falseTerm));
                falseAxiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, falseAxiomExpr));
            }

            this.mapEqInt = new Function(Token.NoToken, domainName + "_linear_MapEq",
                                              new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeInt), true),
                                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt), true)),
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
                var mapApplTerm = new NAryExpr(Token.NoToken, new FunctionCall(mapEqInt), new ExprSeq(aie, bie));
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(mapApplTerm, xie));
                var rhsTerm = Expr.Binary(BinaryOperator.Opcode.Eq,
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(aie, xie)),
                                          new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(bie, xie)));
                var axiomExpr = new ForallExpr(Token.NoToken, new TypeVariableSeq(), new VariableSeq(a, b), null, 
                                               new Trigger(Token.NoToken, true, new ExprSeq(mapApplTerm)), 
                                               new ForallExpr(Token.NoToken, new VariableSeq(x), Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, rhsTerm)));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }

            this.mapConstInt = new Function(Token.NoToken, domainName + "_linear_MapConstInt",
                                          new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Int), true)),
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
                var lhsTerm = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1), new ExprSeq(new NAryExpr(Token.NoToken, new FunctionCall(mapConstInt), new ExprSeq(aie)), xie));
                var axiomExpr = new ForallExpr(Token.NoToken, new VariableSeq(a, x), Expr.Binary(BinaryOperator.Opcode.Eq, lhsTerm, aie));
                axiomExpr.Typecheck(new TypecheckingContext(null));
                axioms.Add(new Axiom(Token.NoToken, axiomExpr));
            }
        }
    }
}
