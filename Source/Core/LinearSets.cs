using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Boogie
{
    public class LinearTypechecker : StandardVisitor
    {
        public int errorCount;
        CheckingContext checkingContext;
        Dictionary<string, Type> domainNameToType;
        public LinearTypechecker()
        {
            this.errorCount = 0;
            this.checkingContext = new CheckingContext(null);
            this.domainNameToType = new Dictionary<string, Type>();
            this.parallelCallInvars = new HashSet<Variable>();
        }
        private void Error(Absy node, string message)
        {
            checkingContext.Error(node, message);
            errorCount++;
        }
        private Dictionary<Variable, string> scope;
        public override Implementation VisitImplementation(Implementation node)
        {
            scope = new Dictionary<Variable, string>();
            for (int i = 0; i < node.OutParams.Length; i++)
            {
                string domainName = QKeyValue.FindStringAttribute(node.Proc.OutParams[i].Attributes, "linear");
                if (domainName != null)
                {
                    scope[node.OutParams[i]] = domainName;
                }
            }
            return base.VisitImplementation(node);
        }
        private string FindDomainName(Variable v)
        {
            if (scope.ContainsKey(v))
                return scope[v]; 
            return QKeyValue.FindStringAttribute(v.Attributes, "linear");
        }
        public override Variable VisitVariable(Variable node)
        {
            string domainName = QKeyValue.FindStringAttribute(node.Attributes, "linear");
            if (domainName != null)
            {
                Type type = node.TypedIdent.Type;
                MapType mapType = type as MapType;
                if (mapType != null)
                {
                    if (mapType.Arguments.Length == 1 && mapType.Result.Equals(Type.Bool))
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
                    Error(node, "A linear set can occur only once in the rhs");
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
            for (int i = 0; i < node.Proc.InParams.Length; i++)
            {
                Variable formal = node.Proc.InParams[i];
                string domainName = QKeyValue.FindStringAttribute(formal.Attributes, "linear");
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
            for (int i = 0; i < node.Proc.OutParams.Length; i++)
            {
                IdentifierExpr actual = node.Outs[i];
                string actualDomainName = FindDomainName(actual.Decl);
                if (actualDomainName == null) continue;
                Variable formal = node.Proc.OutParams[i];
                string domainName = QKeyValue.FindStringAttribute(formal.Attributes, "linear");
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
    }

    public class LinearSetTransform
    {
        private Program program;
        private Dictionary<Variable, string> varToDomainName;
        private Dictionary<string, LinearDomain> linearDomains;

        public LinearSetTransform(Program program)
        {
            this.program = program;
            this.varToDomainName = new Dictionary<Variable, string>();
            this.linearDomains = new Dictionary<string, LinearDomain>();
        }

        private void AddVariableToScope(Variable v, Dictionary<string, HashSet<Variable>> domainNameToScope)
        {
            var domainName = QKeyValue.FindStringAttribute(v.Attributes, "linear");
            if (domainName == null) return;            
            AddVariableToScopeHelper(v, domainName, domainNameToScope);
        }

        private void AddVariableToScope(Implementation impl, int outParamIndex, Dictionary<string, HashSet<Variable>> domainNameToScope)
        {
            var domainName = QKeyValue.FindStringAttribute(impl.Proc.OutParams[outParamIndex].Attributes, "linear");
            if (domainName == null) return;
            AddVariableToScopeHelper(impl.OutParams[outParamIndex], domainName, domainNameToScope);
        }

        private void AddVariableToScopeHelper(Variable v, string domainName, Dictionary<string, HashSet<Variable>> domainNameToScope)
        {
            if (!varToDomainName.ContainsKey(v))
            {
                varToDomainName[v] = domainName;
            }
            if (!linearDomains.ContainsKey(domainName))
            {
                var domain = new LinearDomain(program, v, domainName);
                linearDomains[domainName] = domain;
                varToDomainName[domain.allocator] = domainName;
            } 
            if (!domainNameToScope.ContainsKey(domainName))
            {
                HashSet<Variable> scope = new HashSet<Variable>();
                scope.Add(linearDomains[domainName].allocator);
                domainNameToScope[domainName] = scope;
            }
            domainNameToScope[domainName].Add(v);
        }

        public void Transform()
        {
            foreach (var decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null) continue;

                Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
                foreach (Variable v in program.GlobalVariables())
                {
                    AddVariableToScope(v, domainNameToScope);
                }
                for (int i = 0; i < impl.OutParams.Length; i++)
                {
                    AddVariableToScope(impl, i, domainNameToScope);
                }
                foreach (Variable v in impl.LocVars)
                {
                    AddVariableToScope(v, domainNameToScope);
                }

                Dictionary<Variable, LocalVariable> copies = new Dictionary<Variable, LocalVariable>();
                foreach (Block b in impl.Blocks)
                {
                    CmdSeq newCmds = new CmdSeq();
                    for (int i = 0; i < b.Cmds.Length; i++)
                    {
                        Cmd cmd = b.Cmds[i];
                        if (cmd is AssignCmd)
                        {
                            TransformAssignCmd(newCmds, (AssignCmd)cmd, copies, domainNameToScope);
                        }
                        else if (cmd is HavocCmd)
                        {
                            HavocCmd havocCmd = (HavocCmd)cmd;
                            foreach (IdentifierExpr ie in havocCmd.Vars)
                            {
                                Variable v = ie.Decl;
                                if (!varToDomainName.ContainsKey(v)) continue;
                                Drain(newCmds, ie.Decl, varToDomainName[v]);
                            }
                            TransformHavocCmd(newCmds, havocCmd, copies, domainNameToScope);
                        }
                        else if (cmd is CallCmd)
                        {
                            TransformCallCmd(newCmds, (CallCmd)cmd, copies, domainNameToScope);
                        }
                        else
                        {
                            newCmds.Add(cmd);
                        }
                    }
                    if (b.TransferCmd is ReturnCmd)
                    {
                        foreach (Variable v in impl.LocVars)
                        {
                            if (varToDomainName.ContainsKey(v)) 
                                Drain(newCmds, v, varToDomainName[v]);
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
                            foreach (string domainName in domainNameToScope.Keys)
                            {
                                newCmds.Add(new AssumeCmd(Token.NoToken, DisjointnessExpr(domainName, domainNameToScope[domainName])));
                            }
                            newCmds.AddRange(header.Cmds);
                            header.Cmds = newCmds;
                        }
                    }
                }

                {
                    // Initialization
                    CmdSeq newCmds = new CmdSeq();
                    IdentifierExprSeq havocVars = new IdentifierExprSeq();
                    foreach (Variable v in impl.OutParams)
                    {
                        if (!varToDomainName.ContainsKey(v)) continue;
                        havocVars.Add(new IdentifierExpr(Token.NoToken, v));   
                    }
                    foreach (Variable v in impl.LocVars)
                    {
                        if (!varToDomainName.ContainsKey(v)) continue;
                        havocVars.Add(new IdentifierExpr(Token.NoToken, v));
                    }
                    if (havocVars.Length > 0)
                    {
                        TransformHavocCmd(newCmds, new HavocCmd(Token.NoToken, havocVars), copies, domainNameToScope);
                    }
                    newCmds.AddRange(impl.Blocks[0].Cmds);
                    impl.Blocks[0].Cmds = newCmds;
                }

                foreach (var v in copies.Values)
                {
                    impl.LocVars.Add(v);
                }
            }

            foreach (var decl in program.TopLevelDeclarations)
            {
                Implementation impl = decl as Implementation;
                if (impl == null) continue;
                Procedure proc = impl.Proc;

                Dictionary<string, HashSet<Variable>> domainNameToScope = new Dictionary<string, HashSet<Variable>>();
                foreach (Variable v in program.GlobalVariables())
                {
                    AddVariableToScope(v, domainNameToScope);
                }
                foreach (string domainName in domainNameToScope.Keys)
                {
                    proc.Requires.Add(new Requires(true, DisjointnessExpr(domainName, domainNameToScope[domainName])));
                }
                Dictionary<string, HashSet<Variable>> domainNameToInParams = new Dictionary<string, HashSet<Variable>>();
                foreach (Variable v in proc.InParams)
                {
                    var domainName = QKeyValue.FindStringAttribute(v.Attributes, "linear");
                    if (domainName == null) continue;
                    if (!linearDomains.ContainsKey(domainName))
                    {
                        linearDomains[domainName] = new LinearDomain(program, v, domainName);
                    } 
                    if (!domainNameToInParams.ContainsKey(domainName))
                    {
                        domainNameToInParams[domainName] = new HashSet<Variable>();
                    }
                    domainNameToInParams[domainName].Add(v);
                    var domain = linearDomains[domainName];
                    IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                    Expr e = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapImpBool), new ExprSeq(v.TypedIdent.Type is MapType ? ie : Singleton(ie, domainName), new IdentifierExpr(Token.NoToken, domain.allocator)));
                    e = Expr.Binary(BinaryOperator.Opcode.Eq, e, new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new ExprSeq(Expr.True)));
                    proc.Requires.Add(new Requires(true, e));
                }
                foreach (var domainName in domainNameToInParams.Keys)
                {
                    proc.Requires.Add(new Requires(true, DisjointnessExpr(domainName, domainNameToInParams[domainName])));
                }
            }
            foreach (var decl in program.TopLevelDeclarations)
            {
                Procedure proc = decl as Procedure;
                if (proc == null) continue;
                HashSet<string> domainNamesForOutParams = new HashSet<string>();
                foreach (Variable v in proc.OutParams)
                {
                    var domainName = QKeyValue.FindStringAttribute(v.Attributes, "linear");
                    if (domainName == null) continue;
                    if (!linearDomains.ContainsKey(domainName))
                    {
                        linearDomains[domainName] = new LinearDomain(program, v, domainName);
                    }
                    if (domainNamesForOutParams.Contains(domainName)) continue;
                    domainNamesForOutParams.Add(domainName);
                    proc.Modifies.Add(new IdentifierExpr(Token.NoToken, linearDomains[domainName].allocator));
                }
            }
            foreach (LinearDomain domain in linearDomains.Values)
            {
                program.TopLevelDeclarations.Add(domain.allocator);
            }
        }

        private Expr Singleton(Expr e, string domainName)
        {
            var domain = linearDomains[domainName];
            return Expr.Store(new NAryExpr(Token.NoToken, new FunctionCall(domain.mapConstBool), new ExprSeq(Expr.False)), e, Expr.True);
        }

        void Drain(CmdSeq newCmds, Variable v, string domainName)
        {
            var domain = linearDomains[domainName];
            IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
            List<AssignLhs> lhss = MkAssignLhss(domain.allocator);
            List<Expr> rhss = 
                v.TypedIdent.Type is MapType
                ? MkExprs(new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new ExprSeq(new IdentifierExpr(Token.NoToken, domain.allocator), ie)))
                : MkExprs(Expr.Store(new IdentifierExpr(Token.NoToken, domain.allocator), ie, Expr.True));
            newCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
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

        void TransformHavocCmd(CmdSeq newCmds, HavocCmd havocCmd, Dictionary<Variable, LocalVariable> copies, Dictionary<string, HashSet<Variable>> domainNameToScope)
        {
            Dictionary<string, HashSet<Variable>> domainNameToHavocVars = new Dictionary<string, HashSet<Variable>>();
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>(); 
            foreach (IdentifierExpr ie in havocCmd.Vars)
            {
                Variable v = ie.Decl;
                if (!varToDomainName.ContainsKey(v)) continue;
                var domainName = varToDomainName[v];
                if (!domainNameToHavocVars.ContainsKey(domainName))
                {
                    domainNameToHavocVars[domainName] = new HashSet<Variable>();
                }
                domainNameToHavocVars[domainName].Add(v);
                var allocator = linearDomains[domainName].allocator;
                if (!copies.ContainsKey(allocator))
                {
                    copies[allocator] = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("copy_{0}", allocator.Name), allocator.TypedIdent.Type));
                }
                lhss.Add(new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, copies[allocator])));
                rhss.Add(new IdentifierExpr(Token.NoToken, allocator));
            }
            if (lhss.Count > 0)
            {
                newCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
            foreach (string domainName in domainNameToHavocVars.Keys)
            {
                var allocator = linearDomains[domainName].allocator;
                havocCmd.Vars.Add(new IdentifierExpr(Token.NoToken, allocator));
            }
            newCmds.Add(havocCmd);
            foreach (string domainName in domainNameToHavocVars.Keys)
            {
                var domain = linearDomains[domainName];
                var allocator = domain.allocator;
                Expr oldExpr = new IdentifierExpr(Token.NoToken, copies[allocator]);
                Expr expr = new IdentifierExpr(Token.NoToken, allocator);
                foreach (var v in domainNameToHavocVars[domainName])
                {
                    IdentifierExpr ie = new IdentifierExpr(Token.NoToken, v);
                    expr = new NAryExpr(Token.NoToken, new FunctionCall(domain.mapOrBool), new ExprSeq(v.TypedIdent.Type is MapType ? ie : Singleton(ie, domainName), expr));
                }
                newCmds.Add(new AssumeCmd(Token.NoToken, Expr.Binary(BinaryOperator.Opcode.Eq, oldExpr, expr)));
                newCmds.Add(new AssumeCmd(Token.NoToken, DisjointnessExpr(domainName, domainNameToScope[domainName])));
            }
        }

        void TransformCallCmd(CmdSeq newCmds, CallCmd callCmd, Dictionary<Variable, LocalVariable> copies, Dictionary<string, HashSet<Variable>> domainNameToScope)
        {
            HashSet<Variable> rhsVars = new HashSet<Variable>();
            for (int i = 0; i < callCmd.Proc.InParams.Length; i++)
            {
                Variable target = callCmd.Proc.InParams[i];
                if (!varToDomainName.ContainsKey(target)) continue;
                IdentifierExpr ie = callCmd.Ins[i] as IdentifierExpr;
                Variable source = ie.Decl;
                rhsVars.Add(source);
            }
            HashSet<Variable> lhsVars = new HashSet<Variable>();
            HashSet<string> domainNames = new HashSet<string>();
            foreach (IdentifierExpr ie in callCmd.Outs)
            {
                Variable v = ie.Decl;
                if (!varToDomainName.ContainsKey(v)) continue;
                lhsVars.Add(v);
                domainNames.Add(varToDomainName[v]);
            }
            foreach (Variable v in lhsVars.Union(rhsVars))
            {
                Drain(newCmds, v, varToDomainName[v]);
            }
            newCmds.Add(callCmd);
            foreach (string domainName in domainNames)
            {
                newCmds.Add(new AssumeCmd(Token.NoToken, DisjointnessExpr(domainName, domainNameToScope[domainName])));
            } 
            IdentifierExprSeq havocExprs = new IdentifierExprSeq();
            foreach (Variable v in rhsVars.Except(lhsVars))
            {
                havocExprs.Add(new IdentifierExpr(Token.NoToken, v));
            }
            if (havocExprs.Length > 0)
            {
                TransformHavocCmd(newCmds, new HavocCmd(Token.NoToken, havocExprs), copies, domainNameToScope);
            }
        }

        void TransformAssignCmd(CmdSeq newCmds, AssignCmd assignCmd, Dictionary<Variable, LocalVariable> copies, Dictionary<string, HashSet<Variable>> domainNameToScope)
        {
            HashSet<Variable> rhsVars = new HashSet<Variable>();
            HashSet<Variable> lhsVars = new HashSet<Variable>();
            for (int i = 0; i < assignCmd.Lhss.Count; i++)
            {
                Variable target = assignCmd.Lhss[i].DeepAssignedVariable;
                if (!varToDomainName.ContainsKey(target)) continue;
                IdentifierExpr ie = assignCmd.Rhss[i] as IdentifierExpr;
                Variable source = ie.Decl;
                rhsVars.Add(source);
                lhsVars.Add(target);
            }
            foreach (Variable v in lhsVars.Except(rhsVars))
            {
                Drain(newCmds, v, varToDomainName[v]);
            }
            newCmds.Add(assignCmd);
            IdentifierExprSeq havocExprs = new IdentifierExprSeq();
            foreach (Variable v in rhsVars.Except(lhsVars))
            {
                havocExprs.Add(new IdentifierExpr(Token.NoToken, v));
            }
            if (havocExprs.Length > 0)
            {
                TransformHavocCmd(newCmds, new HavocCmd(Token.NoToken, havocExprs), copies, domainNameToScope);
            }
        }

        Expr DisjointnessExpr(string domainName, HashSet<Variable> scope)
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

    class LinearDomain
    {
        public GlobalVariable allocator;
        public Microsoft.Boogie.Type elementType;
        public Function mapEqInt;
        public Function mapConstInt;
        public Function mapOrBool;
        public Function mapImpBool;
        public Function mapConstBool;
        public List<Axiom> axioms;

        public LinearDomain(Program program, Variable var, string domainName)
        {
            this.elementType = var.TypedIdent.Type;
            if (var.TypedIdent.Type is MapType)
            {
                MapType mapType = (MapType)var.TypedIdent.Type;
                this.elementType = mapType.Arguments[0];
            }
            this.allocator = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, string.Format("allocator_{0}", domainName), new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(this.elementType), Type.Bool)));
            this.axioms = new List<Axiom>();

            MapType mapTypeBool = new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(this.elementType), Type.Bool);
            MapType mapTypeInt = new MapType(Token.NoToken, new TypeVariableSeq(), new TypeSeq(this.elementType), Type.Int);
            this.mapOrBool = new Function(Token.NoToken, "linear@MapOr",
                                          new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool), true),
                                                          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool), true)),
                                          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            this.mapOrBool.AddAttribute("builtin", "MapOr");

            this.mapImpBool = new Function(Token.NoToken, "linear@MapImp",
                                              new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeBool), true),
                                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeBool), true)),
                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            this.mapImpBool.AddAttribute("builtin", "MapImp");

            this.mapConstBool = new Function(Token.NoToken, "linear@MapConstBool",
                                              new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Bool), true)),
                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            this.mapConstBool.AddAttribute("builtin", "MapConst");

            this.mapEqInt = new Function(Token.NoToken, "linear@MapEq",
                                              new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "a", mapTypeInt), true),
                                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", mapTypeInt), true)),
                                              new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeBool), false));
            this.mapEqInt.AddAttribute("builtin", "MapEq");

            this.mapConstInt = new Function(Token.NoToken, "linear@MapConstInt",
                                          new VariableSeq(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "b", Type.Int), true)),
                                          new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "c", mapTypeInt), false));
            this.mapConstInt.AddAttribute("builtin", "MapConst");
        }
    }
}
