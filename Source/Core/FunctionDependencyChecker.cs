using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
    public class FunctionDependencyChecker : StandardVisitor
    {
        public static bool Check(Program program)
        {
            var checkingContext = new CheckingContext(null);
            var functionDependencyChecker = new FunctionDependencyChecker();
            program.TopLevelDeclarations.OfType<Function>().Iter(function =>
            {
                var expr = QKeyValue.FindExprAttribute(function.Attributes, "inline");
                if (expr != null && expr.Type != Type.Bool)
                {
                    checkingContext.Error(function.tok, "Parameter to :inline attribute on a function must be Boolean");
                }
                if (QKeyValue.FindBoolAttribute(function.Attributes, "inline") &&
                    QKeyValue.FindBoolAttribute(function.Attributes, "define"))
                {
                    checkingContext.Error(function.tok, "A function may not have both :inline and :define attributes");
                }
                if (QKeyValue.FindBoolAttribute(function.Attributes, "inline") &&
                    function.Body == null)
                {
                    checkingContext.Error(function.tok, "Function with :inline attribute must have a body");
                }
                if (QKeyValue.FindBoolAttribute(function.Attributes, "define") &&
                    function.DefinitionBody == null)
                {
                    checkingContext.Error(function.tok, "Function with :define attribute must have a body");
                }
            });
            if (checkingContext.ErrorCount > 0)
            {
                return false;
            }
            program.TopLevelDeclarations.OfType<Function>()
                .Iter(function => functionDependencyChecker.VisitFunction(function));
            var functionDependencyGraph = functionDependencyChecker.functionDependencyGraph;
            var selfLoops = functionDependencyGraph.Edges.SelectMany(edge =>
                edge.Item1 == edge.Item2 ? new[] {edge.Item1} : Enumerable.Empty<Function>()).ToHashSet();
            var sccs = new StronglyConnectedComponents<Function>(
                functionDependencyGraph.Nodes,
                functionDependencyGraph.Predecessors,
                functionDependencyGraph.Successors);
            sccs.Compute();
            sccs.Iter(scc =>
            {
                if (scc.Count > 1 ||
                    scc.Count == 1 && selfLoops.Contains(scc.First()))
                {
                    var errorMsg = "Call cycle detected among functions";
                    var first = true;
                    var token = Token.NoToken;
                    scc.Iter(function =>
                    {
                        if (first)
                        {
                            first = false;
                            errorMsg += ": ";
                            token = function.tok;
                        }
                        else
                        {
                            errorMsg += ", ";
                        }
                        errorMsg += function.Name;
                    });
                    checkingContext.Error(token, errorMsg);
                }
            });
            return checkingContext.ErrorCount == 0;
        }

        private Graph<Function> functionDependencyGraph;
        private Function enclosingFunction;
        
        private FunctionDependencyChecker()
        {
            functionDependencyGraph = new Graph<Function>();
        }

        public override Function VisitFunction(Function node)
        {
            if (QKeyValue.FindBoolAttribute(node.Attributes, "inline"))
            {
                this.enclosingFunction = node;
                base.Visit(node.Body);
                this.enclosingFunction = null;
            }
            else if (QKeyValue.FindBoolAttribute(node.Attributes, "define"))
            {
                this.enclosingFunction = node;
                base.Visit(node.DefinitionBody.Args[1]);
                this.enclosingFunction = null;
            }
            return node;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is FunctionCall functionCall)
            {
                if (QKeyValue.FindBoolAttribute(functionCall.Func.Attributes, "inline") ||
                    QKeyValue.FindBoolAttribute(functionCall.Func.Attributes, "define"))
                {
                    functionDependencyGraph.AddEdge(enclosingFunction, functionCall.Func);
                }
            }
            return base.VisitNAryExpr(node);
        }
    }
}