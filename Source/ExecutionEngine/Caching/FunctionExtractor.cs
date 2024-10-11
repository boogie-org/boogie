using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

sealed class FunctionExtractor : StandardVisitor
{
  readonly Dictionary<Variable, BoundVariable> Substitutions = new Dictionary<Variable, BoundVariable>();

  public override Expr VisitIdentifierExpr(IdentifierExpr node)
  {
    if (node.Decl == null || !(node.Decl is LocalVariable || node.Decl is Formal || node.Decl is GlobalVariable))
    {
      return node;
    }
    else
    {
      if (!Substitutions.TryGetValue(node.Decl, out var boundVar))
      {
        boundVar = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, node.Name, node.Type));
        Substitutions[node.Decl] = boundVar;
      }

      return new IdentifierExpr(node.tok, boundVar);
    }
  }

  public static Expr Extract(Expr expr, Program program, List<Axiom> axioms)
  {
    Contract.Requires(expr != null && program != null && !program.TopLevelDeclarationsAreFrozen && axioms != null);

    if (expr is LiteralExpr)
    {
      return expr;
    }

    var extractor = new FunctionExtractor();

    var body = extractor.VisitExpr(expr);

    var name = program.FreshExtractedFunctionName();
    var originalVars = extractor.Substitutions.Keys.ToList();
    var formalInArgs = originalVars.Select(v => new Formal(Token.NoToken,
      new TypedIdent(Token.NoToken, extractor.Substitutions[v].Name, extractor.Substitutions[v].TypedIdent.Type),
      true)).ToList<Variable>();
    var formalOutArg = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, name + "$result$", expr.Type), false);
    var func = new Function(Token.NoToken, name, formalInArgs, formalOutArg);
    func.AddAttribute("never_pattern");

    var boundVars = originalVars.Select(k => extractor.Substitutions[k]);
    var axiomCall = new NAryExpr(Token.NoToken, new FunctionCall(func),
      boundVars.Select(b => new IdentifierExpr(Token.NoToken, b)).ToList<Expr>());
    axiomCall.Type = expr.Type;
    axiomCall.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
    var eq = LiteralExpr.Eq(axiomCall, body);
    eq.Type = body.Type;
    eq.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
    if (0 < formalInArgs.Count)
    {
      var forallExpr = new ForallExpr(Token.NoToken, boundVars.ToList<Variable>(),
        new Trigger(Token.NoToken, true, new List<Expr> {axiomCall}), eq);
      body = forallExpr;
      forallExpr.Attributes = new QKeyValue(Token.NoToken, "weight",
        new List<object> {new LiteralExpr(Token.NoToken, BaseTypes.BigNum.FromInt(30))}, null);
      body.Type = Type.Bool;
    }
    else
    {
      body = eq;
    }

    var axiom = new Axiom(Token.NoToken, body);
    func.DefinitionAxiom = axiom;
    program.AddTopLevelDeclaration(func);
    program.AddTopLevelDeclaration(axiom);
    axioms.Add(axiom);

    var call = new NAryExpr(Token.NoToken, new FunctionCall(func),
      originalVars.Select(v => new IdentifierExpr(Token.NoToken, v)).ToList<Expr>());
    call.Type = expr.Type;
    call.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
    return call;
  }
}