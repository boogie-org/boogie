//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using Core;

namespace Microsoft.Boogie {

  using System;
  using System.Collections.Generic;
  using System.Diagnostics.Contracts;
  using Set = GSet<object>;  // for the purposes here, "object" really means "either Variable or TypeVariable"

  public static class LambdaHelper {
    public static Program Desugar(Program program, out List<Expr/*!*/>/*!*/ axioms, out List<Function/*!*/>/*!*/ functions) {
      Contract.Requires(program != null);
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out functions)));
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out axioms)));
      Contract.Ensures(Contract.Result<Program>() != null);
      LambdaVisitor v = new LambdaVisitor();
      program = v.VisitProgram(program);
      axioms = v.lambdaAxioms;
      functions = v.lambdaFunctions;
      if (CommandLineOptions.Clo.TraceVerify) {
        Console.WriteLine("Desugaring of lambda expressions produced {0} functions and {1} axioms:", functions.Count, axioms.Count);
        TokenTextWriter wr = new TokenTextWriter("<console>", Console.Out, /*pretty=*/ false);
        foreach (Function f in functions) {
          f.Emit(wr, 0);
        }
        foreach (Expr ax in axioms) {
          ax.Emit(wr);
          Console.WriteLine();
        }
      }
      return program;
    }

    /// <summary>
    /// Performs lambda lifting on all anonymous functions in a program.
    /// Lambda lifting transforms a lambda abstraction <c>(lambda x : T :: t)</c> of type <c>T -> U</c>
    /// into a Boogie map of type <c>[T] U</c> as follows:
    /// <list type="number">
    /// <item>
    ///   Certain subexpressions <c>e1</c>, ..., <c>e_n</c> (which have types <c>T1</c>, ..., <c>T_n</c>)
    ///   of the lambda body [t] are replaced with bound variables <c>b1</c>, ..., <c>b_n</c> of the same types,
    ///   yielding a new lambda body [u], which represents a lifted lambda <c>(lambda x : T :: u)</c>.
    /// </item>
    /// <item>
    ///   The original lambda is replaced with a function call <c>f(e1, ..., en)</c> where <c>f</c> is a function
    ///   with <c>n</c> parameters and return type <c>[T] U</c> (i.e. the function returns a map).
    /// </item>
    /// <item>
    ///   The implementation of the lambda is defined through an axiom that states that
    ///   <c>f(b1, ..., b_n)[x] == u</c>.
    /// </item>
    /// </list>
    /// Lambda lifting algorithms differ based on what kind of subexpressions <c>E_i</c> are "lifted" out
    /// of the lambda:
    /// <list type="bullet"></list>
    /// <item>
    ///   <see cref="LambdaVisitor.LambdaLiftingFreeVars"/> lifts all free variables of a lambda;
    /// </item>
    /// <item>
    ///   <c>LambdaVisitor.LambdaLifterMaxHoles()</c> lifts a lambda's maximally large subexpressions that are
    ///   free of bound variables.
    /// </item>
    /// <see cref="LambdaVisitor.LambdaLifterMaxHoles"/> is used by default whereas <c>LambdaLiftingFreeVars</c>
    /// is used with the command-line option <c>/freeVarLambdaLifting</c>.
    /// </summary>
    public static void ExpandLambdas(Program prog) {
      Contract.Requires(prog != null);
      List<Expr/*!*/>/*!*/ axioms;
      List<Function/*!*/>/*!*/ functions;

      Desugar(prog, out axioms, out functions);
      foreach (var f in functions) {
        prog.AddTopLevelDeclaration(f);
      }
      foreach (var a in axioms) {
        prog.AddTopLevelDeclaration(new Axiom(a.tok, a));
      }
    }

    private class LambdaVisitor : StandardVisitor {
      private readonly Dictionary<Expr, FunctionCall> liftedLambdas = 
        new Dictionary<Expr, FunctionCall>(new AlphaEquality());

      internal List<Expr/*!*/>/*!*/ lambdaAxioms = new List<Expr/*!*/>();
      internal List<Function/*!*/>/*!*/ lambdaFunctions = new List<Function/*!*/>();
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(lambdaAxioms));
        Contract.Invariant(cce.NonNullElements(lambdaFunctions));
      }

      int lambdaid = 0;

      string FreshLambdaFunctionName()
      {
        return string.Format("lambda#{0}", lambdaid++);
      }

      public override Expr VisitLambdaExpr(LambdaExpr lambda) {
        var baseResult = base.VisitLambdaExpr(lambda);
        lambda = baseResult as LambdaExpr;
        if (lambda == null) {
          return baseResult;  // apparently, the base visitor already turned the lambda into something else
        }

        return CommandLineOptions.Clo.FreeVarLambdaLifting ? LiftLambdaFreeVars(lambda) : LiftLambdaMaxHoles(lambda);
      }
      
      /// <summary>
      /// Performs lambda lifting (see <see cref="LambdaHelper.ExpandLambdas"/>) by replacing the lambda's
      /// free variables with bound ones.
      /// </summary>
      /// <param name="lambda">A lambda expression
      ///   <code>(lambda x1: T1 ... x_n: T_n :: t)</code>
      /// where <c>t</c> contains the free variables <c>y1</c>, ..., <c>y_m</c>.
      /// </param>
      /// <returns>
      /// <list type="bullet">
      ///   <item>
      ///     A function application <c>f(y1, ..., y_m)</c> where <c>f</c>'s body is defined to be the result of
      ///     replacing the free variables <c>y1</c>, ..., <c>y_m</c> in <c>t</c> with bound variables
      ///     <c>b1</c>, ..., <c>b_m</c>.
      ///   </item>
      ///   <item>
      ///     Adds a definition and axiom for <c>f</c> to <see cref="lambdaFunctions"/> and <see cref="lambdaAxioms"/>.
      ///     Memoizes <c>f</c> as the lifted lambda for <para>lambda</para>.
      ///   </item>
      /// </list>
      /// </returns>
      private Expr LiftLambdaFreeVars(LambdaExpr lambda) {

        // We start by getting rid of any use of "old" inside the lambda.  This is done as follows.
        // For each variable "g" occurring inside lambda as "old(... g ...)", create a new name "og".
        // Replace each old occurrence of "g" with "og", removing the enclosing "old" wrappers.
        var oldFinder = new OldFinder();
        oldFinder.Visit(lambda);
        var oldSubst = new Dictionary<Variable, Expr>();  // g -> g0
        var callOldMapping = new Dictionary<Variable, Expr>();  // g0 -> old(g)
        foreach (var v in oldFinder.FreeOldVars) {
          var g = v as GlobalVariable;
          if (g != null) {
            var g0 = new GlobalVariable(g.tok, new TypedIdent(g.tok, g.TypedIdent.Name + "@old", g.TypedIdent.Type));
            oldSubst.Add(g, new IdentifierExpr(g0.tok, g0));
            callOldMapping.Add(g0, new OldExpr(g0.tok, new IdentifierExpr(g.tok, g)));
          }
        }
        var lambdaBody = Substituter.ApplyReplacingOldExprs(
          Substituter.SubstitutionFromHashtable(new Dictionary<Variable,Expr>()),
          Substituter.SubstitutionFromHashtable(oldSubst),
          lambda.Body);
        var lambdaAttrs = Substituter.ApplyReplacingOldExprs(
          Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>()),
          Substituter.SubstitutionFromHashtable(oldSubst),
          lambda.Attributes);

        if (0 < CommandLineOptions.Clo.VerifySnapshots && QKeyValue.FindStringAttribute(lambdaAttrs, "checksum") == null)
        {
          // Attach a dummy checksum to avoid issues in the dependency analysis.
          var checksumAttr = new QKeyValue(lambda.tok, "checksum", new List<object> { "lambda expression" }, null);
          if (lambdaAttrs == null)
          {
            lambdaAttrs = checksumAttr;
          }
          else
          {
            lambdaAttrs.AddLast(checksumAttr);
          }
        }

        // this is ugly, the output will depend on hashing order
        var subst = new Dictionary<Variable, Expr>();
        var substFnAttrs = new Dictionary<Variable, Expr>();
        var formals = new List<Variable>();
        var callArgs = new List<Expr>();
        var axCallArgs = new List<Expr>();
        var dummies = new List<Variable>(lambda.Dummies);
        var freeTypeVars = new List<TypeVariable>();
        var fnTypeVarActuals = new List<Type/*!*/>();
        var freshTypeVars = new List<TypeVariable>();  // these are only used in the lambda@n function's definition

        // compute the free variables of the lambda expression, but with lambdaBody instead of lambda.Body
        Set freeVars = new Set();
        BinderExpr.ComputeBinderFreeVariables(lambda.TypeParameters, lambda.Dummies, lambdaBody, null, lambdaAttrs, freeVars);

        foreach (object o in freeVars) {
          // 'o' is either a Variable or a TypeVariable.
          if (o is Variable) {
            var v = o as Variable;
            var ti = new TypedIdent(v.TypedIdent.tok, v.TypedIdent.Name, v.TypedIdent.Type);
            var f = new Formal(v.tok, ti, true);
            formals.Add(f);
            substFnAttrs.Add(v, new IdentifierExpr(f.tok, f));
            var b = new BoundVariable(v.tok, ti);
            dummies.Add(b);
            if (callOldMapping.ContainsKey(v)) {
              callArgs.Add(callOldMapping[v]);
            } else {
              callArgs.Add(new IdentifierExpr(v.tok, v));
            }
            Expr id = new IdentifierExpr(b.tok, b);
            subst.Add(v, id);
            axCallArgs.Add(id);
          } else {
            var tv = (TypeVariable)o;
            freeTypeVars.Add(tv);
            fnTypeVarActuals.Add(tv);
            freshTypeVars.Add(new TypeVariable(tv.tok, tv.Name));
          }
        }

        var sw = new System.IO.StringWriter();
        var wr = new TokenTextWriter(sw, true);
        lambda.Emit(wr);
        string lam_str = sw.ToString();

        FunctionCall fcall;
        IToken tok = lambda.tok;
        Formal res = new Formal(tok, new TypedIdent(tok, TypedIdent.NoName, cce.NonNull(lambda.Type)), false);

        if (liftedLambdas.TryGetValue(lambda, out fcall)) {
          if (CommandLineOptions.Clo.TraceVerify) {
            Console.WriteLine("Old lambda: {0}", lam_str);
          }
        } else {
          if (CommandLineOptions.Clo.TraceVerify) {
            Console.WriteLine("New lambda: {0}", lam_str);
          }
          Function fn = new Function(tok, FreshLambdaFunctionName(), freshTypeVars, formals, res, "auto-generated lambda function",
            Substituter.Apply(Substituter.SubstitutionFromHashtable(substFnAttrs), lambdaAttrs));
          fn.OriginalLambdaExprAsString = lam_str;

          fcall = new FunctionCall(new IdentifierExpr(tok, fn.Name));
          fcall.Func = fn;  // resolve here
          liftedLambdas[lambda] = fcall;

          List<Expr/*!*/> selectArgs = new List<Expr/*!*/>();
          foreach (Variable/*!*/ v in lambda.Dummies) {
            Contract.Assert(v != null);
            selectArgs.Add(new IdentifierExpr(v.tok, v));
          }
          NAryExpr axcall = new NAryExpr(tok, fcall, axCallArgs);
          axcall.Type = res.TypedIdent.Type;
          axcall.TypeParameters = SimpleTypeParamInstantiation.From(freeTypeVars, fnTypeVarActuals);
          NAryExpr select = Expr.Select(axcall, selectArgs);
          select.Type = lambdaBody.Type;
          List<Type/*!*/> selectTypeParamActuals = new List<Type/*!*/>();
          List<TypeVariable> forallTypeVariables = new List<TypeVariable>();
          foreach (TypeVariable/*!*/ tp in lambda.TypeParameters) {
            Contract.Assert(tp != null);
            selectTypeParamActuals.Add(tp);
            forallTypeVariables.Add(tp);
          }
          forallTypeVariables.AddRange(freeTypeVars);
          select.TypeParameters = SimpleTypeParamInstantiation.From(lambda.TypeParameters, selectTypeParamActuals);

          Expr bb = Substituter.Apply(Substituter.SubstitutionFromHashtable(subst), lambdaBody);
          NAryExpr body = Expr.Eq(select, bb);
          body.Type = Type.Bool;
          body.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
          Trigger trig = new Trigger(select.tok, true, new List<Expr> { select });

          lambdaFunctions.Add(fn);
          lambdaAxioms.Add(new ForallExpr(tok, forallTypeVariables, dummies,
            Substituter.Apply(Substituter.SubstitutionFromHashtable(subst), lambdaAttrs),
            trig, body));
        }

        NAryExpr call = new NAryExpr(tok, fcall, callArgs);
        call.Type = res.TypedIdent.Type;
        call.TypeParameters = SimpleTypeParamInstantiation.From(freeTypeVars, fnTypeVarActuals);

        return call;
      }
      
      /// <summary>
      /// Performs lambda lifting (see <see cref="LambdaHelper.ExpandLambdas"/>) by replacing with bound variables
      /// maximally large subexpressions of a lambda that do not contain any of the lambda's bound variables.
      /// </summary>
      /// <param name="lambda">A lambda expression
      ///   <code>(lambda x1: T1 ... x_n: T_n :: t)</code>
      /// where <c>t</c> contains the subexpressions <c>e1</c>, ..., <c>e_m</c>. These are maximally large
      /// subexpressions that do not contain the lambda's bound variables.
      /// </param>
      /// <returns>
      /// <list type="bullet">
      ///   <item>
      ///     A function application <c>f(y1, ..., y_m)</c> where <c>f</c>'s body is defined to be the result of
      ///     replacing the expressions <c>e1</c>, ..., <c>e_m</c> in <c>t</c> with bound variables
      ///     <c>b1</c>, ..., <c>b_m</c>.
      ///   </item>
      ///   <item>
      ///     Adds a definition and axiom for <c>f</c> to <see cref="lambdaFunctions"/> and <see cref="lambdaAxioms"/>.
      ///     Memoizes <c>f</c> as the lifted lambda for <para>lambda</para>.
      ///   </item>
      /// </list>
      /// </returns>
      private Expr LiftLambdaMaxHoles(LambdaExpr lambda) {
        
        // We start by getting rid of `old` expressions. Instead, we replace the free variables `x_i` that are
        // nested inside of `old` expressions with `old(x_i)` expressions.
        var oldFinder = new OldFinder();
        oldFinder.Visit(lambda);
        var oldSubst = new Dictionary<Variable, Expr>();
        foreach (var v in oldFinder.FreeOldVars) if (v is GlobalVariable g) {
          oldSubst.Add(g, new OldExpr(g.tok, new IdentifierExpr(g.tok, g)) {Type = g.TypedIdent.Type});
        }
        var lambdaBody = Substituter.ApplyReplacingOldExprs(
          Substituter.SubstitutionFromHashtable(new Dictionary<Variable,Expr>()),
          Substituter.SubstitutionFromHashtable(oldSubst),
          lambda.Body);
        var lambdaAttrs = Substituter.ApplyReplacingOldExprs(
          Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>()),
          Substituter.SubstitutionFromHashtable(oldSubst),
          lambda.Attributes);
        var newLambda =
          new LambdaExpr(lambda.tok, lambda.TypeParameters, lambda.Dummies, lambdaAttrs, lambdaBody) {
            Type = lambda.Type
          };
        
        // We perform lambda lifting on the resulting lambda which now contains only `old` expressions of the form
        // `old(x)` where `x` is a variable that is free in the lambda.
        return new MaxHolesLambdaLifter(
          newLambda, liftedLambdas, FreshLambdaFunctionName(), lambdaFunctions, lambdaAxioms).VisitLambdaExpr(newLambda);
      }

      public override Cmd VisitCallCmd(CallCmd node) {
        var baseResult = base.VisitCallCmd(node);
        node = baseResult as CallCmd;
        if (node == null) {
          return baseResult;  // apparently, the base visitor already turned the lambda into something else
        }
        // also visit the desugaring (which the StandardVisitor does not do)
        node.VisitDesugaring(this);
        return node;
      }
    }
  }

  class OldFinder : ReadOnlyVisitor
  {
    public readonly GSet<Variable> FreeOldVars = new GSet<Variable>();
    public override Expr VisitOldExpr(OldExpr node) {
      Set freeVars = new Set();
      node.Expr.ComputeFreeVariables(freeVars);
      foreach (var v in freeVars) {
        // Note, "v" is either a Variable or a TypeVariable
        if (v is Variable) {
          FreeOldVars.Add((Variable)v);
        }
      }
      return node;  // don't visit subexpressions, since ComputeFreeVariables has already gone through those
    }
    public override BinderExpr VisitBinderExpr(BinderExpr node) {
      base.VisitBinderExpr(node);
      // visit attributes, even though StandardVisitor does not do that (but maybe it should?)
      if (node.Attributes != null) {
        this.Visit(node.Attributes);
      }
      return node;
    }
  }

} // end namespace
