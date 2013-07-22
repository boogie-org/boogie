//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Boogie {

  using System;
  using System.IO;
  using System.Collections;
  using System.Collections.Generic;
  using System.Diagnostics;
  using System.Diagnostics.Contracts;
  using Set = GSet<object>;

  public static class LambdaHelper {
    public static Absy Desugar(Absy node, out List<Expr/*!*/>/*!*/ axioms, out List<Function/*!*/>/*!*/ functions) {
      Contract.Requires(node != null);
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out functions)));
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out axioms)));
      Contract.Ensures(Contract.Result<Absy>() != null);
      LambdaVisitor v = new LambdaVisitor();
      node = v.Visit(node);
      axioms = v.lambdaAxioms;
      functions = v.lambdaFunctions;
      if (CommandLineOptions.Clo.TraceVerify) {
        Console.WriteLine("Desugaring of lambda expressions produced {0} functions and {1} axioms:", functions.Count, axioms.Count);
        TokenTextWriter wr = new TokenTextWriter("<console>", Console.Out);
        foreach (Function f in functions) {
          f.Emit(wr, 0);
        }
        foreach (Expr ax in axioms) {
          ax.Emit(wr);
          Console.WriteLine();
        }
      }
      return node;
    }

    public static void ExpandLambdas(Program prog) {
      Contract.Requires(prog != null);
      List<Expr/*!*/>/*!*/ axioms;
      List<Function/*!*/>/*!*/ functions;

      Desugar(prog, out axioms, out functions);
      foreach (var f in functions) {
        prog.TopLevelDeclarations.Add(f);
      }
      foreach (var a in axioms) {
        prog.TopLevelDeclarations.Add(new Axiom(a.tok, a));
      }
    }

    private class LambdaVisitor : StandardVisitor {
      internal List<Expr/*!*/>/*!*/ lambdaAxioms = new List<Expr/*!*/>();
      internal List<Function/*!*/>/*!*/ lambdaFunctions = new List<Function/*!*/>();
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(lambdaAxioms));
        Contract.Invariant(cce.NonNullElements(lambdaFunctions));
      }

      static int lambdaid = 0;

      public override Program VisitProgram(Program prog) {
        //Contract.Requires(prog != null);
        Contract.Ensures(Contract.Result<Program>() != null);
        foreach (Declaration/*!*/ decl in prog.TopLevelDeclarations) {
          Contract.Assert(decl != null);
          if (decl is Axiom || decl is Function) {
            this.Visit(decl);
          }
        }

        return prog;
      }

      public override Procedure VisitProcedure(Procedure node) {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Procedure>() != null);
        // do not visit requires/ensures when calling this on Implementation
        return node;
      }

      public override Absy Visit(Absy node) {
        //Contract.Requires(node != null);
        Contract.Ensures(Contract.Result<Absy>() != null);
        node = base.Visit(node);

        LambdaExpr lambda = node as LambdaExpr;
        if (lambda != null) {
          IToken/*!*/ tok = lambda.tok;
          Contract.Assert(tok != null);

          Set freeVars = new Set();
          lambda.ComputeFreeVariables(freeVars);
          // this is ugly, the output will depend on hashing order
          Dictionary<Variable, Expr> subst = new Dictionary<Variable, Expr>();
          List<Variable> formals = new List<Variable>();
          List<Expr> callArgs = new List<Expr>();
          List<Expr> axCallArgs = new List<Expr>();
          List<Variable> dummies = new List<Variable>(lambda.Dummies);
          List<TypeVariable> freeTypeVars = new List<TypeVariable>();
          List<Type/*!*/> fnTypeVarActuals = new List<Type/*!*/>();
          List<TypeVariable> freshTypeVars = new List<TypeVariable>();  // these are only used in the lambda@n function's definition
          foreach (object o in freeVars) {
            // 'o' is either a Variable or a TypeVariable.  Since the lambda desugaring happens only
            // at the outermost level of a program (where there are no mutable variables) and, for
            // procedure bodies, after the statements have been passified (when mutable variables have
            // been replaced by immutable incarnations), we are interested only in BoundVar's and
            // TypeVariable's.
            BoundVariable v = o as BoundVariable;
            if (v != null) {
              TypedIdent ti = new TypedIdent(v.TypedIdent.tok, v.TypedIdent.Name, v.TypedIdent.Type);
              Formal f = new Formal(v.tok, ti, true);
              formals.Add(f);
              BoundVariable b = new BoundVariable(v.tok, ti);
              dummies.Add(b);
              callArgs.Add(new IdentifierExpr(v.tok, v));
              Expr/*!*/ id = new IdentifierExpr(f.tok, b);
              Contract.Assert(id != null);
              subst.Add(v, id);
              axCallArgs.Add(id);
            } else if (o is TypeVariable) {
              TypeVariable tv = (TypeVariable)o;
              freeTypeVars.Add(tv);
              fnTypeVarActuals.Add(tv);
              freshTypeVars.Add(new TypeVariable(tv.tok, tv.Name));
            }
          }

          Formal res = new Formal(tok, new TypedIdent(tok, TypedIdent.NoName, cce.NonNull(lambda.Type)), false);
          Function fn = new Function(tok, "lambda@" + lambdaid++, freshTypeVars, formals, res, "auto-generated lambda function", lambda.Attributes);
          lambdaFunctions.Add(fn);

          FunctionCall fcall = new FunctionCall(new IdentifierExpr(tok, fn.Name));
          fcall.Func = fn;  // resolve here

          List<Expr/*!*/> selectArgs = new List<Expr/*!*/>();
          foreach (Variable/*!*/ v in lambda.Dummies) {
            Contract.Assert(v != null);
            selectArgs.Add(new IdentifierExpr(v.tok, v));
          }
          NAryExpr axcall = new NAryExpr(tok, fcall, axCallArgs);
          axcall.Type = res.TypedIdent.Type;
          axcall.TypeParameters = SimpleTypeParamInstantiation.From(freeTypeVars, fnTypeVarActuals);
          NAryExpr select = Expr.Select(axcall, selectArgs);
          select.Type = lambda.Body.Type;
          List<Type/*!*/> selectTypeParamActuals = new List<Type/*!*/>();
          List<TypeVariable> forallTypeVariables = new List<TypeVariable>();
          foreach (TypeVariable/*!*/ tp in lambda.TypeParameters) {
            Contract.Assert(tp != null);
            selectTypeParamActuals.Add(tp);
            forallTypeVariables.Add(tp);
          }
          forallTypeVariables.AddRange(freeTypeVars);
          select.TypeParameters = SimpleTypeParamInstantiation.From(lambda.TypeParameters, selectTypeParamActuals);

          Expr bb = Substituter.Apply(Substituter.SubstitutionFromHashtable(subst), lambda.Body);
          NAryExpr body = Expr.Eq(select, bb);
          body.Type = Type.Bool;
          body.TypeParameters = SimpleTypeParamInstantiation.EMPTY;
          Trigger trig = new Trigger(select.tok, true, new List<Expr> { select });
          lambdaAxioms.Add(new ForallExpr(tok, forallTypeVariables, dummies, lambda.Attributes, trig, body));

          NAryExpr call = new NAryExpr(tok, fcall, callArgs);
          call.Type = res.TypedIdent.Type;
          call.TypeParameters = SimpleTypeParamInstantiation.From(freeTypeVars, fnTypeVarActuals);

          return call;
        }

        return node;
      }
    }
  }

} // end namespace