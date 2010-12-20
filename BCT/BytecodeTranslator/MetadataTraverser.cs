//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;


namespace BytecodeTranslator {

  /// <summary>
  /// Responsible for traversing all metadata elements (i.e., everything exclusive
  /// of method bodies).
  /// </summary>
  public class MetadataTraverser : BaseMetadataTraverser {

    readonly Sink sink;

    public readonly TraverserFactory factory;

    public readonly IContractProvider ContractProvider;

    public readonly ISourceLocationProvider/*?*/ SourceLocationProvider;

    public Bpl.Variable HeapVariable;


    public MetadataTraverser(Sink sink, IContractProvider cp, ISourceLocationProvider/*?*/ sourceLocationProvider)
      : base() {
      this.sink = sink;
      this.factory = sink.Factory;
      ContractProvider = cp;
      this.SourceLocationProvider = sourceLocationProvider;
    }

    public Bpl.Program TranslatedProgram {
      get { return this.sink.TranslatedProgram; }
    }

    #region Overrides

    public override void Visit(IModule module) {
      base.Visit(module);
    }

    public override void Visit(IAssembly assembly) {
      base.Visit(assembly);
    }

    /// <summary>
    /// Visits only classes: throws an exception for all other type definitions.
    /// </summary>
    /// 


    public override void Visit(ITypeDefinition typeDefinition) {

      if (typeDefinition.IsClass) {

        base.Visit(typeDefinition);

      } else {
        Console.WriteLine("Non-Class {0} was found", typeDefinition);
        throw new NotImplementedException(String.Format("Non-Class Type {0} is not yet supported.", typeDefinition.ToString()));
      }
    }

    #region Local state for each method

    #endregion

    /// <summary>
    /// 
    /// </summary>
    public override void Visit(IMethodDefinition method) {

      Dictionary<IParameterDefinition, MethodParameter> formalMap = new Dictionary<IParameterDefinition, MethodParameter>();
      this.sink.BeginMethod();

      try {
        #region Create in- and out-parameters

        int in_count = 0;
        int out_count = 0;
        MethodParameter mp;
        foreach (IParameterDefinition formal in method.Parameters) {

          mp = new MethodParameter(formal);
          if (mp.inParameterCopy != null) in_count++;
          if (mp.outParameterCopy != null && (formal.IsByReference || formal.IsOut))
            out_count++;
          formalMap.Add(formal, mp);
        }
        this.sink.FormalMap = formalMap;

        #region Look for Returnvalue

        if (method.Type.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Type rettype = TranslationHelper.CciTypeToBoogie(method.Type);
          out_count++;
          this.sink.RetVariable = new Bpl.Formal(method.Token(),
              new Bpl.TypedIdent(method.Type.Token(),
                  "$result", rettype), false);
        } else {
          this.sink.RetVariable = null;
        }

        #endregion

        Bpl.Formal/*?*/ self = null;
        #region Create 'this' parameter
        if (!method.IsStatic) {
          in_count++;
          Bpl.Type selftype = Bpl.Type.Int;
          self = new Bpl.Formal(method.Token(),
              new Bpl.TypedIdent(method.Type.Token(),
                  "this", selftype), true);
        }
        #endregion

        Bpl.Variable[] invars = new Bpl.Formal[in_count];
        Bpl.Variable[] outvars = new Bpl.Formal[out_count];

        int i = 0;
        int j = 0;

        #region Add 'this' parameter as first in parameter
        if (!method.IsStatic)
          invars[i++] = self;
        #endregion

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            invars[i++] = mparam.inParameterCopy;
          }
          if (mparam.outParameterCopy != null) {
            if (mparam.underlyingParameter.IsByReference || mparam.underlyingParameter.IsOut)
              outvars[j++] = mparam.outParameterCopy;
          }
        }

        #region add the returnvalue to out if there is one
        if (this.sink.RetVariable != null) outvars[j] = this.sink.RetVariable;
        #endregion

        #endregion

        #region Check The Method Contracts
        Bpl.RequiresSeq boogiePrecondition = new Bpl.RequiresSeq();
        Bpl.EnsuresSeq boogiePostcondition = new Bpl.EnsuresSeq();
        Bpl.IdentifierExprSeq boogieModifies = new Bpl.IdentifierExprSeq();

        IMethodContract contract = ContractProvider.GetMethodContractFor(method);

        if (contract != null) {
          try {
            foreach (IPrecondition pre in contract.Preconditions) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this.sink, null);
              exptravers.Visit(pre.Condition); // TODO
              // Todo: Deal with Descriptions


              Bpl.Requires req
                  = new Bpl.Requires(pre.Token(),
                      true, exptravers.TranslatedExpressions.Pop(), "");
              boogiePrecondition.Add(req);
            }

            foreach (IPostcondition post in contract.Postconditions) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this.sink, null);

              exptravers.Visit(post.Condition);
              // Todo: Deal with Descriptions

              Bpl.Ensures ens =
                  new Bpl.Ensures(post.Token(),
                      true, exptravers.TranslatedExpressions.Pop(), "");
              boogiePostcondition.Add(ens);
            }

            foreach (IAddressableExpression mod in contract.ModifiedVariables) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this.sink, null);
              exptravers.Visit(mod);

              Bpl.IdentifierExpr idexp = exptravers.TranslatedExpressions.Pop() as Bpl.IdentifierExpr;

              if (idexp == null) {
                throw new TranslationException(String.Format("Cannot create IdentifierExpr for Modifyed Variable {0}", mod.ToString()));
              }
              boogieModifies.Add(idexp);
            }
          } catch (TranslationException te) {
            throw new NotImplementedException("Cannot Handle Errors in Method Contract: " + te.ToString());
          } catch {
            throw;
          }
        }

        #endregion

        string MethodName = TranslationHelper.CreateUniqueMethodName(method);

        Bpl.Procedure proc = new Bpl.Procedure(method.Token(),
            MethodName, // make it unique!
            new Bpl.TypeVariableSeq(),
            new Bpl.VariableSeq(invars), // in
            new Bpl.VariableSeq(outvars), // out
            boogiePrecondition,
            boogieModifies,
            boogiePostcondition);

        this.sink.TranslatedProgram.TopLevelDeclarations.Add(proc);

        if (method.IsAbstract) {
          throw new NotImplementedException("abstract methods are not yet implemented");
        }

        StatementTraverser stmtTraverser = this.factory.MakeStatementTraverser(this.sink, this.SourceLocationProvider);

        #region Add assignements from In-Params to local-Params

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            Bpl.IToken tok = method.Token();
            stmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
              new Bpl.IdentifierExpr(tok, mparam.outParameterCopy),
              new Bpl.IdentifierExpr(tok, mparam.inParameterCopy)));
          }
        }

        #endregion

        try {
          method.ResolvedMethod.Body.Dispatch(stmtTraverser);
        } catch (TranslationException te) {
          throw new NotImplementedException("No Errorhandling in Methodvisitor / " + te.ToString());
        } catch {
          throw;
        }

        #region Create Local Vars For Implementation
        List<Bpl.Variable> vars = new List<Bpl.Variable>();
        foreach (MethodParameter mparam in formalMap.Values) {
          if (!(mparam.underlyingParameter.IsByReference || mparam.underlyingParameter.IsOut))
            vars.Add(mparam.outParameterCopy);
        }
        foreach (Bpl.Variable v in this.sink.LocalVarMap.Values) {
          vars.Add(v);
        }

        Bpl.VariableSeq vseq = new Bpl.VariableSeq(vars.ToArray());
        #endregion

        Bpl.Implementation impl =
            new Bpl.Implementation(method.Token(),
                MethodName, // make unique
                new Microsoft.Boogie.TypeVariableSeq(),
                new Microsoft.Boogie.VariableSeq(invars),
                new Microsoft.Boogie.VariableSeq(outvars),
                vseq,
                stmtTraverser.StmtBuilder.Collect(Bpl.Token.NoToken));

        impl.Proc = proc;
        this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
      } catch (TranslationException te) {
        throw new NotImplementedException(te.ToString());
      } catch {
        throw;
      } finally {
        // Maybe this is a good place to add the procedure to the toplevel declarations
      }
    }

    public override void Visit(IFieldDefinition fieldDefinition) {
      this.sink.FindOrCreateFieldVariable(fieldDefinition);
    }

    #endregion

  }
}