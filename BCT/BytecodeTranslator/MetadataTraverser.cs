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

    public Bpl.Variable HeapVariable;
    

    public MetadataTraverser(Sink sink, IContractProvider cp)
      : base() {
      this.sink = sink;
      this.factory = sink.Factory;
      ContractProvider = cp;
    }


    public Bpl.Program TranslatedProgram {
      get { return this.sink.TranslatedProgram; }
    }

    #region Method Helpers
    /// <summary>
    /// 
    /// </summary>
    /// <param name="param"></param>
    /// <remarks> (mschaef) only a stub </remarks>
    private MethodParameter CreateBoogieParameter(IParameterDefinition param) {
      MethodParameter mparam = new MethodParameter();

      Bpl.Type ptype = Bpl.Type.Int;

      Bpl.Formal v = new Bpl.Formal(TranslationHelper.CciLocationToBoogieToken(param.Locations),
          new Bpl.TypedIdent(TranslationHelper.CciLocationToBoogieToken(param.Type.Locations),
              param.Name.Value, ptype), false);

      Bpl.Formal v_in = null;
      if (!param.IsOut) {
        v_in = new Bpl.Formal(TranslationHelper.CciLocationToBoogieToken(param.Locations),
            new Bpl.TypedIdent(TranslationHelper.CciLocationToBoogieToken(param.Type.Locations),
                param.Name.Value + "$in", ptype), true);
      }
      Bpl.Formal v_out = null;
      if (param.IsByReference || param.IsOut) {
        v_out = new Bpl.Formal(TranslationHelper.CciLocationToBoogieToken(param.Locations),
            new Bpl.TypedIdent(TranslationHelper.CciLocationToBoogieToken(param.Type.Locations),
                param.Name.Value + "$out", ptype), false);
      }
      mparam.localParameter = v;
      mparam.inParameterCopy = v_in;
      mparam.outParameterCopy = v_out;

      return mparam;
    }

    #endregion Method Helpers

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
        foreach (IParameterDefinition formal in method.ResolvedMethod.Parameters) {

          mp = CreateBoogieParameter(formal);
          if (mp.inParameterCopy != null) in_count++;
          if (mp.outParameterCopy != null) out_count++;
          formalMap.Add(formal, mp);
        }
        this.sink.FormalMap = formalMap;

        #region Look for Returnvalue

        // This is just a hack, should be replaced with something more robust
        if (method.Type.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Type rettype = Bpl.Type.Int;
          out_count++;
          this.sink.RetVariable = new Bpl.Formal(TranslationHelper.CciLocationToBoogieToken(method.Locations),
              new Bpl.TypedIdent(TranslationHelper.CciLocationToBoogieToken(method.Type.Locations),
                  "$result", rettype), false);
        } else {
          this.sink.RetVariable = null;
        }

        #endregion

        #region Create 'this' parameter
        in_count++;
        Bpl.Type selftype = Bpl.Type.Int;
        Bpl.Formal self = new Bpl.Formal(TranslationHelper.CciLocationToBoogieToken(method.Locations),
            new Bpl.TypedIdent(TranslationHelper.CciLocationToBoogieToken(method.Type.Locations),
                "this", selftype), true);

        #endregion

        Bpl.Variable[] invars = new Bpl.Formal[in_count];
        Bpl.Variable[] outvars = new Bpl.Formal[out_count];

        int i = 0;
        int j = 0;

        #region Add 'this' parameter as first in parameter
        invars[i++] = self;
        #endregion

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            invars[i++] = mparam.inParameterCopy;
          }
          if (mparam.outParameterCopy != null) {
            outvars[j++] = mparam.outParameterCopy;
            this.sink.OutVars.Add(mparam);
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
                  = new Bpl.Requires(TranslationHelper.CciLocationToBoogieToken(pre.Locations),
                      true, exptravers.TranslatedExpressions.Pop(), "");
              boogiePrecondition.Add(req);
            }

            foreach (IPostcondition post in contract.Postconditions) {
              ExpressionTraverser exptravers = this.factory.MakeExpressionTraverser(this.sink, null);

              exptravers.Visit(post.Condition);
              // Todo: Deal with Descriptions

              Bpl.Ensures ens =
                  new Bpl.Ensures(TranslationHelper.CciLocationToBoogieToken(post.Locations),
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

        Bpl.Procedure proc = new Bpl.Procedure(TranslationHelper.CciLocationToBoogieToken(method.Locations),
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

        StatementTraverser stmtTraverser = this.factory.MakeStatementTraverser(this.sink);

        #region Add assignements from In-Params to local-Params

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            Bpl.IToken tok = TranslationHelper.CciLocationToBoogieToken(method.Locations);
            stmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
              new Bpl.IdentifierExpr(tok, mparam.localParameter),
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
        //Todo: (mschaef) hack, there must be a better way to copy this
        Bpl.Variable[] vars = new Bpl.Variable[this.sink.LocalVarMap.Values.Count + formalMap.Values.Count];
        i = 0;
        foreach (Bpl.Variable v in this.sink.LocalVarMap.Values) {
          vars[i++] = v;
        }
        foreach (MethodParameter mparam in formalMap.Values) {
          vars[i++] = mparam.localParameter;
        }

        Bpl.VariableSeq vseq = new Bpl.VariableSeq(vars);
        #endregion

        Bpl.Implementation impl =
            new Bpl.Implementation(TranslationHelper.CciLocationToBoogieToken(method.Locations),
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