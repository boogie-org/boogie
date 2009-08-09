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
  class MethodTraverser : BaseCodeAndContractTraverser {
    public readonly ClassTraverser ClassTraverser;

    private Bpl.Procedure procedure;

    public Bpl.Variable RetVariable;

    public List<MethodParameter> OutVars = new List<MethodParameter>();

    public Bpl.Variable HeapVariable;        

    private Dictionary<ILocalDefinition, Bpl.LocalVariable> localVarMap = new Dictionary<ILocalDefinition, Bpl.LocalVariable>();

    internal class MethodParameter {
      public MethodParameter() {
        localParameter = null;
        inParameterCopy = null;
        outParameterCopy = null;
      }

      public Bpl.Formal localParameter;
      public Bpl.Formal inParameterCopy;
      public Bpl.Formal outParameterCopy;
    }

    private Dictionary<IParameterDefinition, MethodParameter> formalMap = new Dictionary<IParameterDefinition, MethodParameter>();

    #region Helper Functions
    /// <summary>
    /// 
    /// </summary>
    /// <param name="local"></param>
    /// <returns></returns>
    public Bpl.Variable FindOrCreateLocalVariable(ILocalDefinition local) {
      Bpl.LocalVariable v;
      Bpl.IToken tok = TranslationHelper.CciLocationToBoogieToken(local.Locations);
      Bpl.Type t = TranslationHelper.CciTypeToBoogie(local.Type.ResolvedType);
      if (!localVarMap.TryGetValue(local, out v)) {
        v = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, local.Name.Value, t));
        localVarMap.Add(local, v);
      }
      return v;
    }

    /// <summary>
    /// Creates a fresh local var of the given Type and adds it to the
    /// Bpl Implementation
    /// </summary>
    /// <param name="typedef"> The type of the new variable </param>
    /// <returns> A fresh Variable with automatic generated name and location </returns>
    public Bpl.Variable CreateFreshLocal(ITypeDefinition typedef) {
      Bpl.IToken loc = Bpl.Token.NoToken; // Helper Variables do not have a location
      Bpl.Type t = TranslationHelper.CciTypeToBoogie(typedef);
      Bpl.LocalVariable v = new Bpl.LocalVariable(loc, new Bpl.TypedIdent(loc, TranslationHelper.GenerateTempVarName(), t));
      ILocalDefinition dummy = new LocalDefinition(); // Creates a dummy entry for the Dict, since only locals in the dict are translated to boogie
      localVarMap.Add(dummy, v);
      return v;
    }

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

    /// <summary>
    /// 
    /// </summary>
    /// <param name="param"></param>
    /// <remarks>STUB</remarks>
    /// <returns></returns>
    public Bpl.Variable FindParameterVariable(IParameterDefinition param) {
      MethodParameter mp;
      formalMap.TryGetValue(param, out mp);
      return mp.localParameter;
    }
    #endregion

    public MethodTraverser(IContractProvider cp, ClassTraverser cTraverser)
      : base(cp) {
      HeapVariable = cTraverser.HeapVariable;
      procedure = null;
      ClassTraverser = cTraverser;
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="method"></param>
    public override void Visit(IMethodDefinition method) {

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

        #region Look for Returnvalue

        // This is just a hack, should be replaced with something more robust
        if (method.Type.TypeCode != PrimitiveTypeCode.Void) {
          Bpl.Type rettype = Bpl.Type.Int;
          out_count++;
          RetVariable = new Bpl.Formal(TranslationHelper.CciLocationToBoogieToken(method.Locations),
              new Bpl.TypedIdent(TranslationHelper.CciLocationToBoogieToken(method.Type.Locations),
                  "$result", rettype), false);
        } else {
          RetVariable = null;
        }

        #endregion

        #region Create $this parameter
        in_count++;
        Bpl.Type selftype = Bpl.Type.Int;
        Bpl.Formal self = new Bpl.Formal(TranslationHelper.CciLocationToBoogieToken(method.Locations),
            new Bpl.TypedIdent(TranslationHelper.CciLocationToBoogieToken(method.Type.Locations),
                "$inst", selftype), true);

        #endregion

        Bpl.Variable[] invars = new Bpl.Formal[in_count];
        Bpl.Variable[] outvars = new Bpl.Formal[out_count];

        int i = 0;
        int j = 0;

        #region Add $this parameter as first in parameter
        invars[i++] = self;
        #endregion

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            invars[i++] = mparam.inParameterCopy;
          }
          if (mparam.outParameterCopy != null) {
            outvars[j++] = mparam.outParameterCopy;
            OutVars.Add(mparam);
          }
        }

        #region add the returnvalue to out if there is one
        if (RetVariable != null) outvars[j] = RetVariable;
        #endregion
       
        #endregion

        #region Check The Method Contracts
        Bpl.RequiresSeq boogiePrecondition = new Bpl.RequiresSeq();
        Bpl.EnsuresSeq boogiePostcondition = new Bpl.EnsuresSeq();
        Bpl.IdentifierExprSeq boogieModifies = new Bpl.IdentifierExprSeq();

        IMethodContract contract = contractProvider.GetMethodContractFor(method);

        if (contract != null) {
          try {
            foreach (IPrecondition pre in contract.Preconditions) {
              ExpressionTraverser exptravers = new ExpressionTraverser(this);
              exptravers.Visit(pre.Condition); // TODO
              // Todo: Deal with Descriptions


              Bpl.Requires req
                  = new Bpl.Requires(TranslationHelper.CciLocationToBoogieToken(pre.Locations),
                      true, exptravers.TranslatedExpressions.Pop(), "");
              boogiePrecondition.Add(req);
            }

            foreach (IPostcondition post in contract.Postconditions) {
              ExpressionTraverser exptravers = new ExpressionTraverser(this);

              exptravers.Visit(post.Condition);
              // Todo: Deal with Descriptions

              Bpl.Ensures ens =
                  new Bpl.Ensures(TranslationHelper.CciLocationToBoogieToken(post.Locations),
                      true, exptravers.TranslatedExpressions.Pop(), "");
              boogiePostcondition.Add(ens);
            }

            foreach (IAddressableExpression mod in contract.ModifiedVariables) {
              ExpressionTraverser exptravers = new ExpressionTraverser(this);
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

        ClassTraverser.ToplevelTraverser.TranslatedProgram.TopLevelDeclarations.Add(proc);

        this.procedure = proc;

        if (method.IsAbstract) {
          throw new NotImplementedException("abstract methods are not yet implemented");
        }

        StatementTraverser stmtTraverser = new StatementTraverser(this);

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
          throw new NotImplementedException("No Errorhandling in Mehtodvisitor / " + te.ToString());
        } catch {
          throw;
        }

        #region Create Local Vars For Implementation
        //Todo: (mschaef) hack, there must be a better way to copy this
        Bpl.Variable[] vars = new Bpl.Variable[localVarMap.Values.Count + formalMap.Values.Count];
        i = 0;
        foreach (Bpl.Variable v in localVarMap.Values) {
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
        ClassTraverser.ToplevelTraverser.TranslatedProgram.TopLevelDeclarations.Add(impl);
      } catch (TranslationException te) {
        throw new NotImplementedException(te.ToString());
      } catch {
        throw;
      } finally {
        // Maybe this is a good place to add the procedure to the toplevel declarations
      }
    }

  }
}
