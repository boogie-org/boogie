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
using System.Diagnostics.Contracts;


namespace BytecodeTranslator {

  /// <summary>
  /// Responsible for traversing all metadata elements (i.e., everything exclusive
  /// of method bodies).
  /// </summary>
  public class MetadataTraverser : BaseMetadataTraverser {

    readonly Sink sink;

    public readonly TraverserFactory factory;

    public readonly PdbReader/*?*/ PdbReader;

    public MetadataTraverser(Sink sink, PdbReader/*?*/ pdbReader)
      : base() {
      this.sink = sink;
      this.factory = sink.Factory;
      this.PdbReader = pdbReader;
    }

    #region Overrides

    public override void Visit(IModule module) {
      base.Visit(module);
    }

    public override void Visit(IAssembly assembly) {
      base.Visit(assembly);
      foreach (ITypeDefinition type in sink.delegateTypeToDelegates.Keys)
      {
        CreateDispatchMethod(type);
      }
    }

    private Bpl.IfCmd BuildReturnCmd(Bpl.Expr b) {
      Bpl.StmtListBuilder ifStmtBuilder = new Bpl.StmtListBuilder();
      ifStmtBuilder.Add(new Bpl.ReturnCmd(b.tok));
      return new Bpl.IfCmd(b.tok, b, ifStmtBuilder.Collect(b.tok), null, null);
    }

    private Bpl.IfCmd BuildIfCmd(Bpl.Expr b, Bpl.Cmd cmd, Bpl.IfCmd ifCmd)
    {
      Bpl.StmtListBuilder ifStmtBuilder;
      ifStmtBuilder = new Bpl.StmtListBuilder();
      ifStmtBuilder.Add(cmd);
      return new Bpl.IfCmd(b.tok, b, ifStmtBuilder.Collect(b.tok), ifCmd, null);
    }

    private void CreateDispatchMethod(ITypeDefinition type)
    {
      Contract.Assert(type.IsDelegate);
      IMethodDefinition invokeMethod = null;
      foreach (IMethodDefinition m in type.Methods)
      {
        if (m.Name.Value == "Invoke")
        {
          invokeMethod = m;
          break;
        }
      }
      
      try
      {
        var proc = this.sink.FindOrCreateProcedure(invokeMethod);
        var invars = proc.InParams;
        var outvars = proc.OutParams;

        Bpl.IToken token = invokeMethod.Token();
        
        Bpl.Formal method = new Bpl.Formal(token, new Bpl.TypedIdent(token, "method", Bpl.Type.Int), true);
        Bpl.Formal receiver = new Bpl.Formal(token, new Bpl.TypedIdent(token, "receiver", Bpl.Type.Int), true);

        Bpl.VariableSeq dispatchProcInvars = new Bpl.VariableSeq();
        dispatchProcInvars.Add(method);
        dispatchProcInvars.Add(receiver);
        for (int i = 1; i < invars.Length; i++) {
          Bpl.Variable f = invars[i];
          dispatchProcInvars.Add(new Bpl.Formal(token, new Bpl.TypedIdent(token, f.Name, f.TypedIdent.Type), true));
        }

        Bpl.VariableSeq dispatchProcOutvars = new Bpl.VariableSeq();
        foreach (Bpl.Formal f in outvars) {
          dispatchProcOutvars.Add(new Bpl.Formal(token, new Bpl.TypedIdent(token, f.Name, f.TypedIdent.Type), false));
        }

        Bpl.Procedure dispatchProc = 
          new Bpl.Procedure(token, 
            "DispatchOne." + proc.Name, 
            new Bpl.TypeVariableSeq(), 
            dispatchProcInvars, 
            dispatchProcOutvars, 
            new Bpl.RequiresSeq(), 
            new Bpl.IdentifierExprSeq(), 
            new Bpl.EnsuresSeq());
        this.sink.TranslatedProgram.TopLevelDeclarations.Add(dispatchProc);

        Bpl.IfCmd ifCmd = BuildIfCmd(Bpl.Expr.True, new Bpl.AssumeCmd(token, Bpl.Expr.False), null);
        foreach (IMethodDefinition defn in sink.delegateTypeToDelegates[type]) {
          Bpl.ExprSeq ins = new Bpl.ExprSeq();
          Bpl.IdentifierExprSeq outs = new Bpl.IdentifierExprSeq();
          if (!defn.IsStatic)
            ins.Add(Bpl.Expr.Ident(receiver));
          int index;
          for (index = 2; index < dispatchProcInvars.Length; index++) {
            ins.Add(Bpl.Expr.Ident(dispatchProcInvars[index]));
          }
          for (index = 0; index < dispatchProcOutvars.Length; index++) {
            outs.Add(Bpl.Expr.Ident(dispatchProcOutvars[index]));
          }
          Bpl.Constant c = sink.FindOrAddDelegateMethodConstant(defn);
          Bpl.Expr bexpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, Bpl.Expr.Ident(method), Bpl.Expr.Ident(c));
          Bpl.CallCmd callCmd = new Bpl.CallCmd(token, c.Name, ins, outs);
          ifCmd = BuildIfCmd(bexpr, callCmd, ifCmd);
        }
        Bpl.StmtListBuilder ifStmtBuilder = new Bpl.StmtListBuilder();
        ifStmtBuilder.Add(ifCmd);
        Bpl.Implementation dispatchImpl =
            new Bpl.Implementation(token,
                dispatchProc.Name,
                new Bpl.TypeVariableSeq(),
                dispatchProc.InParams,
                dispatchProc.OutParams,
                new Bpl.VariableSeq(), 
                ifStmtBuilder.Collect(token)
                );
        dispatchImpl.Proc = dispatchProc;
        this.sink.TranslatedProgram.TopLevelDeclarations.Add(dispatchImpl);

        Bpl.LocalVariable iter = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "iter", Bpl.Type.Int));
        Bpl.LocalVariable niter = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "niter", Bpl.Type.Int));

        Bpl.StmtListBuilder implStmtBuilder = new Bpl.StmtListBuilder();
        implStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(iter), this.sink.ReadHead(Bpl.Expr.Ident(invars[0]))));

        Bpl.StmtListBuilder whileStmtBuilder = new Bpl.StmtListBuilder();
        whileStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(niter), this.sink.ReadNext(Bpl.Expr.Ident(invars[0]), Bpl.Expr.Ident(iter))));
        whileStmtBuilder.Add(BuildReturnCmd(Bpl.Expr.Eq(Bpl.Expr.Ident(niter), this.sink.ReadHead(Bpl.Expr.Ident(invars[0])))));
        Bpl.ExprSeq inExprs = new Bpl.ExprSeq();
        inExprs.Add(this.sink.ReadMethod(Bpl.Expr.Ident(invars[0]), Bpl.Expr.Ident(niter)));
        inExprs.Add(this.sink.ReadReceiver(Bpl.Expr.Ident(invars[0]), Bpl.Expr.Ident(niter)));
        for (int i = 1; i < invars.Length; i++) {
          Bpl.Variable f = invars[i];
          inExprs.Add(Bpl.Expr.Ident(f));
        }
        Bpl.IdentifierExprSeq outExprs = new Bpl.IdentifierExprSeq();
        foreach (Bpl.Formal f in outvars) {
          outExprs.Add(Bpl.Expr.Ident(f));
        }
        whileStmtBuilder.Add(new Bpl.CallCmd(token, dispatchProc.Name, inExprs, outExprs));
        whileStmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(iter), Bpl.Expr.Ident(niter)));
        Bpl.WhileCmd whileCmd = new Bpl.WhileCmd(token, Bpl.Expr.True, new List<Bpl.PredicateCmd>(), whileStmtBuilder.Collect(token));

        implStmtBuilder.Add(whileCmd);

        Bpl.Implementation impl =
            new Bpl.Implementation(token,
                proc.Name,
                new Bpl.TypeVariableSeq(),
                invars,
                outvars,
                new Bpl.VariableSeq(iter, niter),
                implStmtBuilder.Collect(token)
                );
        impl.Proc = proc;
        this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
      }
      catch (TranslationException te)
      {
        throw new NotImplementedException(te.ToString());
      }
      catch
      {
        throw;
      }
      finally
      {
        // Maybe this is a good place to add the procedure to the toplevel declarations
      }
    }

    /// <summary>
    /// Translate the type definition.
    /// </summary>
    /// 
    public override void Visit(ITypeDefinition typeDefinition) {

      if (typeDefinition.IsClass) {
        bool savedSawCctor = this.sawCctor;
        this.sawCctor = false;
        sink.FindOrCreateType(typeDefinition);
        base.Visit(typeDefinition);
        if (!this.sawCctor) {
          CreateStaticConstructor(typeDefinition);
        }
        this.sawCctor = savedSawCctor;
      } else if (typeDefinition.IsDelegate) {
        sink.AddDelegateType(typeDefinition);
      } else if (typeDefinition.IsInterface) {
        sink.FindOrCreateType(typeDefinition);
        base.Visit(typeDefinition);
      } else if (typeDefinition.IsEnum) {
        return; // enums just are translated as ints
      } else if (typeDefinition.IsStruct) {
        Console.WriteLine("Skipping definition of '" + TypeHelper.GetTypeName(typeDefinition) + "' because it is a struct!");
      } else {
        Console.WriteLine("Unknown kind of type definition '{0}' was found",
          TypeHelper.GetTypeName(typeDefinition));
        throw new NotImplementedException(String.Format("Unknown kind of type definition '{0}'.", TypeHelper.GetTypeName(typeDefinition)));
      }
    }

    private bool sawCctor = false;

    private void CreateStaticConstructor(ITypeDefinition typeDefinition) {
      var typename = TypeHelper.GetTypeName(typeDefinition);
      typename = TranslationHelper.TurnStringIntoValidIdentifier(typename);
      var proc = new Bpl.Procedure(Bpl.Token.NoToken, typename + ".#cctor",
          new Bpl.TypeVariableSeq(),
          new Bpl.VariableSeq(), // in
          new Bpl.VariableSeq(), // out
          new Bpl.RequiresSeq(),
          new Bpl.IdentifierExprSeq(), // modifies
          new Bpl.EnsuresSeq()
          );

      this.sink.TranslatedProgram.TopLevelDeclarations.Add(proc);

      var stmtBuilder = new Bpl.StmtListBuilder();
      foreach (var f in typeDefinition.Fields) {
        if (f.IsStatic) {

          Bpl.Expr e;
          var bplType = TranslationHelper.CciTypeToBoogie(f.Type);
          if (bplType == Bpl.Type.Int) {
            e = Bpl.Expr.Literal(0);
            e.Type = Bpl.Type.Int;
          } else if (bplType == Bpl.Type.Bool) {
            e = Bpl.Expr.False;
            e.Type = Bpl.Type.Bool;
          } else {
            throw new NotImplementedException("Don't know how to translate type");
          }

          stmtBuilder.Add(
            TranslationHelper.BuildAssignCmd(
            Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(f)), 
            e
            ));
        }
      }
      Bpl.Implementation impl =
        new Bpl.Implementation(Bpl.Token.NoToken,
        proc.Name,
        new Bpl.TypeVariableSeq(),
        proc.InParams,
        proc.OutParams,
        new Bpl.VariableSeq(),
        stmtBuilder.Collect(Bpl.Token.NoToken)
        );

      impl.Proc = proc;
      this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);


    }

    /// <summary>
    /// 
    /// </summary>
    public override void Visit(IMethodDefinition method) {

      if (method.IsStaticConstructor) this.sawCctor = true;

      bool isEventAddOrRemove = method.IsSpecialName && (method.Name.Value.StartsWith("add_") || method.Name.Value.StartsWith("remove_"));
      if (isEventAddOrRemove)
        return;

      this.sink.BeginMethod();

      Sink.ProcedureInfo procAndFormalMap;
      IMethodDefinition stubMethod = null;
      if (IsStubMethod(method, out stubMethod)) {
        procAndFormalMap = this.sink.FindOrCreateProcedureAndReturnProcAndFormalMap(stubMethod);
      } else {
        procAndFormalMap = this.sink.FindOrCreateProcedureAndReturnProcAndFormalMap(method);
      }

      if (method.IsAbstract) { // we're done, just define the procedure
        return;
      }

      var proc = procAndFormalMap.Procedure;
      var formalMap = procAndFormalMap.FormalMap;
      this.sink.RetVariable = procAndFormalMap.ReturnVariable;

      try {

        StatementTraverser stmtTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, false);

        #region Add assignments from In-Params to local-Params

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            Bpl.IToken tok = method.Token();
            stmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
              new Bpl.IdentifierExpr(tok, mparam.outParameterCopy),
              new Bpl.IdentifierExpr(tok, mparam.inParameterCopy)));
          }
        }

        #endregion

        #region For non-deferring ctors and all cctors, initialize all fields to null-equivalent values
        var inits = InitializeFieldsInConstructor(method);
        if (0 < inits.Count) {
          new BlockStatement() { Statements = inits, }.Dispatch(stmtTraverser);
        }
        #endregion

        try {
          method.Body.Dispatch(stmtTraverser);
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
                proc.Name,
                new Microsoft.Boogie.TypeVariableSeq(),
                proc.InParams,
                proc.OutParams,
                vseq,
                stmtTraverser.StmtBuilder.Collect(Bpl.Token.NoToken));

        impl.Proc = proc;

        #region Translate method attributes
        // Don't need an expression translator because there is a limited set of things
        // that can appear as arguments to custom attributes
        foreach (var a in method.Attributes) {
          var attrName = TypeHelper.GetTypeName(a.Type);
          if (attrName.EndsWith("Attribute"))
            attrName = attrName.Substring(0, attrName.Length - 9);
          var args = new object[IteratorHelper.EnumerableCount(a.Arguments)];
          int argIndex = 0;
          foreach (var c in a.Arguments) {
            var mdc = c as IMetadataConstant;
            if (mdc != null) {
              object o;
              switch (mdc.Type.TypeCode) {
                case PrimitiveTypeCode.Boolean:
                  o = (bool)mdc.Value ? Bpl.Expr.True : Bpl.Expr.False;
                  break;
                case PrimitiveTypeCode.Int32:
                  var lit = Bpl.Expr.Literal((int)mdc.Value);
                  lit.Type = Bpl.Type.Int;
                  o = lit;
                  break;
                case PrimitiveTypeCode.String:
                  o = mdc.Value;
                  break;
                default:
                  throw new InvalidCastException("Invalid metadata constant type");
              }
              args[argIndex++] = o;
            }
          }
          impl.AddAttribute(attrName, args);
        }
        #endregion

        this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);

      } catch (TranslationException te) {
        throw new NotImplementedException(te.ToString());
      } catch {
        throw;
      } finally {
        // Maybe this is a good place to add the procedure to the toplevel declarations
      }
    }

    private static List<IStatement> InitializeFieldsInConstructor(IMethodDefinition method) {
      Contract.Ensures(Contract.Result<List<IStatement>>() != null);
      var inits = new List<IStatement>();
      if (method.IsConstructor || method.IsStaticConstructor) {
        var smb = method.Body as ISourceMethodBody;
        if (method.IsStaticConstructor || (smb != null && !FindCtorCall.IsDeferringCtor(method, smb.Block))) {
          var thisExp = new ThisReference() { Type = method.ContainingTypeDefinition, };
          foreach (var f in method.ContainingTypeDefinition.Fields) {
            if (f.IsStatic == method.IsStatic) {
              var a = new Assignment() {
                Source = new DefaultValue() { Type = f.Type, },
                Target = new TargetExpression() { Definition = f, Instance = method.IsConstructor ? thisExp : null, Type = f.Type },
                Type = f.Type,
              };
              inits.Add(new ExpressionStatement() { Expression = a, });
            }
          }
        }
      }
      return inits;
    }
    // TODO: do a type test, not a string test for the attribute
    private bool IsStubMethod(IMethodDefinition methodDefinition, out IMethodDefinition/*?*/ stubMethod) {
      stubMethod = null;
      var td = GetTypeDefinitionFromAttribute(methodDefinition.Attributes, "BytecodeTranslator.StubAttribute");
      if (td == null)
        td = GetTypeDefinitionFromAttribute(methodDefinition.ContainingTypeDefinition.Attributes, "BytecodeTranslator.StubAttribute");
      if (td != null) {
        foreach (var mem in td.GetMatchingMembersNamed(methodDefinition.Name, false,
          tdm => {
            var md = tdm as IMethodDefinition;
            return md != null && MemberHelper.MethodsAreEquivalent(methodDefinition, md);
          })) {
          stubMethod = mem as IMethodDefinition;
          return true;
        }
      }
      return false;
    }
    public static ITypeDefinition/*?*/ GetTypeDefinitionFromAttribute(IEnumerable<ICustomAttribute> attributes, string attributeName) {
      ICustomAttribute foundAttribute = null;
      foreach (ICustomAttribute attribute in attributes) {
        if (TypeHelper.GetTypeName(attribute.Type) == attributeName) {
          foundAttribute = attribute;
          break;
        }
      }
      if (foundAttribute == null) return null;
      List<IMetadataExpression> args = new List<IMetadataExpression>(foundAttribute.Arguments);
      if (args.Count < 1) return null;
      IMetadataTypeOf abstractTypeMD = args[0] as IMetadataTypeOf;
      if (abstractTypeMD == null) return null;
      ITypeReference referencedTypeReference = Microsoft.Cci.MutableContracts.ContractHelper.Unspecialized(abstractTypeMD.TypeToGet);
      ITypeDefinition referencedTypeDefinition = referencedTypeReference.ResolvedType;
      return referencedTypeDefinition;
    }

    public override void Visit(IFieldDefinition fieldDefinition) {
      this.sink.FindOrCreateFieldVariable(fieldDefinition);
    }

    #endregion

    private class FindCtorCall : BaseCodeTraverser {
      private bool isDeferringCtor = false;
      public ITypeReference containingType;
      public static bool IsDeferringCtor(IMethodDefinition method, IBlockStatement body) {
        var fcc = new FindCtorCall(method.ContainingType);
        fcc.Visit(body);
        return fcc.isDeferringCtor;
      }
      private FindCtorCall(ITypeReference containingType) {
        this.containingType = containingType;
      }
      public override void Visit(IMethodCall methodCall) {
        var md = methodCall.MethodToCall.ResolvedMethod;
        if (md != null && md.IsConstructor && methodCall.ThisArgument is IThisReference) {
          this.isDeferringCtor = TypeHelper.TypesAreEquivalent(md.ContainingType, containingType);
          this.stopTraversal = true;
          return;
        }
        base.Visit(methodCall);
      }
    }
  }
}