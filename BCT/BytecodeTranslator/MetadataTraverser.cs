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
using TranslationPlugins;
using BytecodeTranslator.Phone;


namespace BytecodeTranslator {

  /// <summary>
  /// Responsible for traversing all metadata elements (i.e., everything exclusive
  /// of method bodies).
  /// </summary>
  public class MetadataTraverser : BaseMetadataTraverser {

    readonly Sink sink;

    public readonly TraverserFactory factory;

    public readonly IDictionary<IUnit, PdbReader> PdbReaders;
    public PdbReader/*?*/ PdbReader;

    public MetadataTraverser(Sink sink, IDictionary<IUnit, PdbReader> pdbReaders)
      : base() {
      this.sink = sink;
      this.factory = sink.Factory;
      this.PdbReaders = pdbReaders;
    }

    #region Overrides

    public override void Visit(IModule module) {
      this.PdbReaders.TryGetValue(module, out this.PdbReader);
      base.Visit(module);
    }

    public override void Visit(IAssembly assembly) {
      this.PdbReaders.TryGetValue(assembly, out this.PdbReader);
      this.sink.BeginAssembly(assembly);
      try {
        base.Visit(assembly);
      } finally {
        this.sink.EndAssembly(assembly);
      }
    }

    /// <summary>
    /// Translate the type definition.
    /// </summary>
    /// 
    public override void Visit(ITypeDefinition typeDefinition) {

      if (!this.sink.TranslateType(typeDefinition)) return;

      var savedPrivateTypes = this.privateTypes;
      this.privateTypes = new List<ITypeDefinition>();

      trackPageNameVariableName(typeDefinition);
      trackPhoneApplicationClassname(typeDefinition);

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
        ITypeDefinition unspecializedType = Microsoft.Cci.MutableContracts.ContractHelper.Unspecialized(typeDefinition).ResolvedType;
        sink.AddDelegateType(unspecializedType);
      } else if (typeDefinition.IsInterface) {
        sink.FindOrCreateType(typeDefinition);
        base.Visit(typeDefinition);
      } else if (typeDefinition.IsEnum) {
        return; // enums just are translated as ints
      } else if (typeDefinition.IsStruct) {
        sink.FindOrCreateType(typeDefinition);
        CreateDefaultStructConstructor(typeDefinition);
        CreateStructCopyConstructor(typeDefinition);
        base.Visit(typeDefinition);
      } else {
        Console.WriteLine("Unknown kind of type definition '{0}' was found",
          TypeHelper.GetTypeName(typeDefinition));
        throw new NotImplementedException(String.Format("Unknown kind of type definition '{0}'.", TypeHelper.GetTypeName(typeDefinition)));
      }
      this.Visit(typeDefinition.PrivateHelperMembers);
      foreach (var t in this.privateTypes) {
        this.Visit(t);
      }
    }
    List<ITypeDefinition> privateTypes = new List<ITypeDefinition>();

    private void trackPhoneApplicationClassname(ITypeDefinition typeDef) {
      if (PhoneCodeHelper.instance().PhonePlugin != null && typeDef.isPhoneApplicationClass(sink.host)) {
        INamespaceTypeDefinition namedTypeDef = typeDef as INamespaceTypeDefinition;
        // string fullyQualifiedName = namedTypeDef.ContainingNamespace.Name.Value + "." + namedTypeDef.Name.Value;
        string fullyQualifiedName = namedTypeDef.ToString();
        PhoneCodeHelper.instance().setMainAppTypeReference(typeDef);
        PhoneCodeHelper.instance().setMainAppTypeName(fullyQualifiedName);
      }
    }

    private void trackPageNameVariableName(ITypeDefinition typeDef) {
      if (PhoneCodeHelper.instance().PhonePlugin != null && typeDef.isPhoneApplicationPageClass(sink.host)) {
        INamespaceTypeDefinition namedTypeDef = typeDef as INamespaceTypeDefinition;
        string fullyQualifiedName = namedTypeDef.ToString();
        string xamlForClass = PhoneCodeHelper.instance().getXAMLForPage(fullyQualifiedName);
        if (xamlForClass != null) { // if not it is possibly an abstract page
          string uriName = UriHelper.getURIBase(xamlForClass);
          Bpl.Constant uriConstant = sink.FindOrCreateConstant(uriName);
          PhoneCodeHelper.instance().setBoogieStringPageNameForPageClass(fullyQualifiedName, uriConstant.Name);
        }
      }
    }

    private void CreateDefaultStructConstructor(ITypeDefinition typeDefinition) {
      Contract.Requires(typeDefinition.IsStruct);

      var proc = this.sink.FindOrCreateProcedureForDefaultStructCtor(typeDefinition);

      this.sink.BeginMethod(typeDefinition);
      var stmtTranslator = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, false);
      var stmts = new List<IStatement>();

      foreach (var f in typeDefinition.Fields) {
        if (f.IsStatic) continue;
        var s = new ExpressionStatement() {
          Expression = new Assignment() {
            Source = new DefaultValue() { DefaultValueType = f.Type, Type = f.Type, },
            Target = new TargetExpression() {
              Definition = f,
              Instance = new ThisReference() { Type = typeDefinition, },
              Type = f.Type,
            },
            Type = f.Type,
          },
        };
      }

      stmtTranslator.Visit(stmts);
      var translatedStatements = stmtTranslator.StmtBuilder.Collect(Bpl.Token.NoToken);

      var lit = Bpl.Expr.Literal(1);
      lit.Type = Bpl.Type.Int;
      var args = new List<object> { lit };
      var attrib = new Bpl.QKeyValue(typeDefinition.Token(), "inline", args, null); // TODO: Need to have it be {:inine 1} (and not just {:inline})?

      List<Bpl.Variable> vars = new List<Bpl.Variable>();
      foreach (Bpl.Variable v in this.sink.LocalVarMap.Values) {
        vars.Add(v);
      }
      Bpl.VariableSeq vseq = new Bpl.VariableSeq(vars.ToArray());

      Bpl.Implementation impl =
        new Bpl.Implementation(Bpl.Token.NoToken,
        proc.Name,
        new Bpl.TypeVariableSeq(),
        proc.InParams,
        proc.OutParams,
        vseq,
        translatedStatements,
        attrib,
        new Bpl.Errors()
        );

      impl.Proc = (Bpl.Procedure) proc; // TODO: get rid of cast
      this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
    }
    
    private void CreateStructCopyConstructor(ITypeDefinition typeDefinition) {
      Contract.Requires(typeDefinition.IsStruct);

      var proc = this.sink.FindOrCreateProcedureForStructCopy(typeDefinition);

      var stmtBuilder = new Bpl.StmtListBuilder();

      foreach (var f in typeDefinition.Fields) {
        if (f.IsStatic) continue;
        var boogieType = sink.CciTypeToBoogie(f.Type);
        var fExp = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(f));
        var e = this.sink.Heap.ReadHeap(Bpl.Expr.Ident(proc.InParams[0]), fExp, AccessType.Struct, boogieType);
        var o = Bpl.Expr.Ident(proc.InParams[1]);
        var c = this.sink.Heap.WriteHeap(Bpl.Token.NoToken, o, fExp, e, AccessType.Struct, boogieType);
        stmtBuilder.Add(c);
      }

      var lit = Bpl.Expr.Literal(1);
      lit.Type = Bpl.Type.Int;
      var args = new List<object> { lit };
      var attrib = new Bpl.QKeyValue(typeDefinition.Token(), "inline", args, null); // TODO: Need to have it be {:inine 1} (and not just {:inline})?
      Bpl.Implementation impl =
        new Bpl.Implementation(Bpl.Token.NoToken,
        proc.Name,
        new Bpl.TypeVariableSeq(),
        proc.InParams,
        proc.OutParams,
        new Bpl.VariableSeq(),
        stmtBuilder.Collect(Bpl.Token.NoToken),
        attrib,
        new Bpl.Errors()
        );

      impl.Proc = (Bpl.Procedure)proc; // TODO: get rid of cast
      this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
    }

    private bool sawCctor = false;

    private void CreateStaticConstructor(ITypeDefinition typeDefinition) {
      var typename = TypeHelper.GetTypeName(typeDefinition, Microsoft.Cci.NameFormattingOptions.DocumentationId);
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

      this.sink.BeginMethod(typeDefinition);

      var stmtTranslator = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, false);
      var stmts = new List<IStatement>();

      foreach (var f in typeDefinition.Fields) {
        if (!f.IsStatic) continue;
        stmts.Add(
          new ExpressionStatement() {
            Expression = new Assignment() {
              Source = new DefaultValue() { DefaultValueType = f.Type, Type = f.Type, },
              Target = new TargetExpression() {
                Definition = f,
                Instance = null,
                Type = f.Type,
              },
              Type = f.Type,
            }
          });
      }

      stmtTranslator.Visit(stmts);
      var translatedStatements = stmtTranslator.StmtBuilder.Collect(Bpl.Token.NoToken);

      List<Bpl.Variable> vars = new List<Bpl.Variable>();
      foreach (Bpl.Variable v in this.sink.LocalVarMap.Values) {
        vars.Add(v);
      }
      Bpl.VariableSeq vseq = new Bpl.VariableSeq(vars.ToArray());

      Bpl.Implementation impl =
        new Bpl.Implementation(Bpl.Token.NoToken,
        proc.Name,
        new Bpl.TypeVariableSeq(),
        proc.InParams,
        proc.OutParams,
        vseq,
        translatedStatements
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


      Sink.ProcedureInfo procInfo;
      IMethodDefinition stubMethod = null;
      if (IsStubMethod(method, out stubMethod)) {
        procInfo = this.sink.FindOrCreateProcedure(stubMethod);
      } else {
        procInfo = this.sink.FindOrCreateProcedure(method);
      }

      if (method.IsAbstract) { // we're done, just define the procedure
        return;
      }

      this.sink.BeginMethod(method);
      var decl = procInfo.Decl;
      var proc = decl as Bpl.Procedure;
      var formalMap = procInfo.FormalMap;

      // FEEDBACK inline handler methods to avoid more false alarms
      if (PhoneCodeHelper.instance().PhoneFeedbackToggled && PhoneCodeHelper.instance().isMethodInputHandlerOrFeedbackOverride(method) &&
          !PhoneCodeHelper.instance().isMethodIgnoredForFeedback(method)) {
            proc.AddAttribute("inline", new Bpl.LiteralExpr(Bpl.Token.NoToken, Microsoft.Basetypes.BigNum.ONE));
            PhoneCodeHelper.instance().trackCallableMethod(proc);
      }

      try {
        StatementTraverser stmtTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, false);

        // FEEDBACK if this is a feedback method it will be plagued with false asserts. They will trigger if $Exception becomes other than null
        // FEEDBACK for modular analysis we need it to be non-null at the start
        // FEEDBACK also, callee is obviously non null
        IMethodDefinition translatedMethod= sink.getMethodBeingTranslated();
        if (PhoneCodeHelper.instance().PhoneFeedbackToggled && translatedMethod != null &&
            PhoneCodeHelper.instance().isMethodInputHandlerOrFeedbackOverride(translatedMethod)) {
          // assign null to exception
          List<Bpl.AssignLhs> assignee= new List<Bpl.AssignLhs>();
          Bpl.AssignLhs exceptionAssignee= new Bpl.SimpleAssignLhs(Bpl.Token.NoToken, Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable));
          assignee.Add(exceptionAssignee);
          List<Bpl.Expr> value= new List<Bpl.Expr>();
          value.Add(Bpl.Expr.Ident(this.sink.Heap.NullRef));
          Bpl.Cmd exceptionAssign= new Bpl.AssignCmd(Bpl.Token.NoToken, assignee, value);
          stmtTraverser.StmtBuilder.Add(exceptionAssign);
        }

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

        #region Translate method attributes
        // Don't need an expression translator because there is a limited set of things
        // that can appear as arguments to custom attributes
        // TODO: decode enum values
        try {
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
                if (mdc.Type.IsEnum) {
                  var lit = Bpl.Expr.Literal((int) mdc.Value);
                  lit.Type = Bpl.Type.Int;
                  o = lit;
                } else {
                  switch (mdc.Type.TypeCode) {
                    case PrimitiveTypeCode.Boolean:
                      o = (bool) mdc.Value ? Bpl.Expr.True : Bpl.Expr.False;
                      break;
                    case PrimitiveTypeCode.Int32:
                      var lit = Bpl.Expr.Literal((int) mdc.Value);
                      lit.Type = Bpl.Type.Int;
                      o = lit;
                      break;
                    case PrimitiveTypeCode.String:
                      o = mdc.Value;
                      break;
                    default:
                      throw new InvalidCastException("Invalid metadata constant type");
                  }
                }
                args[argIndex++] = o;
              }
            }
            decl.AddAttribute(attrName, args);
          }
        } catch (InvalidCastException) {
          Console.WriteLine("Warning: Cannot translate custom attributes for method\n    '{0}':",
            MemberHelper.GetMethodSignature(method, NameFormattingOptions.None));
          Console.WriteLine("    >>Skipping attributes, continuing with method translation");
        }
        #endregion

        #region Translate body
        var helperTypes = stmtTraverser.TranslateMethod(method);
        if (helperTypes != null) {
          this.privateTypes.AddRange(helperTypes);
        }
        #endregion

        #region Create Local Vars For Implementation
        List<Bpl.Variable> vars = new List<Bpl.Variable>();
        foreach (MethodParameter mparam in formalMap.Values) {
          if (!mparam.underlyingParameter.IsByReference)
            vars.Add(mparam.outParameterCopy);
        }
        foreach (Bpl.Variable v in this.sink.LocalVarMap.Values) {
          vars.Add(v);
        }
        vars.Add(procInfo.LocalExcVariable);
        vars.Add(procInfo.LabelVariable);
        Bpl.VariableSeq vseq = new Bpl.VariableSeq(vars.ToArray());
        #endregion

        var translatedBody = stmtTraverser.StmtBuilder.Collect(Bpl.Token.NoToken);

        #region Add implementation to Boogie program
        if (proc != null) {
          Bpl.Implementation impl =
              new Bpl.Implementation(method.Token(),
                  decl.Name,
                  new Microsoft.Boogie.TypeVariableSeq(),
                  decl.InParams,
                  decl.OutParams,
                  vseq,
                  translatedBody);

          impl.Proc = proc;
          this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
        } else { // method is translated as a function
          //var func = decl as Bpl.Function;
          //Contract.Assume(func != null);
          //var blocks = new List<Bpl.Block>();
          //var counter = 0;
          //var returnValue = decl.OutParams[0];
          //foreach (var bb in translatedBody.BigBlocks) {
          //  var label = bb.LabelName ?? "L" + counter++.ToString();
          //  var newTransferCmd = (bb.tc is Bpl.ReturnCmd)
          //    ? new Bpl.ReturnExprCmd(bb.tc.tok, Bpl.Expr.Ident(returnValue))
          //    : bb.tc;
          //  var b = new Bpl.Block(bb.tok, label, bb.simpleCmds, newTransferCmd);
          //  blocks.Add(b);
          //}
          //var localVars = new Bpl.VariableSeq();
          //localVars.Add(returnValue);
          //func.Body = new Bpl.CodeExpr(localVars, blocks);
        }
        #endregion

      } catch (TranslationException te) {
        Console.WriteLine("Translation error in body of \n    '{0}':",
          MemberHelper.GetMethodSignature(method, NameFormattingOptions.None));
        Console.WriteLine("\t" + te.Message);
      } catch (Exception e) {
        Console.WriteLine("Error encountered during translation of \n    '{0}':",
          MemberHelper.GetMethodSignature(method, NameFormattingOptions.None));
        Console.WriteLine("\t>>" + e.Message);
      } finally {
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
                Source = new DefaultValue() { DefaultValueType = f.Type, Type = f.Type, },
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
      Bpl.Variable fieldVar= this.sink.FindOrCreateFieldVariable(fieldDefinition);

      // if tracked by the phone plugin, we need to find out the bpl assigned name for future use
      if (PhoneCodeHelper.instance().PhonePlugin != null) {
        trackControlVariableName(fieldDefinition, fieldVar);
        trackNavigationVariableName(fieldDefinition, fieldVar);
      }
    }

    private static void trackNavigationVariableName(IFieldDefinition fieldDefinition, Bpl.Variable fieldVar) {
      if (fieldDefinition.Name.Value.Equals(PhoneCodeHelper.IL_CURRENT_NAVIGATION_URI_VARIABLE)) {
        PhoneCodeHelper.instance().setBoogieNavigationVariable(fieldVar.Name);
      }
    }

    private static void trackControlVariableName(IFieldDefinition fieldDefinition, Bpl.Variable fieldVar) {
      INamespaceTypeReference namedContainerRef = fieldDefinition.ContainingType as INamespaceTypeReference;
      if (namedContainerRef != null) {
        string containerName = namedContainerRef.ContainingUnitNamespace.Unit.Name.Value + "." + namedContainerRef.Name.Value;
        IEnumerable<ControlInfoStructure> controls = PhoneCodeHelper.instance().PhonePlugin.getControlsForPage(containerName);
        if (controls != null) {
          ControlInfoStructure ctrlInfo = controls.FirstOrDefault(ctrl => ctrl.Name == fieldDefinition.Name.Value);
          if (ctrlInfo != null)
            ctrlInfo.BplName = fieldVar.Name;
        }
      }
    }
    #endregion

    private void addPhoneTopLevelDeclarations() {
      if (PhoneCodeHelper.instance().PhoneNavigationToggled) {
        Bpl.Variable continueOnPageVar = sink.FindOrCreateGlobalVariable(PhoneCodeHelper.BOOGIE_CONTINUE_ON_PAGE_VARIABLE, Bpl.Type.Bool);
        sink.TranslatedProgram.TopLevelDeclarations.Add(continueOnPageVar);
        Bpl.Variable navigationCheckVar = sink.FindOrCreateGlobalVariable(PhoneCodeHelper.BOOGIE_NAVIGATION_CHECK_VARIABLE, Bpl.Type.Bool);
        sink.TranslatedProgram.TopLevelDeclarations.Add(navigationCheckVar);
      }
    }

    #region Public API
    public virtual void TranslateAssemblies(IEnumerable<IUnit> assemblies) {
      if (PhoneCodeHelper.instance().PhonePlugin != null)
        addPhoneTopLevelDeclarations();

      foreach (var a in assemblies) {
        a.Dispatch(this);
      }
    }
    #endregion

    #region Helpers
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

    #endregion

  }
}