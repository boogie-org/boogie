using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

public class LinearRewriter
{
  private CivlTypeChecker civlTypeChecker;

  private Monomorphizer monomorphizer => civlTypeChecker.program.monomorphizer;
  
  private ConcurrencyOptions options => civlTypeChecker.Options;

  public LinearRewriter(CivlTypeChecker civlTypeChecker)
  {
    this.civlTypeChecker = civlTypeChecker;
  }
  
  public static bool IsPrimitive(DeclWithFormals decl)
  {
    return CivlPrimitives.LinearPrimitives.Contains(Monomorphizer.GetOriginalDecl(decl).Name);
  }

  public static void Rewrite(CivlTypeChecker civlTypeChecker, Implementation impl)
  {
    var linearRewriter = new LinearRewriter(civlTypeChecker);
    impl.Blocks.ForEach(block => block.Cmds = linearRewriter.RewriteCmdSeq(block.Cmds));
  }

  private List<Cmd> RewriteCmdSeq(List<Cmd> cmdSeq)
  {
    var newCmdSeq = new List<Cmd>();
    foreach (var cmd in cmdSeq)
    {
      if (cmd is AssignCmd assignCmd)
      {
        assignCmd.Rhss.Where(LinearStoreVisitor.HasLinearStoreAccess).ForEach(expr => {
          CreateAccessAsserts(expr, expr.tok, "Illegal access");
        });
        assignCmd.Lhss.Where(LinearStoreVisitor.HasLinearStoreAccess).ForEach(assignLhs => {
          CreateAccessAsserts(assignLhs, assignLhs.tok, "Illegal access");
        });
        newCmdSeq.Add(cmd);
      }
      else if (cmd is CallCmd callCmd)
      {
        callCmd.Ins.Where(LinearStoreVisitor.HasLinearStoreAccess).ForEach(expr => {
          CreateAccessAsserts(expr, expr.tok, "Illegal access");
        });
        if (IsPrimitive(callCmd.Proc))
        {
          newCmdSeq.AddRange(RewriteCallCmd(callCmd));
        }
        else
        {
          newCmdSeq.Add(cmd);
        }
      }
      else
      {
        newCmdSeq.Add(cmd);
      }
    }
    return newCmdSeq;
  }

  public List<Cmd> RewriteCallCmd(CallCmd callCmd)
  {
    switch (Monomorphizer.GetOriginalDecl(callCmd.Proc).Name)
    {
      case "Ref_Alloc":
        return RewriteRefAlloc(callCmd);
      case "Lheap_Empty":
        return RewriteLheapEmpty(callCmd);
      case "Lheap_Alloc":
        return RewriteLheapAlloc(callCmd);
      case "Lheap_Free":
        return RewriteLheapFree(callCmd);
      case "Lheap_Get":
        return RewriteLheapGet(callCmd);
      case "Lheap_Put":
        return RewriteLheapPut(callCmd);
      case "Lmap_Alloc":
        return RewriteLmapAlloc(callCmd);
      case "Lmap_Free":
        return RewriteLmapFree(callCmd);
      case "Lmap_Get":
        return RewriteLmapGet(callCmd);
      case "Lmap_Put":
        return RewriteLmapPut(callCmd);
      case "Lset_Empty":
        return RewriteLsetEmpty(callCmd);
      case "Lset_Split":
        return RewriteLsetSplit(callCmd);
      case "Lset_Get":
        return RewriteLsetGet(callCmd);
      case "Lset_Put":
        return RewriteLsetPut(callCmd);
      case "Lval_Split":
        return RewriteLvalSplit(callCmd);
      case "Lval_Get":
        return RewriteLvalGet(callCmd);
      case "Lval_Put":
        return RewriteLvalPut(callCmd);
      default:
        Contract.Assume(false);
        return null;
    }
  }

  private AssertCmd AssertCmd(IToken tok, Expr expr, string msg)
  {
    var assertCmd = CmdHelper.AssertCmd(tok, expr, msg);
    return assertCmd;
  }
  
  private Function MapConst(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("MapConst",
      new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function MapImp(Type domain)
  {
    return monomorphizer.InstantiateFunction("MapImp", new Dictionary<string, Type>() { { "T", domain } });
  }

  private Function MapDiff(Type domain)
  {
    return monomorphizer.InstantiateFunction("MapDiff", new Dictionary<string, Type>() { { "T", domain } });  
  }

  private Function MapOne(Type domain)
  {
    return monomorphizer.InstantiateFunction("MapOne", new Dictionary<string, Type>() { { "T", domain } });  
  }
  
  private Function MapOr(Type domain)
  {
    return monomorphizer.InstantiateFunction("MapOr", new Dictionary<string, Type>() { { "T", domain } });
  }

  private Function MapIte(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("MapIte",new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function LheapContains(Type type)
  {
    return monomorphizer.InstantiateFunction("Lheap_Contains",new Dictionary<string, Type>() { { "V", type } });
  }
  
  private Function LheapDeref(Type type)
  {
    return monomorphizer.InstantiateFunction("Lheap_Deref",new Dictionary<string, Type>() { { "V", type } });
  }
  
  private Function LsetContains(Type type)
  {
    return monomorphizer.InstantiateFunction("Lset_Contains",new Dictionary<string, Type>() { { "V", type } });
  }
  
  private static Expr Dom(Expr path)
  {
    return ExprHelper.FieldAccess(path, "dom");
  }
  
  private static Expr Val(Expr path)
  {
    return ExprHelper.FieldAccess(path, "val");
  }

  private Expr Default(Type type)
  {
    var defaultFunc = monomorphizer.InstantiateFunction("Default", new Dictionary<string, Type>() { { "T", type } });
    return ExprHelper.FunctionCall(defaultFunc);
  }
  
  private List<Cmd> RewriteRefAlloc(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var nilFunc = monomorphizer.InstantiateFunction("Nil", instantiation);

    var cmdSeq = new List<Cmd>();
    var k = callCmd.Outs[0];

    cmdSeq.Add(CmdHelper.HavocCmd(k));
    cmdSeq.Add(CmdHelper.AssumeCmd(Expr.Neq(Val(k), ExprHelper.FunctionCall(nilFunc))));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLheapEmpty(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var cmdSeq = new List<Cmd>();
    var l = callCmd.Outs[0].Decl;
    
    var mapConstFunc1 = MapConst(refType, Type.Bool);
    var mapConstFunc2 = MapConst(refType, type);

    cmdSeq.Add(CmdHelper.AssignCmd(l,
      ExprHelper.FunctionCall(lheapConstructor, ExprHelper.FunctionCall(mapConstFunc1, Expr.False),
        ExprHelper.FunctionCall(mapConstFunc2, Default(type)))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLheapAlloc(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var nilFunc = monomorphizer.InstantiateFunction("Nil", instantiation);
    
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var v = callCmd.Ins[1];
    var l = callCmd.Outs[0];

    cmdSeq.Add(CmdHelper.HavocCmd(l));
    cmdSeq.Add(CmdHelper.AssumeCmd(Expr.Neq(Val(l), ExprHelper.FunctionCall(nilFunc))));
    cmdSeq.Add(CmdHelper.AssumeCmd(Expr.Not(ExprHelper.FunctionCall(new MapSelect(callCmd.tok, 1), Dom(path), Val(l)))));
    cmdSeq.Add(CmdHelper.AssumeCmd(Expr.Eq(ExprHelper.FunctionCall(new MapSelect(callCmd.tok, 1), Val(path), Val(l)), v)));
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lheapConstructor,
        ExprHelper.FunctionCall(new MapStore(callCmd.tok, 1), Dom(path), Val(l), Expr.True),
        Val(path))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLheapFree(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    
    var lheapContainsFunc = LheapContains(type);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(lheapContainsFunc, path, k), "Lheap_Free failed"));

    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lheapConstructor,
        ExprHelper.FunctionCall(new MapStore(callCmd.tok, 1), Dom(path), k, Expr.False),
        ExprHelper.FunctionCall(new MapStore(callCmd.tok, 1), Val(path), k, Default(type)))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLheapGet(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var l = callCmd.Outs[0].Decl;
    
    var mapImpFunc = MapImp(refType);
    var mapIteFunc = MapIte(refType, type);
    var mapConstFunc1 = MapConst(refType, Type.Bool);
    var mapConstFunc2 = MapConst(refType, type);
    var mapDiffFunc = MapDiff(refType);
    
    cmdSeq.Add(AssertCmd(callCmd.tok,
      Expr.Eq(ExprHelper.FunctionCall(mapImpFunc, k, Dom(path)), ExprHelper.FunctionCall(mapConstFunc1, Expr.True)),
      "Lheap_Get failed"));
    
    cmdSeq.Add(CmdHelper.AssignCmd(l,
      ExprHelper.FunctionCall(lheapConstructor, k,
        ExprHelper.FunctionCall(mapIteFunc, k, Val(path), ExprHelper.FunctionCall(mapConstFunc2, Default(type))))));
    
    cmdSeq.Add(CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lheapConstructor, ExprHelper.FunctionCall(mapDiffFunc, Dom(path), k),
        ExprHelper.FunctionCall(mapIteFunc, ExprHelper.FunctionCall(mapDiffFunc, Dom(path), k), Val(path),
          ExprHelper.FunctionCall(mapConstFunc2, Default(type))))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLheapPut(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var mapOrFunc = MapOr(refType);
    var mapIteFunc = MapIte(refType, type);
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lheapConstructor,
        ExprHelper.FunctionCall(mapOrFunc, Dom(path), Dom(l)),
        ExprHelper.FunctionCall(mapIteFunc, Dom(path), Val(path), Val(l)))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLmapAlloc(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type keyType, out Type valType, out Function lmapConstructor);

    var cmdSeq = new List<Cmd>();
    var k = callCmd.Ins[0];
    var val = callCmd.Ins[1];
    var l = callCmd.Outs[0].Decl;

    cmdSeq.Add(CmdHelper.AssignCmd(l, ExprHelper.FunctionCall(lmapConstructor, Dom(k), val)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLmapFree(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type keyType, out Type valType, out Function lmapConstructor);
    var lsetTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lset", new List<Type>() { keyType });
    var lsetConstructor = lsetTypeCtorDecl.Constructors[0];

    var cmdSeq = new List<Cmd>();
    var l = callCmd.Ins[0];
    var k = callCmd.Outs[0].Decl;

    cmdSeq.Add(CmdHelper.AssignCmd(k, ExprHelper.FunctionCall(lsetConstructor, Dom(l))));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLmapGet(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type keyType, out Type valType, out Function lmapConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var l = callCmd.Outs[0].Decl;

    var mapImpFunc = MapImp(keyType);
    var mapIteFunc = MapIte(keyType, valType);
    var mapConstFunc1 = MapConst(keyType, Type.Bool);
    var mapConstFunc2 = MapConst(keyType, valType);
    var mapDiffFunc = MapDiff(keyType);

    cmdSeq.Add(AssertCmd(callCmd.tok,
      Expr.Eq(ExprHelper.FunctionCall(mapImpFunc, k, Dom(path)), ExprHelper.FunctionCall(mapConstFunc1, Expr.True)),
      "Lmap_Get failed"));

    cmdSeq.Add(CmdHelper.AssignCmd(l,
      ExprHelper.FunctionCall(lmapConstructor, k,
        ExprHelper.FunctionCall(mapIteFunc, k, Val(path), ExprHelper.FunctionCall(mapConstFunc2, Default(valType))))));

    cmdSeq.Add(CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lmapConstructor, ExprHelper.FunctionCall(mapDiffFunc, Dom(path), k),
        ExprHelper.FunctionCall(mapIteFunc, ExprHelper.FunctionCall(mapDiffFunc, Dom(path), k), Val(path),
          ExprHelper.FunctionCall(mapConstFunc2, Default(valType))))));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLmapPut(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type keyType, out Type valType, out Function lmapConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var mapOrFunc = MapOr(keyType);
    var mapIteFunc = MapIte(keyType, valType);
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lmapConstructor,
        ExprHelper.FunctionCall(mapOrFunc, Dom(path), Dom(l)),
        ExprHelper.FunctionCall(mapIteFunc, Dom(path), Val(path), Val(l)))));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLsetEmpty(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var cmdSeq = new List<Cmd>();
    var l = callCmd.Outs[0].Decl;
    
    var mapConstFunc = MapConst(type, Type.Bool);
    cmdSeq.Add(CmdHelper.AssignCmd(l, ExprHelper.FunctionCall(lsetConstructor,ExprHelper.FunctionCall(mapConstFunc, Expr.False))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLsetSplit(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var mapConstFunc = MapConst(type, Type.Bool);
    var mapImpFunc = MapImp(type);
    cmdSeq.Add(AssertCmd(callCmd.tok,
      Expr.Eq(ExprHelper.FunctionCall(mapImpFunc, Dom(l), Dom(path)), ExprHelper.FunctionCall(mapConstFunc, Expr.True)),
      "Lset_Split failed"));

    var mapDiffFunc = MapDiff(type);
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(path, "dom"),ExprHelper.FunctionCall(mapDiffFunc, Dom(path), Dom(l))));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLsetGet(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var l = callCmd.Outs[0];

    var mapConstFunc = MapConst(type, Type.Bool);
    var mapImpFunc = MapImp(type);
    cmdSeq.Add(AssertCmd(callCmd.tok,
      Expr.Eq(ExprHelper.FunctionCall(mapImpFunc, k, Dom(path)), ExprHelper.FunctionCall(mapConstFunc, Expr.True)),
      "Lset_Get failed"));

    var mapDiffFunc = MapDiff(type);
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(path, "dom"),ExprHelper.FunctionCall(mapDiffFunc, Dom(path), k)));

    cmdSeq.Add(CmdHelper.AssignCmd(l.Decl, ExprHelper.FunctionCall(lsetConstructor, k)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLsetPut(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var mapOrFunc = MapOr(type);
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lsetConstructor, ExprHelper.FunctionCall(mapOrFunc, Dom(path), Dom(l)))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLvalSplit(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var lsetContainsFunc = LsetContains(type);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(lsetContainsFunc, path, Val(l)), "Lval_Split failed"));

    var mapOneFunc = MapOne(type);
    var mapDiffFunc = MapDiff(type);
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(path, "dom"),
        ExprHelper.FunctionCall(mapDiffFunc, Dom(path), ExprHelper.FunctionCall(mapOneFunc, Val(l)))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLvalGet(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var l = callCmd.Outs[0];

    var lsetContainsFunc = LsetContains(type);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(lsetContainsFunc, path, k), "Lval_Get failed"));

    var mapOneFunc = MapOne(type);
    var mapDiffFunc = MapDiff(type);
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(path, "dom"),
        ExprHelper.FunctionCall(mapDiffFunc, Dom(path), ExprHelper.FunctionCall(mapOneFunc, k))));

    cmdSeq.Add(CmdHelper.AssignCmd(l.Decl, ExprHelper.FunctionCall(lvalConstructor, k)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLvalPut(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];
    
    var mapOneFunc = MapOne(type);
    var mapOrFunc = MapOr(type);
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lsetConstructor,
        ExprHelper.FunctionCall(mapOrFunc, Dom(path), ExprHelper.FunctionCall(mapOneFunc, Val(l))))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private void GetRelevantInfo(CallCmd callCmd, out Type type, out Type refType, out Function lheapConstructor,
    out Function lsetConstructor, out Function lvalConstructor)
  {
    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    type = instantiation["V"];
    var actualTypeParams = new List<Type>() { type };
    var refTypeCtorDecl = monomorphizer.InstantiateTypeCtorDecl("Ref", actualTypeParams);
    refType = new CtorType(Token.NoToken, refTypeCtorDecl, new List<Type>());
    var lheapTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lheap", actualTypeParams);
    lheapConstructor = lheapTypeCtorDecl.Constructors[0];
    var lsetTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lset", actualTypeParams);
    lsetConstructor = lsetTypeCtorDecl.Constructors[0];
    var lvalTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lval", actualTypeParams);
    lvalConstructor = lvalTypeCtorDecl.Constructors[0];
  }
  
  private void GetRelevantInfo(CallCmd callCmd, out Type keyType, out Type valType, out Function lmapConstructor)
  {
    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    keyType = instantiation["K"];
    valType = instantiation["V"];
    var actualTypeParams = new List<Type>() { keyType, valType };
    var lmapTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lmap", actualTypeParams);
    lmapConstructor = lmapTypeCtorDecl.Constructors[0];
  }

  private void ResolveAndTypecheck(CoreOptions options, IEnumerable<Absy> absys)
  {
    var rc = new ResolutionContext(null, options);
    absys.ForEach(absy => absy.Resolve(rc));
    if (rc.ErrorCount != 0)
    {
      return;
    }
    var tc = new TypecheckingContext(null, options);
    var oldCheckModifies = tc.CheckModifies;
    tc.CheckModifies = false;
    absys.ForEach(absy => absy.Typecheck(tc));
    tc.CheckModifies = oldCheckModifies;
  }

  private List<Cmd> CreateAccessAsserts(Expr expr, IToken tok, string msg)
  {
    if (expr is NAryExpr nAryExpr)
    {
      if (nAryExpr.Fun is FieldAccess)
      {
        return CreateAccessAsserts(nAryExpr.Args[0], tok, msg);
      }
      if (nAryExpr.Fun is MapSelect)
      {
        var mapExpr = nAryExpr.Args[0];
        if (mapExpr is NAryExpr lheapValExpr &&
            lheapValExpr.Fun is FieldAccess &&
            lheapValExpr.Args[0].Type is CtorType ctorType &&
            Monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Lheap")
        {
          var cmdSeq = CreateAccessAsserts(lheapValExpr.Args[0], tok, msg);
          var lheapContainsFunc = LheapContains(nAryExpr.Type);
          cmdSeq.Add(AssertCmd(tok, ExprHelper.FunctionCall(lheapContainsFunc, lheapValExpr.Args[0], nAryExpr.Args[1]), msg));
          return cmdSeq;
        }
      }
    }
    return new List<Cmd>();
  }

  private List<Cmd> CreateAccessAsserts(AssignLhs assignLhs, IToken tok, string msg)
  {
    if (assignLhs is FieldAssignLhs fieldAssignLhs)
    {
      return CreateAccessAsserts(fieldAssignLhs.Datatype, tok, msg);
    }
    if (assignLhs is MapAssignLhs mapAssignLhs &&
        mapAssignLhs.Map is FieldAssignLhs fieldAssignLhs1 &&
        fieldAssignLhs1.Datatype.Type is CtorType ctorType &&
        Monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Lheap")
    {
      var cmdSeq = CreateAccessAsserts(mapAssignLhs.Map, tok, msg);
      var lheapContainsFunc = LheapContains(mapAssignLhs.Map.Type);
      cmdSeq.Add(AssertCmd(tok, ExprHelper.FunctionCall(lheapContainsFunc, fieldAssignLhs1.Datatype.AsExpr, mapAssignLhs.Indexes[0]), msg));
      return cmdSeq;
    }
    return new List<Cmd>();
  }
}