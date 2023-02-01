using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class LinearRewriter
{
  private static HashSet<string> primitives = new HashSet<string>()
  {
    "Lheap_Empty", "Lheap_Split", "Lheap_Transfer", "Lheap_Read", "Lheap_Write","Lheap_Add", "Lheap_Remove",
    "Lset_Empty", "Lset_Split", "Lset_Transfer",
    "Lval_Split", "Lval_Transfer",
  };

  private Monomorphizer monomorphizer;

  private ConcurrencyOptions options;

  private List<IdentifierExpr> frame;
  
  private int? layerNum;

  public LinearRewriter(ConcurrencyOptions options, Monomorphizer monomorphizer, List<IdentifierExpr> frame, int? layerNum)
  {
    this.monomorphizer = monomorphizer;
    this.options = options;
    this.frame = frame;
    this.layerNum = layerNum;
  }
  
  public static bool IsPrimitive(DeclWithFormals decl)
  {
    return primitives.Contains(decl.Name);
  }
  
  public List<Cmd> RewriteCmdSeq(List<Cmd> cmdSeq)
  {
    var newCmdSeq = new List<Cmd>();
    foreach (var cmd in cmdSeq)
    {
      if (cmd is CallCmd callCmd && IsPrimitive(monomorphizer.GetOriginalDecl(callCmd.Proc)))
      {
        newCmdSeq.AddRange(RewriteCallCmd(callCmd));
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
    switch (monomorphizer.GetOriginalDecl(callCmd.Proc).Name)
    {
      case "Lheap_Empty":
        return RewriteLheapEmpty(callCmd);
      case "Lheap_Split":
        return RewriteLheapSplit(callCmd);
      case "Lheap_Transfer":
        return RewriteLheapTransfer(callCmd);
      case "Lheap_Read":
        return RewriteLheapRead(callCmd);
      case "Lheap_Write":
        return RewriteLheapWrite(callCmd);
      case "Lheap_Add":
        return RewriteLheapAdd(callCmd);
      case "Lheap_Remove":
        return RewriteLheapRemove(callCmd);
      case "Lset_Empty":
        return RewriteLsetEmpty(callCmd);
      case "Lset_Split":
        return RewriteLsetSplit(callCmd);
      case "Lset_Transfer":
        return RewriteLsetTransfer(callCmd);
      case "Lval_Split":
        return RewriteLvalSplit(callCmd);
      case "Lval_Transfer":
        return RewriteLvalTransfer(callCmd);
      default:
        Contract.Assume(false);
        return null;
    }
  }

  private AssertCmd AssertCmd(IToken tok, Expr expr, string msg)
  {
    var assertCmd = CmdHelper.AssertCmd(tok, expr, msg);
    if (layerNum.HasValue)
    {
      assertCmd.Attributes =
        new QKeyValue(Token.NoToken, "layer", new List<object> { layerNum.Value }, assertCmd.Attributes);
    }
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
  
  private List<Cmd> RewriteLheapSplit(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var cmdSeq = new List<Cmd>();
    var k = callCmd.Ins[0];
    var path = callCmd.Ins[1];
    var l = callCmd.Outs[0].Decl;
    
    var mapImpFunc = MapImp(refType);
    var mapIteFunc = MapIte(refType, type);
    var mapConstFunc1 = MapConst(refType, Type.Bool);
    var mapConstFunc2 = MapConst(refType, type);
    var mapDiffFunc = MapDiff(refType);
    
    cmdSeq.Add(AssertCmd(callCmd.tok,
      Expr.Eq(ExprHelper.FunctionCall(mapImpFunc, k, Dom(path)), ExprHelper.FunctionCall(mapConstFunc1, Expr.True)),
      "Lheap_Split failed"));
    
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

  private List<Cmd> RewriteLheapTransfer(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path1 = callCmd.Ins[0];
    var path2 = callCmd.Ins[1];

    var mapOrFunc = MapOr(refType);
    var mapIteFunc = MapIte(refType, type);
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path2),
      ExprHelper.FunctionCall(lheapConstructor,
        ExprHelper.FunctionCall(mapOrFunc, Dom(path2), Dom(path1)),
        ExprHelper.FunctionCall(mapIteFunc, Dom(path2), Val(path2), Val(path1)))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLheapRead(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var path = callCmd.Ins[0];
    var v = callCmd.Outs[0];

    var cmdSeq = CreateAccessAsserts(path, callCmd.tok, "Lheap_Read failed");
    cmdSeq.Add(CmdHelper.AssignCmd(v.Decl, path));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLheapWrite(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var path = callCmd.Ins[0];
    var v = callCmd.Ins[1];
    
    var cmdSeq = CreateAccessAsserts(path, callCmd.tok, "Lheap_Write failed");
    cmdSeq.Add(CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path), v));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> CreateAccessAsserts(Expr expr, IToken tok, string msg)
  {
    if (expr is IdentifierExpr identifierExpr)
    {
      return new List<Cmd>();
    }
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
            monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Lheap")
        {
          var cmdSeq = CreateAccessAsserts(lheapValExpr.Args[0], tok, msg);
          var lheapContainsFunc = LheapContains(nAryExpr.Type);
          cmdSeq.Add(AssertCmd(tok, ExprHelper.FunctionCall(lheapContainsFunc, lheapValExpr.Args[0], nAryExpr.Args[1]), "Lheap_Write failed"));
          return cmdSeq;
        }
      }
    }
    throw new cce.UnreachableException();
  }

  private List<Cmd> RewriteLheapAdd(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var v = callCmd.Ins[1];
    var k = callCmd.Outs[0];
    
    cmdSeq.Add(CmdHelper.HavocCmd(k));
    cmdSeq.Add(CmdHelper.AssumeCmd(Expr.Not(ExprHelper.FunctionCall(new MapSelect(callCmd.tok, 1), Dom(path), k))));
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lheapConstructor,
        ExprHelper.FunctionCall(new MapStore(callCmd.tok, 1), Dom(path), k, Expr.True),
        ExprHelper.FunctionCall(new MapStore(callCmd.tok, 1), Val(path), k, v))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLheapRemove(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);
    
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var v = callCmd.Outs[0];
    
    var lheapContainsFunc = LheapContains(type);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(lheapContainsFunc, path, k), "Lheap_Remove failed"));

    var lheapDerefFunc = LheapDeref(type);
    cmdSeq.Add(CmdHelper.AssignCmd(v.Decl, ExprHelper.FunctionCall(lheapDerefFunc, path, k)));

    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path),
      ExprHelper.FunctionCall(lheapConstructor,
        ExprHelper.FunctionCall(new MapStore(callCmd.tok, 1), Dom(path), k, Expr.False),
        ExprHelper.FunctionCall(new MapStore(callCmd.tok, 1), Val(path), k, Default(type)))));
    
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
    var k = callCmd.Ins[0];
    var path = callCmd.Ins[1];
    
    var mapConstFunc = MapConst(type, Type.Bool);
    var mapImpFunc = MapImp(type);
    cmdSeq.Add(AssertCmd(callCmd.tok,
      Expr.Eq(ExprHelper.FunctionCall(mapImpFunc, Dom(k), Dom(path)), ExprHelper.FunctionCall(mapConstFunc, Expr.True)),
      "Lset_Split failed"));

    var mapDiffFunc = MapDiff(type);
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(path, "dom"),ExprHelper.FunctionCall(mapDiffFunc, Dom(path), Dom(k))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteLsetTransfer(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var path1 = callCmd.Ins[0];
    var path2 = callCmd.Ins[1];

    var mapOrFunc = MapOr(type);
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path2),
      ExprHelper.FunctionCall(lsetConstructor, ExprHelper.FunctionCall(mapOrFunc, Dom(path2), Dom(path1)))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLvalSplit(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var k = callCmd.Ins[0];
    var path = callCmd.Ins[1];
    
    var lsetContainsFunc = LsetContains(type);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(lsetContainsFunc, path, ExprHelper.FieldAccess(k, "val")), "Lval_Split failed"));

    var mapOneFunc = MapOne(type);
    var mapDiffFunc = MapDiff(type);
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.FieldAssignLhs(path, "dom"),
        ExprHelper.FunctionCall(mapDiffFunc, Dom(path), ExprHelper.FunctionCall(mapOneFunc, ExprHelper.FieldAccess(k, "val")))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }
  
  private List<Cmd> RewriteLvalTransfer(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType, out Function lheapConstructor,
      out Function lsetConstructor, out Function lvalConstructor);

    var cmdSeq = new List<Cmd>();
    var l = callCmd.Ins[0];
    var path2 = callCmd.Ins[1];

    var mapOneFunc = MapOne(type);
    var mapOrFunc = MapOr(type);
    cmdSeq.Add(CmdHelper.AssignCmd(
      CmdHelper.ExprToAssignLhs(path2),
      ExprHelper.FunctionCall(lsetConstructor,
        ExprHelper.FunctionCall(mapOrFunc, Dom(path2), ExprHelper.FunctionCall(mapOneFunc, Val(l))))));
    
    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private void GetRelevantInfo(CallCmd callCmd, out Type type, out Type refType, out Function lheapConstructor,
    out Function lsetConstructor, out Function lvalConstructor)
  {
    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    type = instantiation["V"];
    var actualTypeParams = new List<Type>() { instantiation["V"] };
    var refTypeCtorDecl = monomorphizer.InstantiateTypeCtorDecl("Ref", actualTypeParams);
    refType = new CtorType(Token.NoToken, refTypeCtorDecl, new List<Type>());
    var lheapTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lheap", actualTypeParams);
    lheapConstructor = lheapTypeCtorDecl.Constructors[0];
    var lsetTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lset", actualTypeParams);
    lsetConstructor = lsetTypeCtorDecl.Constructors[0];
    var lvalTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lval", actualTypeParams);
    lvalConstructor = lvalTypeCtorDecl.Constructors[0];
  }
  
  private void ResolveAndTypecheck(CoreOptions options, IEnumerable<Absy> absys)
  {
    var rc = new ResolutionContext(null, options);
    absys.Iter(absy => absy.Resolve(rc));
    if (rc.ErrorCount != 0)
    {
      return;
    }
    var tc = new TypecheckingContext(null, options);
    tc.Frame = frame;
    absys.Iter(absy => absy.Typecheck(tc));
  }
}