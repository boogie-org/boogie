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
    if (IsPrimitive(impl)) {
      return;
    }
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
      case "Loc_New":
      case "Lmap_Empty":
      case "Lmap_Alloc":
      case "Lmap_Create":
      case "Lmap_Free":
      case "Lmap_Move":
      case "Lmap_Assume":
        return new List<Cmd>{callCmd};
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

  private Function LmapContains(Type keyType, Type valueType)
  {
    return monomorphizer.InstantiateFunction("Lmap_Contains",new Dictionary<string, Type>() { {"K", keyType}, { "V", valueType } });
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

  private List<Cmd> RewriteLsetEmpty(CallCmd callCmd)
  {
    GetRelevantInfo(callCmd, out Type type, out Type refType,
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
    GetRelevantInfo(callCmd, out Type type, out Type refType,
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
    GetRelevantInfo(callCmd, out Type type, out Type refType,
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
    GetRelevantInfo(callCmd, out Type type, out Type refType,
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
    GetRelevantInfo(callCmd, out Type type, out Type refType,
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
    GetRelevantInfo(callCmd, out Type type, out Type refType,
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
    GetRelevantInfo(callCmd, out Type type, out Type refType,
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

  private void GetRelevantInfo(CallCmd callCmd, out Type type, out Type refType,
    out Function lsetConstructor, out Function lvalConstructor)
  {
    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    type = instantiation["V"];
    var actualTypeParams = new List<Type>() { type };
    var refTypeCtorDecl = monomorphizer.InstantiateTypeCtorDecl("Ref", actualTypeParams);
    refType = new CtorType(Token.NoToken, refTypeCtorDecl, new List<Type>());
    var lsetTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lset", actualTypeParams);
    lsetConstructor = lsetTypeCtorDecl.Constructors[0];
    var lvalTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Lval", actualTypeParams);
    lvalConstructor = lvalTypeCtorDecl.Constructors[0];
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
        if (mapExpr is NAryExpr lmapValExpr &&
            lmapValExpr.Fun is FieldAccess &&
            lmapValExpr.Args[0].Type is CtorType ctorType &&
            Monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Lmap")
        {
          var cmdSeq = CreateAccessAsserts(lmapValExpr.Args[0], tok, msg);
          var lmapContainsFunc = LmapContains(nAryExpr.Args[1].Type, nAryExpr.Type);
          cmdSeq.Add(AssertCmd(tok, ExprHelper.FunctionCall(lmapContainsFunc, lmapValExpr.Args[0], nAryExpr.Args[1]), msg));
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
        Monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Lmap")
    {
      var cmdSeq = CreateAccessAsserts(mapAssignLhs.Map, tok, msg);
      var lmapContainsFunc = LmapContains(mapAssignLhs.Indexes[0].Type, mapAssignLhs.Map.Type);
      cmdSeq.Add(AssertCmd(tok, ExprHelper.FunctionCall(lmapContainsFunc, fieldAssignLhs1.Datatype.AsExpr, mapAssignLhs.Indexes[0]), msg));
      return cmdSeq;
    }
    return new List<Cmd>();
  }
}
