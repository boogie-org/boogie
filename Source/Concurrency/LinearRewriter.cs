using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class LinearRewriter
{
  private CivlTypeChecker civlTypeChecker;

  private LinearTypeChecker linearTypeChecker => civlTypeChecker.linearTypeChecker;

  private Monomorphizer monomorphizer => civlTypeChecker.program.monomorphizer;

  private ConcurrencyOptions options => civlTypeChecker.Options;

  public LinearRewriter(CivlTypeChecker civlTypeChecker)
  {
    this.civlTypeChecker = civlTypeChecker;
  }

  public static void Rewrite(CivlTypeChecker civlTypeChecker, Implementation impl)
  {
    if (CivlPrimitives.IsPrimitive(impl)) {
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
      if (cmd is CallCmd callCmd)
      {
        if (CivlPrimitives.IsPrimitive(callCmd.Proc))
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
      case "TaggedLocs_New":
      case "Set_MakeEmpty":
      case "Map_MakeEmpty":
        return new List<Cmd>{callCmd};
      case "Set_Get":
        return RewriteSetGet(callCmd);
      case "Set_Put":
        return RewriteSetPut(callCmd);
      case "One_Get":
        return RewriteOneGet(callCmd);
      case "One_Put":
        return RewriteOnePut(callCmd);
      case "Map_Get":
        return RewriteMapGet(callCmd);
      case "Map_Put":
        return RewriteMapPut(callCmd);
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

  private Function MapRemove(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("Map_Remove", new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function MapExtract(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("Map_Extract", new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function MapExclude(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("Map_Exclude", new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function MapUnion(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("Map_Union", new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function MapUpdate(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("Map_Update", new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function MapAt(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("Map_At", new Dictionary<string, Type>() { { "T", domain }, { "U", range } });
  }

  private Function MapContains(Type domain, Type range)
  {
    return monomorphizer.InstantiateFunction("Map_Contains", new Dictionary<string, Type>() { {"T", domain}, { "U", range } });
  }

  private Function SetIsSubset(Type type)
  {
    return monomorphizer.InstantiateFunction("Set_IsSubset", new Dictionary<string, Type>() { { "T", type } });
  }

  private Function SetIsDisjoint(Type type)
  {
    return monomorphizer.InstantiateFunction("Set_IsDisjoint", new Dictionary<string, Type>() { { "T", type } });
  }

  private Function SetAdd(Type type)
  {
    return monomorphizer.InstantiateFunction("Set_Add", new Dictionary<string, Type>() { { "T", type } });
  }

  private Function SetRemove(Type type)
  {
    return monomorphizer.InstantiateFunction("Set_Remove", new Dictionary<string, Type>() { { "T", type } });
  }

  private Function SetUnion(Type type)
  {
    return monomorphizer.InstantiateFunction("Set_Union", new Dictionary<string, Type>() { { "T", type } });
  }

  private Function SetDifference(Type type)
  {
    return monomorphizer.InstantiateFunction("Set_Difference", new Dictionary<string, Type>() { { "T", type } });
  }

  private Function SetContains(Type type)
  {
    return monomorphizer.InstantiateFunction("Set_Contains", new Dictionary<string, Type>() { { "T", type } });
  }

  private Function OneConstructor(Type type)
  {
    var actualTypeParams = new List<Type>() { type };
    var oneTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("One", actualTypeParams);
    var oneConstructor = oneTypeCtorDecl.Constructors[0];
    return oneConstructor;
  }

  private Function SetConstructor(Type type)
  {
    var actualTypeParams = new List<Type>() { type };
    var setTypeCtorDecl = (DatatypeTypeCtorDecl)monomorphizer.InstantiateTypeCtorDecl("Set", actualTypeParams);
    var setConstructor = setTypeCtorDecl.Constructors[0];
    return setConstructor;
  }

  private static Expr Key(Expr path)
  {
    return ExprHelper.FieldAccess(path, "key");
  }

  private static Expr Dom(Expr path)
  {
    return ExprHelper.FieldAccess(path, "dom");
  }

  private static Expr Val(Expr path)
  {
    return ExprHelper.FieldAccess(path, "val");
  }

  private List<Cmd> RewriteSetGet(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var type = instantiation["K"];
    var isSubsetFunc = SetIsSubset(type);
    var setDifferenceFunc = SetDifference(type);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(isSubsetFunc, l, path), "Set_Get failed"));
    cmdSeq.Add(CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path), ExprHelper.FunctionCall(setDifferenceFunc, path, l)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteSetPut(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var type = instantiation["K"];
    var setUnionFunc = SetUnion(type);
    cmdSeq.Add(CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path), ExprHelper.FunctionCall(setUnionFunc, path, l)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteOneGet(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var type = instantiation["K"];
    var setContainsFunc = SetContains(type);
    var setRemoveFunc = SetRemove(type);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(setContainsFunc, path, l), "One_Get failed"));
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path), ExprHelper.FunctionCall(setRemoveFunc, path, l)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteOnePut(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var type = instantiation["K"];
    var setAddFunc = SetAdd(type);
    cmdSeq.Add(CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path), ExprHelper.FunctionCall(setAddFunc, path, l)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteMapGet(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var v = callCmd.Outs[0];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var domain = instantiation["K"];
    var range = instantiation["V"];
    var mapContainsFunc = MapContains(domain, range);
    var mapRemoveFunc = MapRemove(domain, range);
    var mapAtFunc = MapAt(domain, range);
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(mapContainsFunc, path, k), "Map_Get failed"));
    cmdSeq.Add(CmdHelper.AssignCmd(v.Decl, ExprHelper.FunctionCall(mapAtFunc, path, k)));
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path), ExprHelper.FunctionCall(mapRemoveFunc, path, k)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteMapPut(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var v = callCmd.Ins[2];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var domain = instantiation["K"];
    var range = instantiation["V"];
    var mapUpdateFunc = MapUpdate(domain, range);
    if (k is IdentifierExpr ie && !linearTypeChecker.IsOrdinaryType(ie.Decl.TypedIdent.Type))
    {
      var mapContainsFunc = MapContains(domain, range);
      cmdSeq.Add(new AssumeCmd(Token.NoToken, Expr.Not(ExprHelper.FunctionCall(mapContainsFunc, path, k))));
    }
    cmdSeq.Add(
      CmdHelper.AssignCmd(CmdHelper.ExprToAssignLhs(path), ExprHelper.FunctionCall(mapUpdateFunc, path, k, v)));

    ResolveAndTypecheck(options, cmdSeq);
    return cmdSeq;
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
    absys.ForEach(absy => absy.Typecheck(tc));
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
        if (mapExpr is NAryExpr mapValExpr &&
            mapValExpr.Fun is FieldAccess fa &&
            fa.FieldName == "val" &&
            mapValExpr.Args[0].Type is CtorType ctorType &&
            Monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Map")
        {
          var cmdSeq = CreateAccessAsserts(mapValExpr.Args[0], tok, msg);
          var mapContainsFunc = MapContains(nAryExpr.Args[1].Type, nAryExpr.Type);
          cmdSeq.Add(AssertCmd(tok, ExprHelper.FunctionCall(mapContainsFunc, mapValExpr.Args[0], nAryExpr.Args[1]), msg));
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
        fieldAssignLhs1.FieldAccess.FieldName == "val" &&
        fieldAssignLhs1.Datatype.Type is CtorType ctorType &&
        Monomorphizer.GetOriginalDecl(ctorType.Decl).Name == "Map")
    {
      var cmdSeq = CreateAccessAsserts(mapAssignLhs.Map, tok, msg);
      var mapContainsFunc = MapContains(mapAssignLhs.Indexes[0].Type, mapAssignLhs.Map.Type);
      cmdSeq.Add(AssertCmd(tok, ExprHelper.FunctionCall(mapContainsFunc, fieldAssignLhs1.Datatype.AsExpr, mapAssignLhs.Indexes[0]), msg));
      return cmdSeq;
    }
    return new List<Cmd>();
  }
}
