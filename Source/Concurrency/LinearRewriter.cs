using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

public class LinearRewriter
{
  private CivlTypeChecker civlTypeChecker;

  private LinearTypeChecker linearTypeChecker => civlTypeChecker.linearTypeChecker;

  private Monomorphizer monomorphizer => civlTypeChecker.program.monomorphizer;

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
      case "Tag_New":
      case "Tags_New":
      case "Map_MakeEmpty":
        return [callCmd];
      case "Move":
        return RewriteMove(callCmd);
      case "One_Get":
        return RewriteOneGet(callCmd);
      case "One_Put":
        return RewriteOnePut(callCmd);
      case "Map_Get":
        return RewriteMapGet(callCmd);
      case "Map_Put":
        return RewriteMapPut(callCmd);
      case "Map_Split":
        return RewriteMapSplit(callCmd);
      case "Map_Join":
        return RewriteMapJoin(callCmd);
      case "Path_Load":
        return RewritePathLoad(callCmd);
      case "Path_Store":
        return RewritePathStore(callCmd);
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

  private static Expr Key(Expr path)
  {
    return ExprHelper.FieldAccess(path, "key");
  }

  private static Expr Dom(Expr path)
  {
    return ExprHelper.FieldAccess(path, "dom");
  }

  private static FieldAssignLhs Dom(AssignLhs assignLhs)
  {
    return new FieldAssignLhs(assignLhs, new FieldAccess("dom"));
  }

  private static Expr Val(Expr path)
  {
    return ExprHelper.FieldAccess(path, "val");
  }

  private List<Cmd> RewriteMove(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var u = callCmd.Ins[0];
    var v = callCmd.Ins[1];

    cmdSeq.Add(AssertCmd(callCmd.tok, Expr.Eq(u, v), "Move failed"));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
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
    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(setContainsFunc, Dom(path), l), "One_Get failed"));
    cmdSeq.Add(CmdHelper.AssignCmd(Dom(assignLhs), ExprHelper.FunctionCall(setRemoveFunc, Dom(path), l)));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
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
    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    cmdSeq.Add(CmdHelper.AssignCmd(Dom(assignLhs), ExprHelper.FunctionCall(setAddFunc, Dom(path), l)));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
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
    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(mapContainsFunc, path, k), "Map_Get failed"));
    cmdSeq.Add(CmdHelper.AssignCmd(v.Decl, ExprHelper.FunctionCall(mapAtFunc, path, k)));
    cmdSeq.Add(CmdHelper.AssignCmd(assignLhs, ExprHelper.FunctionCall(mapRemoveFunc, path, k)));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
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
    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    if (k is IdentifierExpr ie && !linearTypeChecker.IsOrdinaryType(ie.Decl.TypedIdent.Type))
    {
      var mapContainsFunc = MapContains(domain, range);
      cmdSeq.Add(new AssumeCmd(Token.NoToken, Expr.Not(ExprHelper.FunctionCall(mapContainsFunc, path, k))));
    }
    cmdSeq.Add(CmdHelper.AssignCmd(assignLhs, ExprHelper.FunctionCall(mapUpdateFunc, path, k, v)));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteMapSplit(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var k = callCmd.Ins[1];
    var l = callCmd.Outs[0];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var domain = instantiation["K"];
    var range = instantiation["V"];
    var isSubsetFunc = SetIsSubset(domain);
    var mapExtractFunc = MapExtract(domain, range);
    var mapExcludeFunc = MapExclude(domain, range);
    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    cmdSeq.Add(AssertCmd(callCmd.tok, ExprHelper.FunctionCall(isSubsetFunc, k, Dom(path)), "Map_Split failed"));
    cmdSeq.Add(CmdHelper.AssignCmd(l.Decl, ExprHelper.FunctionCall(mapExtractFunc, path, k)));
    cmdSeq.Add(CmdHelper.AssignCmd(assignLhs, ExprHelper.FunctionCall(mapExcludeFunc, path, k)));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewriteMapJoin(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var l = callCmd.Ins[1];

    var instantiation = monomorphizer.GetTypeInstantiation(callCmd.Proc);
    var domain = instantiation["K"];
    var range = instantiation["V"];
    var mapUnionFunc = MapUnion(domain, range);
    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    cmdSeq.Add(CmdHelper.AssignCmd(assignLhs, ExprHelper.FunctionCall(mapUnionFunc, path, l)));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewritePathLoad(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var v = callCmd.Outs[0];

    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    cmdSeq.Add(CmdHelper.AssignCmd(v.Decl, path));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> RewritePathStore(CallCmd callCmd)
  {
    var cmdSeq = new List<Cmd>();
    var path = callCmd.Ins[0];
    var v = callCmd.Ins[1];

    var assignLhs = civlTypeChecker.ExprToAssignLhs(path);
    cmdSeq.AddRange(PathAsserts(assignLhs));
    cmdSeq.Add(CmdHelper.AssignCmd(assignLhs, v));

    civlTypeChecker.ResolveAndTypecheck(cmdSeq);
    return cmdSeq;
  }

  private List<Cmd> PathAsserts(AssignLhs assignLhs)
  {
    if (assignLhs is SimpleAssignLhs)
    {
      return [];
    }
    else if (assignLhs is MapAssignLhs mapAssignLhs)
    {
      var map = mapAssignLhs.Map;
      var pathAsserts = PathAsserts(map);
      if (map is FieldAssignLhs fieldAssignLhs)
      {
        var ctorType = (CtorType)fieldAssignLhs.Datatype.Type;
        var typeCtorDecl = Monomorphizer.GetOriginalDecl(ctorType);
        if (typeCtorDecl != null && typeCtorDecl.Name == "Map")
        {
          var instantiation = monomorphizer.GetTypeInstantiation(ctorType.Decl);
          var domain = instantiation[0];
          var range = instantiation[1];
          var mapContainsFunc = MapContains(domain, range);
          var assertExpr = ExprHelper.FunctionCall(mapContainsFunc, fieldAssignLhs.Datatype.AsExpr, mapAssignLhs.Indexes[0]);
          pathAsserts.Add(CmdHelper.AssertCmd(assignLhs.tok, assertExpr, "map lookup failed"));
        }
      }
      return pathAsserts;
    }
    else if (assignLhs is FieldAssignLhs fieldAssignLhs)
    {
      var datatype = fieldAssignLhs.Datatype;
      var pathAsserts = PathAsserts(datatype);
      var datatypeTypeCtorDecl = fieldAssignLhs.FieldAccess.DatatypeTypeCtorDecl;
      if (datatypeTypeCtorDecl.Constructors.Count > 1)
      {
        Expr assertExpr = Expr.False;
        fieldAssignLhs.FieldAccess.Accessors.ForEach(accessor =>
        {
          var constructor = datatypeTypeCtorDecl.Constructors[accessor.ConstructorIndex];
          var condExpr = new NAryExpr(Token.NoToken,
            new IsConstructor(Token.NoToken, datatypeTypeCtorDecl, accessor.ConstructorIndex), [datatype.AsExpr]);
          assertExpr = Expr.Or(assertExpr, condExpr);
        });
        pathAsserts.Add(CmdHelper.AssertCmd(assignLhs.tok, assertExpr, "field lookup failed"));
      }
      return pathAsserts;
    }
    else
    {
      Debug.Assert(false); // unreachable
      return [];
    }
  }
}
