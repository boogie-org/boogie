using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
  public class Wlp
  {
    /*
     * HoistAsserts computes the weakest liberal precondition (wlp) of the body
     * of impl as a collection of AssertCmd's. As a side effect, all AssertCmd's
     * in any block of impl are removed.
     *
     * HoistAsserts assumes that the body of impl does not contain any loops or
     * calls. The blocks in impl are sorted from entry to exit and processed in
     * reverse order, thus ensuring that a block is processed only once the wlp
     * of all its successors has been computed.
     */

    public static List<AssertCmd> HoistAsserts(Implementation impl, ConcurrencyOptions options)
    {
      return HoistAsserts(impl, new List<AssertCmd>(), options);
    }

    public static List<AssertCmd> HoistAsserts(Implementation impl, List<AssertCmd> postconditions, ConcurrencyOptions options)
    {
      Dictionary<Block, List<AssertCmd>> wlps = new Dictionary<Block, List<AssertCmd>>();
      Graph<Block> dag = Program.GraphFromBlocks(impl.Blocks, false);
      foreach (var block in dag.TopologicalSort())
      {
        if (block.TransferCmd is ReturnCmd)
        {
          var wlp = HoistAsserts(block.Cmds, postconditions, options);
          wlps.Add(block, wlp);
        }
        else if (block.TransferCmd is GotoCmd gotoCmd)
        {
          var wlp =
            HoistAsserts(block.Cmds, gotoCmd.LabelTargets.SelectMany(b => wlps[b]).ToList(), options);
          wlps.Add(block, wlp);
        }
        else
        {
          throw new Cce.UnreachableException();
        }
      }
      return wlps[impl.Blocks[0]].Select(assertCmd => Forall(impl.LocVars.Union(impl.OutParams), assertCmd)).ToList();
    }

    private static List<AssertCmd> HoistAsserts(List<Cmd> cmds, List<AssertCmd> postconditions, ConcurrencyOptions options)
    {
      for (int i = cmds.Count - 1; i >= 0; i--)
      {
        var cmd = cmds[i];
        if (cmd is AssertCmd assertCmd)
        {
          postconditions.Add(assertCmd);
        } 
        else if (cmd is AssumeCmd assumeCmd)
        {
          QKeyValue Append(QKeyValue assumeAttributes, QKeyValue assertAttributes)
          {
            if (assumeAttributes == null)
            {
              return assertAttributes;
            }
            return new QKeyValue(assumeAttributes.tok, assumeAttributes.Key, assumeAttributes.Params, Append(assumeAttributes.Next, assertAttributes));
          }
          postconditions = postconditions
            .Select(assertCmd => new AssertCmd(assertCmd.tok, Expr.Imp(assumeCmd.Expr, assertCmd.Expr), Append(assumeCmd.Attributes, assertCmd.Attributes)))
            .ToList();
        }
        else if (cmd is AssignCmd assignCmd)
        {
          var varToExpr = new Dictionary<Variable, Expr>();
          var simpleAssignCmd = assignCmd.AsSimpleAssignCmd;
          for (var j = 0; j < simpleAssignCmd.Lhss.Count; j++)
          {
            var lhs = simpleAssignCmd.Lhss[j];
            var rhs = simpleAssignCmd.Rhss[j];
            varToExpr.Add(lhs.DeepAssignedVariable, rhs);
          }
          postconditions = postconditions.Select(assertCmd =>
            new AssertCmd(assertCmd.tok, SubstitutionHelper.Apply(varToExpr, assertCmd.Expr), Substitute(assertCmd.Attributes, varToExpr))).ToList();
        }
        else if (cmd is HavocCmd havocCmd)
        {
          postconditions = postconditions.Select(assertCmd => Forall(havocCmd.Vars.Select(ie => ie.Decl), assertCmd)).ToList();
        }
        else if (cmd is UnpackCmd unpackCmd)
        {
          var desugaredCmd = (StateCmd) unpackCmd.GetDesugaring(options);
          postconditions = HoistAsserts(desugaredCmd.Cmds, postconditions, options); // removes precondition assert from desugaredCmd.Cmds
        }
        else
        {
          throw new Cce.UnreachableException();
        }
      }
      cmds.RemoveAll(cmd => cmd is AssertCmd);
      return postconditions;
    }

    private static QKeyValue Substitute(QKeyValue kv, Dictionary<Variable, Expr> always)
    {
      if (kv == null)
      {
        return null;
      }
      var newKv = Substitute(kv.Next, always);
      if (kv.Key != "add_to_pool")
      {
        return new QKeyValue(kv.tok, kv.Key, kv.Params, newKv);
      }
      return new QKeyValue(
        kv.tok,
        kv.Key,
        kv.Params.Select(param => param is Expr expr ? SubstitutionHelper.Apply(always, expr) : param).ToList(),
        newKv);
    }

    private static AssertCmd Forall(IEnumerable<Variable> vars, AssertCmd assertCmd)
    {
      bool KeepExpr(Expr expr)
      {
        var freeObjects = new GSet<object>();
        expr.ComputeFreeVariables(freeObjects);
        return freeObjects.OfType<Variable>().Intersect(vars).Count() == 0;
      }

      QKeyValue FilterAttributes(QKeyValue kv)
      {
        if (kv == null)
        {
          return null;
        }
        var newKv = FilterAttributes(kv.Next);
        if (kv.Key != "add_to_pool")
        {
          return new QKeyValue(kv.tok, kv.Key, kv.Params, newKv);
        }
        var newParams = kv.Params.Where(param => param is not Expr expr || KeepExpr(expr)).ToList();
        if (newParams.All(param => param is not Expr))
        {
          return newKv;
        }
        return new QKeyValue(kv.tok, kv.Key, newParams, newKv);
      }

      Expr ForallExpr(IEnumerable<Variable> vars, Expr expr)
      {
        var freeObjects = new GSet<object>();
        expr.ComputeFreeVariables(freeObjects);
        var quantifiedVars = freeObjects.OfType<Variable>().Intersect(vars);
        if (quantifiedVars.Count() == 0)
        {
          return expr;
        }
        else
        {
          var varMapping = quantifiedVars.ToDictionary(v => v,
            v => (Variable)VarHelper.BoundVariable(v.Name, v.TypedIdent.Type, v.Attributes));
          return ExprHelper.ForallExpr(varMapping.Values.ToList(), SubstitutionHelper.Apply(varMapping, expr));
        }
      }

      return new AssertCmd(assertCmd.tok, ForallExpr(vars, assertCmd.Expr), FilterAttributes(assertCmd.Attributes));
    }
  }
}