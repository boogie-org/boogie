using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
  public class CommutativityHint
  {
    public readonly Function function;
    public readonly AtomicAction firstAction;
    public readonly AtomicAction secondAction;
    public List<Expr> args;

    public CommutativityHint(Function function,
      AtomicAction firstAction, AtomicAction secondAction, List<Expr> args)
    {
      this.function = function;
      this.firstAction = firstAction;
      this.secondAction = secondAction;
      this.args = args;
    }
  }

  public class CommutativityWitness : CommutativityHint
  {
    public readonly Variable witnessedVariable;

    public CommutativityWitness(Function function, Variable witnessedVariable,
      AtomicAction firstAction, AtomicAction secondAction, List<Expr> args)
      : base(function, firstAction, secondAction, args)
    {
      this.witnessedVariable = witnessedVariable;
    }

    public CommutativityWitness(Variable witnessedVariable, CommutativityHint h)
      : this(h.function, witnessedVariable, h.firstAction, h.secondAction, h.args)
    {
    }
  }

  public class CommutativityHints
  {
    private Dictionary<Tuple<AtomicAction, AtomicAction>, List<CommutativityWitness>> witnesses;
    private Dictionary<Tuple<AtomicAction, AtomicAction>, List<CommutativityHint>> lemmas;

    public CommutativityHints()
    {
      witnesses = new Dictionary<Tuple<AtomicAction, AtomicAction>, List<CommutativityWitness>>();
      lemmas = new Dictionary<Tuple<AtomicAction, AtomicAction>, List<CommutativityHint>>();
    }

    private Tuple<AtomicAction, AtomicAction> Key(AtomicAction first, AtomicAction second)
    {
      return Tuple.Create(first, second);
    }

    public void AddWitness(CommutativityWitness witness)
    {
      var key = Key(witness.firstAction, witness.secondAction);
      if (!witnesses.ContainsKey(key))
      {
        witnesses[key] = new List<CommutativityWitness>();
      }

      witnesses[key].Add(witness);
    }

    public void AddLemma(CommutativityHint lemma)
    {
      var key = Key(lemma.firstAction, lemma.secondAction);
      if (!lemmas.ContainsKey(key))
      {
        lemmas[key] = new List<CommutativityHint>();
      }

      lemmas[key].Add(lemma);
    }

    public IEnumerable<CommutativityWitness> GetWitnesses(AtomicAction first, AtomicAction second)
    {
      witnesses.TryGetValue(Key(first, second), out List<CommutativityWitness> list);
      if (list == null) return Enumerable.Empty<CommutativityWitness>();
      return list;
    }

    public IEnumerable<CommutativityHint> GetLemmas(AtomicAction first, AtomicAction second)
    {
      lemmas.TryGetValue(Key(first, second), out List<CommutativityHint> list);
      if (list == null) return Enumerable.Empty<CommutativityHint>();
      return list;
    }
  }

  class CommutativityHintVisitor
  {
    private const string FirstProcInputPrefix = "first_";
    private const string SecondProcInputPrefix = "second_";
    private const string PostStateSuffix = "'";

    private readonly CivlTypeChecker civlTypeChecker;
    public CommutativityHints commutativityHints;

    private AtomicAction firstAction;
    private AtomicAction secondAction;
    private List<Expr> args;

    public CommutativityHintVisitor(CivlTypeChecker civlTypeChecker)
    {
      this.civlTypeChecker = civlTypeChecker;
      commutativityHints = new CommutativityHints();
    }

    public void VisitFunctions()
    {
      foreach (var f in civlTypeChecker.program.Functions)
      {
        VisitFunction(f);
      }
    }

    private void VisitFunction(Function function)
    {
      Debug.Assert(function.OutParams.Count == 1);
      List<CommutativityHint> hints = new List<CommutativityHint>();
      // First we collect all {:commutativity "first_action", "second_action"} attributes
      for (QKeyValue kv = function.Attributes; kv != null; kv = kv.Next)
      {
        if (kv.Key != CivlAttributes.COMMUTATIVITY)
          continue;
        if (kv.Params.Count == 2 &&
            kv.Params[0] is string firstActionName &&
            kv.Params[1] is string secondActionName)
        {
          firstAction = civlTypeChecker.FindAtomicActionOrAbstraction(firstActionName);
          secondAction = civlTypeChecker.FindAtomicActionOrAbstraction(secondActionName);
          if (firstAction == null)
          {
            civlTypeChecker.Error(kv, $"Could not find atomic action {firstActionName}");
          }

          if (secondAction == null)
          {
            civlTypeChecker.Error(kv, $"Could not find atomic action {secondActionName}");
          }

          if (firstAction != null && secondAction != null)
          {
            CheckInParams(function.InParams);
          }

          hints.Add(new CommutativityHint(function, firstAction, secondAction, args));
        }
        else
        {
          civlTypeChecker.Error(kv, "Commutativity attribute expects two action names as parameters");
        }
      }

      // And then we look for either {:witness "globalVar"} or {:lemma}
      for (QKeyValue kv = function.Attributes; kv != null; kv = kv.Next)
      {
        if (kv.Key == CivlAttributes.WITNESS)
        {
          if (kv.Params.Count == 1 &&
              kv.Params[0] is string witnessedVariableName)
          {
            Variable witnessedVariable = civlTypeChecker.GlobalVariables.First(v => v.Name == witnessedVariableName);
            if (witnessedVariable == null)
            {
              civlTypeChecker.Error(kv, $"Could not find shared variable {witnessedVariableName}");
            }
            else if (!function.OutParams[0].TypedIdent.Type.Equals(witnessedVariable.TypedIdent.Type))
            {
              civlTypeChecker.Error(function, "Result type does not match witnessed variable");
            }
            else
            {
              hints.ForEach(h => commutativityHints.AddWitness(new CommutativityWitness(witnessedVariable, h)));
            }
          }
          else
          {
            civlTypeChecker.Error(kv, "Witness attribute expects the name of a global variable as parameter");
          }

          break;
        }
        else if (kv.Key == CivlAttributes.LEMMA)
        {
          if (kv.Params.Count == 0)
          {
            if (!function.OutParams[0].TypedIdent.Type.Equals(Type.Bool))
            {
              civlTypeChecker.Error(function, "Result type of lemma must be bool");
            }
            else
            {
              hints.ForEach(h => commutativityHints.AddLemma(h));
            }
          }
          else
          {
            civlTypeChecker.Error(kv, "Lemma attribute does not expect any parameters");
          }

          break;
        }
      }
    }

    private void CheckInParams(List<Variable> inParams)
    {
      args = new List<Expr>();
      foreach (var param in inParams)
      {
        Expr arg = null;
        if (param.Name.StartsWith(FirstProcInputPrefix, StringComparison.Ordinal))
        {
          arg = CheckLocal(param, firstAction.firstImpl, FirstProcInputPrefix);
        }
        else if (param.Name.StartsWith(SecondProcInputPrefix, StringComparison.Ordinal))
        {
          arg = CheckLocal(param, secondAction.secondImpl, SecondProcInputPrefix);
        }
        else
        {
          arg = CheckGlobal(param);
        }

        args.Add(arg);
      }
    }

    private Expr CheckLocal(Variable param, Implementation impl, string prefix)
    {
      var var = FindVariable(param.Name, param.TypedIdent.Type,
        impl.InParams.Union(impl.OutParams));
      if (var != null)
        return Expr.Ident(var);
      var name = param.Name.Remove(0, prefix.Length);
      civlTypeChecker.Error(param, $"Action {impl.Name} does not have parameter {name}:{param.TypedIdent.Type}");
      return null;
    }

    private Expr CheckGlobal(Variable param)
    {
      bool postState = param.Name.EndsWith(PostStateSuffix, StringComparison.Ordinal);
      var name = param.Name;
      if (postState)
        name = name.Substring(0, name.Length - 1);
      var var = FindVariable(name, param.TypedIdent.Type, civlTypeChecker.GlobalVariables);
      if (var != null)
      {
        if (!postState)
          return ExprHelper.Old(Expr.Ident(var));
        else
          return Expr.Ident(var);
      }

      civlTypeChecker.Error(param, $"No shared variable {name}:{param.TypedIdent.Type}");
      return null;
    }

    private Variable FindVariable(string name, Type type, IEnumerable<Variable> vars)
    {
      return vars.FirstOrDefault(i => i.Name == name && i.TypedIdent.Type.Equals(type));
    }
  }
}