using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie;

/*
// An idempotent semiring interface
abstract public class Weight {
   abstract public Weight! one();
   abstract public Weight! zero();
   abstract public Weight! extend(Weight! w1, Weight! w2);
   abstract public Weight! combine(Weight! w1, Weight! w2);
   abstract public Weight! isEqual(Weight! w);
   abstract public Weight! projectLocals()
}
*/

// Weight domain for LiveVariableAnalysis (Gen/Kill)
public class GenKillWeight
{
  // lambda S. (S - kill) union gen
  HashSet<Variable>
    gen;

  HashSet<Variable>
    kill;

  [ContractInvariantMethod]
  void ObjectInvariant()
  {
    Contract.Invariant(Cce.NonNullElements(gen));
    Contract.Invariant(Cce.NonNullElements(kill));
    Contract.Invariant(oneWeight != null);
    Contract.Invariant(zeroWeight != null);
  }

  bool isZero;

  public static GenKillWeight
    oneWeight = new GenKillWeight(new HashSet<Variable>(), new HashSet<Variable>());

  public static GenKillWeight
    zeroWeight = new GenKillWeight();

  // initializes to zero
  public GenKillWeight()
  {
    this.isZero = true;
    this.gen = new HashSet<Variable>();
    this.kill = new HashSet<Variable>();
  }

  public GenKillWeight(HashSet<Variable> gen, HashSet<Variable> kill)
  {
    Contract.Requires(Cce.NonNullElements(gen));
    Contract.Requires(Cce.NonNullElements(kill));
    Contract.Assert(gen != null);
    Contract.Assert(kill != null);
    this.gen = gen;
    this.kill = kill;
    this.isZero = false;
  }

  public static GenKillWeight one()
  {
    Contract.Ensures(Contract.Result<GenKillWeight>() != null);
    return oneWeight;
  }

  public static GenKillWeight zero()
  {
    Contract.Ensures(Contract.Result<GenKillWeight>() != null);
    return zeroWeight;
  }

  public static GenKillWeight extend(GenKillWeight w1, GenKillWeight w2)
  {
    Contract.Requires(w2 != null);
    Contract.Requires(w1 != null);
    Contract.Ensures(Contract.Result<GenKillWeight>() != null);
    if (w1.isZero || w2.isZero)
    {
      return zero();
    }

    HashSet<Variable> t = new HashSet<Variable>(w2.gen);
    t.ExceptWith(w1.kill);
    HashSet<Variable> g = new HashSet<Variable>(w1.gen);
    g.UnionWith(t);
    HashSet<Variable> k = new HashSet<Variable>(w1.kill);
    k.UnionWith(w2.kill);
    return new GenKillWeight(g, k);
    //return new GenKillWeight(w1.gen.Union(w2.gen.Difference(w1.kill)), w1.kill.Union(w2.kill));
  }

  public static GenKillWeight combine(GenKillWeight w1, GenKillWeight w2)
  {
    Contract.Requires(w2 != null);
    Contract.Requires(w1 != null);
    Contract.Ensures(Contract.Result<GenKillWeight>() != null);
    if (w1.isZero)
    {
      return w2;
    }

    if (w2.isZero)
    {
      return w1;
    }

    HashSet<Variable> g = new HashSet<Variable>(w1.gen);
    g.UnionWith(w2.gen);
    HashSet<Variable> k = new HashSet<Variable>(w1.kill);
    k.IntersectWith(w2.kill);
    return new GenKillWeight(g, k);
    //return new GenKillWeight(w1.gen.Union(w2.gen), w1.kill.Intersection(w2.kill));
  }

  public static GenKillWeight projectLocals(GenKillWeight w)
  {
    Contract.Requires(w != null);
    Contract.Ensures(Contract.Result<GenKillWeight>() != null);
    HashSet<Variable> gen = new HashSet<Variable>();
    foreach (Variable v in w.gen)
    {
      if (isGlobal(v))
      {
        gen.Add(v);
      }
    }

    HashSet<Variable> kill = new HashSet<Variable>();
    foreach (Variable v in w.kill)
    {
      if (isGlobal(v))
      {
        kill.Add(v);
      }
    }

    return new GenKillWeight(gen, kill);
  }

  public static bool isEqual(GenKillWeight w1, GenKillWeight w2)
  {
    Contract.Requires(w2 != null);
    Contract.Requires(w1 != null);
    if (w1.isZero)
    {
      return w2.isZero;
    }

    if (w2.isZero)
    {
      return w1.isZero;
    }

    return (w1.gen.Equals(w2.gen) && w1.kill.Equals(w2.kill));
  }

  private static bool isGlobal(Variable v)
  {
    Contract.Requires(v != null);
    return (v is GlobalVariable);
  }

  [Pure]
  public override string ToString()
  {
    Contract.Ensures(Contract.Result<string>() != null);
    return string.Format("({0},{1})", gen.ToString(), kill.ToString());
  }

  public HashSet<Variable> getLiveVars()
  {
    Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
    return gen;
  }

  public HashSet<Variable> getLiveVars(HashSet<Variable> lv)
  {
    Contract.Requires(Cce.NonNullElements(lv));
    Contract.Ensures(Cce.NonNullElements(Contract.Result<HashSet<Variable>>()));
    HashSet<Variable> temp = new HashSet<Variable>(lv);
    temp.ExceptWith(kill);
    temp.UnionWith(gen);
    return temp;
  }
}