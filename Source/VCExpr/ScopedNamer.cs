using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.VCExprAST
{
  public abstract class ScopedNamer : UniqueNamer
  {
    public string Spacer = "@@";
    protected IDictionary<Object /*!*/, string /*!*/> /*!*/ GlobalNames;

    protected List<IDictionary<Object /*!*/, string /*!*/> /*!*/> /*!*/ LocalNames;

    protected HashSet<string /*!*/> /*!*/ UsedNames;

    protected IDictionary<string /*!*/, int /*!*/> /*!*/ CurrentCounters;

    protected IDictionary<Object /*!*/, string /*!*/> /*!*/ GlobalPlusLocalNames;

    protected ScopedNamer()
    {
      GlobalNames = new Dictionary<Object, string>();
      LocalNames = new() { new Dictionary<object, string>() };
      UsedNames = new HashSet<string>();
      CurrentCounters = new Dictionary<string, int>();
      GlobalPlusLocalNames = new Dictionary<Object, string>();
    }
    
    protected ScopedNamer(ScopedNamer namer)
    {
      Contract.Requires(namer != null);

      Spacer = namer.Spacer;
      GlobalNames = new Dictionary<Object, string>(namer.GlobalNames);
      LocalNames = new List<IDictionary<Object, string>>();

      foreach (IDictionary<Object /*!*/, string /*!*/> /*!*/ d in namer.LocalNames)
      {
        LocalNames.Add(new Dictionary<Object /*!*/, string /*!*/>(d));
      }

      UsedNames = new HashSet<string>(namer.UsedNames);
      CurrentCounters = new Dictionary<string, int>(namer.CurrentCounters);
      GlobalPlusLocalNames = new Dictionary<Object, string>(namer.GlobalPlusLocalNames);
    }

    public virtual void Reset()
    {
      GlobalNames.Clear();
      LocalNames.Clear();
      LocalNames.Add(new Dictionary<Object /*!*/, string /*!*/>());
      UsedNames.Clear();
      CurrentCounters.Clear();
      GlobalPlusLocalNames.Clear();
    }

    public abstract string GetName(object thingie, string name);

    [ContractInvariantMethod]
    private void GlobalNamesInvariantMethod()
    {
      Contract.Invariant(cce.NonNullDictionaryAndValues(GlobalNames));
    }

    [ContractInvariantMethod]
    private void LocalNamesInvariantMethod()
    {
      Contract.Invariant(Contract.ForAll(LocalNames, i => i != null && cce.NonNullDictionaryAndValues(i)));
    }

    [ContractInvariantMethod]
    private void UsedNamesInvariantMethod()
    {
      Contract.Invariant(cce.NonNull(UsedNames));
    }

    [ContractInvariantMethod]
    private void CurrentCountersInvariantMethod()
    {
      Contract.Invariant(CurrentCounters != null);
    }

    [ContractInvariantMethod]
    private void GlobalPlusLocalNamesInvariantMethod()
    {
      Contract.Invariant(cce.NonNullDictionaryAndValues(GlobalPlusLocalNames));
    }

    public void PushScope()
    {
      LocalNames.Add(new Dictionary<Object /*!*/, string /*!*/>());
    }

    public abstract string GetLocalName(object thingie, string name);
    public abstract string GetOriginalName(string newName);
    public abstract UniqueNamer Clone();

    public void PopScope()
    {
      LocalNames.RemoveAt(LocalNames.Count - 1);
    }

    protected string NextFreeName(Object thingie, string baseName)
    {
      Contract.Requires(baseName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string /*!*/ candidate;

      if (CurrentCounters.TryGetValue(baseName, out var counter))
      {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      }
      else
      {
        candidate = baseName;
        counter = 0;
      }

      while (UsedNames.Contains(candidate))
      {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      }

      UsedNames.Add(candidate);
      CurrentCounters[baseName] = counter;
      GlobalPlusLocalNames[thingie] = candidate;
      return candidate;
    }

    [Pure]
    public string this[Object /*!*/ thingie]
    {
      get
      {
        Contract.Requires(thingie != null);

        string res;
        for (int i = LocalNames.Count - 1; i >= 0; --i)
        {
          if (LocalNames[i].TryGetValue(thingie, out res))
          {
            return res;
          }
        }

        GlobalNames.TryGetValue(thingie, out res);
        return res;
      }
    }

    public string Lookup(Object thingie)
    {
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      if (GlobalPlusLocalNames.TryGetValue(thingie, out var name))
      {
        return name;
      }

      return Spacer + "undefined" + Spacer + thingie.GetHashCode() + Spacer;
    }
  }
}