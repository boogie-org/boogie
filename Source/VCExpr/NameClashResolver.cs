//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.IO;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;

// Visitor that establishes unique variable (or constant) names in a VCExpr.
// This is done by adding a counter as suffix if name clashes occur

// TODO: also handle type variables here

namespace Microsoft.Boogie.VCExprAST {
  using TEHelperFuns = Microsoft.Boogie.TypeErasure.HelperFuns;

  public class UniqueNamer : ICloneable {
    public string Spacer = "@@";

    public UniqueNamer() {
      GlobalNames = new Dictionary<Object, string>();
      LocalNames = TEHelperFuns.ToList(new Dictionary<Object/*!*/, string/*!*/>()
                                         as IDictionary<Object/*!*/, string/*!*/>);
      UsedNames = new HashSet<string>();
      CurrentCounters = new Dictionary<string, int>();
      GlobalPlusLocalNames = new Dictionary<Object, string>();
    }

    protected UniqueNamer(UniqueNamer namer) {
      Contract.Requires(namer != null);

      Spacer = namer.Spacer;
      GlobalNames = new Dictionary<Object, string>(namer.GlobalNames);
      LocalNames = new List<IDictionary<Object, string>>();

      foreach (IDictionary<Object/*!*/, string/*!*/>/*!*/ d in namer.LocalNames)
        LocalNames.Add(new Dictionary<Object/*!*/, string/*!*/>(d));

      UsedNames = new HashSet<string>(namer.UsedNames);
      CurrentCounters = new Dictionary<string, int>(namer.CurrentCounters);
      GlobalPlusLocalNames = new Dictionary<Object, string>(namer.GlobalPlusLocalNames);
    }

    public virtual Object Clone() {
      Contract.Ensures(Contract.Result<Object>() != null);
      return new UniqueNamer(this);
    }

    public virtual void Reset()
    {
      GlobalNames.Clear();
      LocalNames.Clear();
      LocalNames.Add(new Dictionary<Object/*!*/, string/*!*/>());
      UsedNames.Clear();
      CurrentCounters.Clear();
      GlobalPlusLocalNames.Clear();
    }

    ////////////////////////////////////////////////////////////////////////////

    private readonly IDictionary<Object/*!*/, string/*!*/>/*!*/ GlobalNames;
    [ContractInvariantMethod]
    void GlobalNamesInvariantMethod() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(GlobalNames));
    }
    private readonly List<IDictionary<Object/*!*/, string/*!*/>/*!*/>/*!*/ LocalNames;
    [ContractInvariantMethod]
    void LocalNamesInvariantMethod() {
      Contract.Invariant(Contract.ForAll(LocalNames, i => i != null && cce.NonNullDictionaryAndValues(i)));
    }

    // dictionary of all names that have already been used
    // (locally or globally)
    private readonly HashSet<string/*!*/>/*!*/ UsedNames;
    [ContractInvariantMethod]
    void UsedNamesInvariantMethod() {
      Contract.Invariant(cce.NonNull(UsedNames));
    }
    private readonly IDictionary<string/*!*/, int/*!*/>/*!*/ CurrentCounters;
    [ContractInvariantMethod]
    void CurrentCountersInvariantMethod() {
      Contract.Invariant(CurrentCounters != null);
    }
    private readonly IDictionary<Object/*!*/, string/*!*/>/*!*/ GlobalPlusLocalNames;
    [ContractInvariantMethod]
    void GlobalPlusLocalNamesInvariantMethod() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(GlobalPlusLocalNames));
    }

    ////////////////////////////////////////////////////////////////////////////

    public void PushScope() {
      LocalNames.Add(new Dictionary<Object/*!*/, string/*!*/>());
    }

    public void PopScope() {
      LocalNames.RemoveAt(LocalNames.Count - 1);
    }

    ////////////////////////////////////////////////////////////////////////////

    private string NextFreeName(Object thingie, string baseName) {
      Contract.Requires(baseName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string/*!*/ candidate;
      int counter;

      if (CurrentCounters.TryGetValue(baseName, out counter)) {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      } else {
        candidate = baseName;
        counter = 0;
      }

      while (UsedNames.Contains(candidate)) {
        candidate = baseName + Spacer + counter;
        counter = counter + 1;
      }

      UsedNames.Add(candidate);
      CurrentCounters[baseName] = counter;
      GlobalPlusLocalNames[thingie] = candidate;
      return candidate;
    }

    // retrieve the name of a thingie; if it does not have a name yet,
    // generate a unique name for it (as close as possible to its inherent
    // name) and register it globally
    public string GetName(Object thingie, string inherentName) {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = this[thingie];

      if (res != null)
        return res;

      // if the object is not yet registered, create a name for it
      res = NextFreeName(thingie, inherentName);
      GlobalNames.Add(thingie, res);

      return res;
    }

    [Pure]
    public string this[Object/*!*/ thingie] {
      get {
        Contract.Requires(thingie != null);

        string res;
        for (int i = LocalNames.Count - 1; i >= 0; --i) {
          if (LocalNames[i].TryGetValue(thingie, out res))
            return res;
        }

        GlobalNames.TryGetValue(thingie, out res);
        return res;
      }
    }

    public string GetLocalName(Object thingie, string inherentName) {
      Contract.Requires(inherentName != null);
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string res = NextFreeName(thingie, inherentName);
      LocalNames[LocalNames.Count - 1][thingie] = res;
      return res;
    }

    public virtual string GetQuotedName(Object thingie, string inherentName)
    {
      return GetName(thingie, inherentName);
    }

    public virtual string GetQuotedLocalName(Object thingie, string inherentName)
    {
      return GetLocalName(thingie, inherentName);
    }

    public virtual string LabelVar(string s) {
      return s;
    }

    public virtual string LabelName(string s) {
      return s;
    }

    public virtual string AbsyLabel(string s) {
      return s;
    }

    public virtual void ResetLabelCount() { }

    public string Lookup(Object thingie) {
      Contract.Requires(thingie != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string name;
      if (GlobalPlusLocalNames.TryGetValue(thingie, out name))
        return name;
      return Spacer + "undefined" + Spacer + thingie.GetHashCode() + Spacer;
    }
  }
}
