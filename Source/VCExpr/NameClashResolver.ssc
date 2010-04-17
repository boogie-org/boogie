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
using Microsoft.Contracts;
using Microsoft.Basetypes;

// Visitor that establishes unique variable (or constant) names in a VCExpr.
// This is done by adding a counter as suffix if name clashes occur

// TODO: also handle type variables here

namespace Microsoft.Boogie.VCExprAST {
  using TEHelperFuns = Microsoft.Boogie.TypeErasure.HelperFuns;

  public class UniqueNamer : ICloneable {

    public UniqueNamer() {
      GlobalNames = new Dictionary<Object!, string!> ();
      LocalNames = TEHelperFuns.ToList(new Dictionary<Object!, string!> ()
                                         as IDictionary<Object!, string!>);
      UsedNames = new Dictionary<string!, bool> ();
      CurrentCounters = new Dictionary<string!, int> ();
      GlobalPlusLocalNames = new Dictionary<Object!, string!> ();
    }

    private UniqueNamer(UniqueNamer! namer) {
      GlobalNames = new Dictionary<Object!, string!> (namer.GlobalNames);
      
      List<IDictionary<Object!, string!>!>! localNames =
        new List<IDictionary<Object!, string!>!> ();
      LocalNames = localNames;
      
      foreach (IDictionary<Object!, string!>! d in namer.LocalNames)
        localNames.Add(new Dictionary<Object!, string!> (d));

      UsedNames = new Dictionary<string!, bool> (namer.UsedNames);
      CurrentCounters = new Dictionary<string!, int> (namer.CurrentCounters);
      GlobalPlusLocalNames = new Dictionary<Object!, string!>(namer.GlobalPlusLocalNames);
    }

    public Object! Clone() {
      return new UniqueNamer (this);
    }

    ////////////////////////////////////////////////////////////////////////////

    private readonly IDictionary<Object!, string!>! GlobalNames;
    private readonly List<IDictionary<Object!, string!>!>! LocalNames;

    // dictionary of all names that have already been used
    // (locally or globally)
    private readonly IDictionary<string!, bool>! UsedNames;
    private readonly IDictionary<string!, int>! CurrentCounters;
    private readonly IDictionary<Object!, string!>! GlobalPlusLocalNames;

    ////////////////////////////////////////////////////////////////////////////

    public void PushScope() {
      LocalNames.Add(new Dictionary<Object!, string!> ());
    }

    public void PopScope() {
      LocalNames.RemoveAt(LocalNames.Count - 1);
    }    

    ////////////////////////////////////////////////////////////////////////////

    private string! NextFreeName(Object! thingie, string! baseName) {
      string! candidate;
      int counter;

      if (CurrentCounters.TryGetValue(baseName, out counter)) {
        candidate = baseName + "@@" + counter;
        counter = counter + 1;
      } else {
        candidate = baseName;
        counter = 0;
      }

      bool dummy;
      while (UsedNames.TryGetValue(candidate, out dummy)) {
        candidate = baseName + "@@" + counter;
        counter = counter + 1;
      }

      UsedNames.Add(candidate, true);
      CurrentCounters[baseName] = counter;
      GlobalPlusLocalNames[thingie] = candidate;
      return candidate;
    }

    // retrieve the name of a thingie; if it does not have a name yet,
    // generate a unique name for it (as close as possible to its inherent
    // name) and register it globally
    public string! GetName(Object! thingie, string! inherentName) {
      string res = this[thingie];

      if (res != null)
        return res;

      // if the object is not yet registered, create a name for it
      res = NextFreeName(thingie, inherentName);
      GlobalNames.Add(thingie, res);

      return res;
    }

    [Pure]
    public string this[Object! thingie] { get {
      string res;
      for (int i = LocalNames.Count - 1; i >= 0; --i) {
        if (LocalNames[i].TryGetValue(thingie, out res))
          return res;
      }

      GlobalNames.TryGetValue(thingie, out res);
      return res;
    } }

    public string! GetLocalName(Object! thingie, string! inherentName) {
      string! res = NextFreeName(thingie, inherentName);
      LocalNames[LocalNames.Count - 1][thingie] = res;
      return res;
    }
    
    public string! Lookup(Object! thingie) {
      return GlobalPlusLocalNames[thingie];
    }
  }
}
