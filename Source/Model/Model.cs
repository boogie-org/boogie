//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

/*
An instance of the Model class represents a single model returned from the SMT solver. This usually 
corresponds to a single verification error. The model consists of elements and function interpretations.
Additionally the model may contain a number of captured states, each consisting of a user-supplied name
a mapping from Boogie variable names to model elements.

Model elements (which used to be called “partitions” in Z3) are represented by instances of the 
Model.Element class. Each element has an integer identity. The Element class has subclasses
Uninterpreted, Boolean, Integer, BitVector, and Array. The classes correspond to different sorts of 
elements that the SMT solver may use. Each of these has properties for returning the actual 
value (true/false or a number; for bitvectors also size). For an array the interpretation is a
particular function defined elsewhere in the model.

A function interpretation is represented by Model.Func class. It consists of a name, arity, and 
a list of defining tuples. A defining tuple (Model.FuncTuple) for a function of arity N has 
N model elements as arguments and a single element as the result. A constant is a function 
of arity 0, with just one defining tuple. Given a constant function f, the result element of 
the defining tuple is retrieved with f.GetConstant().

The Model.Element class exposes methods to look up all the functions that reference it in their 
defining tuples. Additionally Model.Func allows lookup of specific tuples, based on the elements.

An instance of the Model class represents a single model returned from the SMT solver.
 
 */

using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
  public class Model
  {
    #region Elements and functions (inner classes)
    public enum ElementKind
    {
      Integer,
      Real,
      BitVector,
      Boolean,
      Uninterpreted,
      Array,
      DataValue
    }

    abstract public class Element
    {
      public readonly Model Model;
      internal List<FuncTuple> references = new List<FuncTuple>();
      public readonly int Id;

      public IEnumerable<FuncTuple> References { get { return references; } }
      
      public IEnumerable<FuncTuple> Names { 
        get {
          foreach (var f in references)
            if (f.Result == this) yield return f;
        } 
      }

      protected Element(Model p) 
      { 
        Model = p;
        Id = Model.elements.Count;
      }
      public abstract ElementKind Kind { get; }
      public virtual int AsInt() { throw new NotImplementedException(); }

      public override int GetHashCode() {
        return Id;
      }

      public override bool Equals(object obj) {
        return obj == this;
      }
    }

    #region element kinds
    public class Uninterpreted : Element
    {
      public override ElementKind Kind { get { return ElementKind.Uninterpreted; } }
      public override string ToString() { return Name; }

      internal Uninterpreted(Model p, string n) : base(p) { Name = n; }
      public readonly string Name;
    }

    abstract public class Number : Element
    {
      protected Number(Model p, string n) : base(p) { Numeral = n; }
      public readonly string Numeral;
      public override int AsInt() { return int.Parse(Numeral); }
    }

    public class Integer : Number
    {
      internal Integer(Model p, string n) : base(p, n) { }
      public override ElementKind Kind { get { return ElementKind.Integer; } }
      public override string ToString() { return Numeral.ToString(); }
    }

    public class Real : Number
    {
      internal Real(Model p, string n) : base(p, n) { }
      public override ElementKind Kind { get { return ElementKind.Real; } }
      public override string ToString() { return Numeral.ToString(); }
    }

    public class BitVector : Number
    {
      internal BitVector(Model p, string n, int sz) : base(p, n) { Size = sz; }
      public readonly int Size;
      public override ElementKind Kind { get { return ElementKind.BitVector; } }
      public override string ToString() { return string.Format("{0}bv{1}", Numeral, Size); }
    }

    public class Boolean : Element
    {
      public bool Value;
      internal Boolean(Model p, bool v) : base(p) { Value = v; }
      public override ElementKind Kind { get { return ElementKind.Boolean; } }
      public override string ToString() { return Value ? "true" : "false"; }      
    }

    public class Array : Element
    {
      public Func Value;
      internal Array(Model p, Func v) : base(p) { Value = v; }
      public override ElementKind Kind { get { return ElementKind.Array; } }
      public override string ToString() { return string.Format("as-array[{0}]", Value.Name); }
    }

    public class DatatypeValue : Element 
    {
      public readonly string ConstructorName;
      public readonly Element[] Arguments;
      internal DatatypeValue(Model p, string name, List<Element> args) : base(p) { 
        ConstructorName = name; 
        Arguments = args.ToArray(); 
      }
      public override ElementKind Kind { get { return ElementKind.DataValue; } }
      public override string ToString() {
        StringBuilder builder = new StringBuilder();
        builder.Append("(").Append(ConstructorName);
        foreach (Element arg in Arguments) {
          builder.Append(" ").Append(arg);
        }
        builder.Append(")");
        return builder.ToString();
      }
    }
    #endregion

    public class Func
    {
      public readonly Model Model;
      public readonly string Name;
      public readonly int Arity;
      internal readonly List<FuncTuple> apps = new List<FuncTuple>();
      public IEnumerable<FuncTuple> Apps { get { return apps; } }
      public int AppCount { get { return apps.Count; } }
      private Element @else;

      internal Func(Model p, string n, int a) { Model = p;  Name = n; Arity = a; }

      public override string ToString()
      {
        return string.Format("{0}/{1}", Name, Arity);
      }

      internal void Substitute(Dictionary<Element, Element> mapping) {
        Element e;
        if (@else != null && mapping.TryGetValue(@else, out e))
          @else = e;
        foreach (var ft in apps) {
          if (mapping.TryGetValue(ft.Result, out e)) ft.Result = e;
          for (var i = 0; i < ft.Args.Length; ++i)
            if (mapping.TryGetValue(ft.Args[i], out e)) ft.Args[i] = e;
        }
      }

      public Element Else
      {
        get
        {
          return @else;
        }
        set
        {
          if (@else != null)
            throw new ArgumentException();
          @else = value;
        }
      }

      public void SetConstant(Element res)
      {
        if (Arity != 0 || apps.Count > 0)
          throw new ArgumentException();
        var t = new FuncTuple(this, res, null);
        apps.Add(t);
        res.references.Add(t);
      }

      /// <summary>
      /// Return the first application where the argument at position argIdx is elt.
      /// </summary>
      public FuncTuple AppWithArg(int argIdx, Element elt)
      {
        foreach (var a in AppsWithArg(argIdx, elt))
          return a;
        return null;
      }

      /// <summary>
      /// Return the first application with the result elt.
      /// </summary>
      public FuncTuple AppWithResult(Element elt)
      {
        foreach (var a in AppsWithResult(elt))
          return a;
        return null;
      }

      /// <summary>
      /// Return all applications where the argument at position argIdx is elt.
      /// </summary>
      public IEnumerable<FuncTuple> AppsWithArg(int argIdx, Element elt)
      {
        foreach (var r in elt.References) {
          if (r.Func == this && r.Args[argIdx] == elt)
            yield return r;
        }
      }

      /// <summary>
      /// Return all applications where the argument at position argIdx0 is elt0 and argument at argIdx1 is elt1.
      /// </summary>
      public IEnumerable<FuncTuple> AppsWithArgs(int argIdx0, Element elt0, int argIdx1, Element elt1)
      {
        foreach (var r in elt0.References) {
          if (r.Func == this && r.Args[argIdx0] == elt0 && r.Args[argIdx1] == elt1)
            yield return r;
        }
      }

      /// <summary>
      /// Return all the applications with the result elt.
      /// </summary>
      public IEnumerable<FuncTuple> AppsWithResult(Element elt)
      {
        foreach (var r in elt.References) {
          if (r.Func == this && r.Result == elt)
            yield return r;
        }
      }

      /// <summary>
      /// For a nullary function, return its value.
      /// </summary>
      public Element GetConstant()
      {
        if (Arity != 0)
          throw new ArgumentException();
        if (apps.Count == 0)
          SetConstant(Model.MkElement("**" + Name));
        return apps[0].Result;
      }

      /// <summary>
      /// If all arguments are non-null, and function application for them exists return the value, otherwise return null.
      /// </summary>
      public Element OptEval(params Element[] args)
      {
        if (args.Any(a => a == null)) return null;
        return TryEval(args);
      }

      /// <summary>
      /// Look for function application with given arguments and return its value or null if no such application exists.
      /// </summary>
      public Element TryEval(params Element[] args)
      {
        for (int i = 0; i < args.Length; ++i)
          if(args[i]==null)
            throw new ArgumentException();

        if (apps.Count > 10) {
          var best = apps;
          for (int i = 0; i < args.Length; ++i)
            if (args[i].references.Count < best.Count)
              best = args[i].references;
          if (best != apps) {
            foreach (var tpl in best) {
              bool same = true;
              if (tpl.Func != this)
                continue;
              for (int i = 0; i < args.Length; ++i)
                if (tpl.Args[i] != args[i]) {
                  same = false;
                  break;
                }
              if (same) return tpl.Result;
            }
            return null;
          }
        }

        foreach (var tpl in apps) {
          bool same = true;
          for (int i = 0; i < args.Length; ++i)
            if (tpl.Args[i] != args[i]) {
              same = false;
              break;
            }
          if (same) return tpl.Result;
        }
        return null;
      }

      /// <summary>
      /// Look for function application with a subsequence of given arguments and return its value or null if no such application exists.
      /// </summary>
      public Element TryPartialEval(params Element[] args)
      {
        foreach (var tpl in apps) {
          int j = 0;
          for (int i = 0; i < args.Length; ++i) {
            if (tpl.Args[j] == args[i]) {
              j++;
              if (j == tpl.Args.Length)
                return tpl.Result;
            }
          }
        }
        return null;
      }
 
      /// <summary>
      /// Short for TryEval(args) == (Element)true
      /// </summary>
      public bool IsTrue(params Element[] args)
      {
        var r = TryEval(args) as Boolean;
        return r != null && r.Value;
      }

      /// <summary>
      /// Short for TryEval(args) == (Element)false
      /// </summary>
      public bool IsFalse(params Element[] args)
      {
        var r = TryEval(args) as Boolean;
        return r != null && !r.Value;
      }

      public void AddApp(Element res, params Element[] args)
      {        
        if (Arity == 0)
          SetConstant(res);
        else {
          if (args.Length != Arity)
            throw new ArgumentException();
          var t = new FuncTuple(this, res, (Element[])args.Clone());
          apps.Add(t);
          var u = new HashSet<Element>();
          res.references.Add(t);
          u.Add(res);
          foreach (var a in args)
            if (!u.Contains(a)) {
              u.Add(a);
              a.references.Add(t);
            }
        }
      }
    }

    public class FuncTuple
    {
      static readonly Element[] EmptyArgs = new Element[0];

      // These should be immutable, except when Substituting the entire model
      public readonly Func Func;
      public Element Result; 
      public readonly Element[] Args;

      internal FuncTuple(Func func, Element res, Element[] args)
      {
        if (args == null) Args = EmptyArgs;
        else Args = args;
        Func = func;
        Result = res;
      }

      public override string ToString()
      {
        var res = new StringBuilder();
        res.Append("(").Append(Func.Name);
        for (int i = 0; i < Args.Length; ++i) {
          res.Append(" ").Append(Args[i]);
        }
        res.Append(") -> ").Append(Result);
        return res.ToString();
      }
    }
    #endregion

    private List<Func> functions = new List<Func>();
    private List<Element> elements = new List<Element>();
    private List<CapturedState> states = new List<CapturedState>();
    private Dictionary<string, Func> functionsByName = new Dictionary<string, Func>();
    private Dictionary<string, Element> elementsByName = new Dictionary<string, Element>();

    #region factory methods
    Element ConstructElement(string name)
    {
      if (name.ToLower() == "true") return True;
      if (name.ToLower() == "false") return False;

      if (name.StartsWith("bv") && name.Length > 4 && Char.IsDigit(name[2]))
        name = name.Substring(2);

      if (Char.IsDigit(name[0]) || (name[0] == '-' && name.Length > 1 && Char.IsDigit(name[1]))) {
        int col = name.IndexOf("bv");
        int szi = -1;

        if (name.EndsWith(":int"))
          name = name.Substring(0, name.Length - 4);

        if (col > 0) {          
          if (int.TryParse(name.Substring(col + 2), out szi) && szi > 0) {
            name = name.Substring(0, col);
          } else {
            return null;
          }
        } else if (name.EndsWith("]")) {
          col = name.IndexOf("[");
          if (col > 0 && int.TryParse(name.Substring(col + 1, name.Length - col - 2), out szi) && szi > 0) {
            name = name.Substring(0, col);
          } else {
            return null;
          }
        }

        var allDigits = new Regex(@"^-?[0-9]*$");
        var real = new Regex(@"^-?[0-9]+\.[0-9]+$");
        if (allDigits.IsMatch(name)) {
          if (szi > 0)
            return new BitVector(this, name, szi);
          else
            return new Integer(this, name);
        } else if (real.IsMatch(name)) {
          return new Real(this, name);
        } else {
          return null;
        }
      } else if (name[0] == '*' || name.StartsWith("val!") || name.Contains("!val!")) {
        return new Uninterpreted(this, name);
      } else if (name.StartsWith("as-array[") && name.EndsWith("]")) {
        var fnName = name.Substring(9, name.Length - 10);
        return new Array(this, MkFunc(fnName, 1));
      } else {
        return new DatatypeValue(this, name, new List<Element>());
      }
    }

    public Element TryMkElement(string name)
    {
      Element res;

      if (elementsByName.TryGetValue(name, out res))
        return res;

      var tmp = ConstructElement(name);
      if (tmp == null) return null;

      name = tmp.ToString();
      if (elementsByName.TryGetValue(name, out res))
        return res;

      elementsByName.Add(name, tmp);
      elements.Add(tmp);
      return tmp;
    }

    public Element MkElement(string name)
    {
      Element res = TryMkElement(name);
      if (res == null)
        throw new ArgumentException("invalid element name: '" + name + "'");
      return res;
    }

    public Func MkFunc(string name, int arity)
    {
      Func res;
      if (functionsByName.TryGetValue(name, out res)) {
        if (res.Arity != arity)
          throw new ArgumentException(string.Format("function '{0}' previously created with arity {1}, now trying to recreate with arity {2}", name, res.Arity, arity));
        return res;
      }
      res = new Func(this, name, arity);
      functionsByName.Add(name, res);
      functions.Add(res);
      return res;
    }
    #endregion

    #region state management
    public class CapturedState
    {
      List<string> vars = new List<string>();
      Dictionary<string, Element> valuations = new Dictionary<string, Element>();
      readonly CapturedState previous;
      // AL: Dropping "readonly" for corral
      public /* readonly */ string Name { get; private set; }

      public IEnumerable<string> Variables { get { return vars; } }
      public IEnumerable<string> AllVariables { 
        get {
          if (previous != null)
            return previous.AllVariables.Concat(Variables).Distinct();
          else
            return Variables;
        } 
      }
      public int VariableCount { get { return vars.Count; } }
      public bool HasBinding(string varname)
      {
        return valuations.ContainsKey(varname);
      }
      public Element TryGet(string varname)
      {
        CapturedState curr = this;
        while (curr != null) {
          Element res;
          if (curr.valuations.TryGetValue(varname, out res))
            return res;
          curr = curr.previous;
        }
        return null;
      }

      public void AddBinding(string varname, Element value)
      {
        vars.Add(varname);
        valuations.Add(varname, value);
      }

      // Change name of the state
      public void ChangeName(string newName)
      {
          Name = newName;
      }

      // Change names of variables in this state
      // (Used by corral)
      internal void ChangeVariableNames(Dictionary<string, string> varNameMap)
      {
          var oldVars = vars;
          var oldValuations = valuations;

          vars = new List<string>();
          valuations = new Dictionary<string, Element>();

          foreach (var v in oldVars)
          {
              if (varNameMap.ContainsKey(v)) vars.Add(varNameMap[v]);
              else vars.Add(v);
          }

          foreach (var kvp in oldValuations)
          {
              if (varNameMap.ContainsKey(kvp.Key)) valuations.Add(varNameMap[kvp.Key], kvp.Value);
              else valuations.Add(kvp.Key, kvp.Value);
          }
      }

      internal CapturedState(string name, CapturedState prev)
      {
        Name = name;
        previous = prev;
      }
    }

    public CapturedState MkState(string name)
    {
      var last = states[states.Count - 1];
      var s = new CapturedState(name, last);
      states.Add(s);
      return s;
    }

    // Change names of variables in all captured states
    // (Used by corral)
    public void ChangeVariableNames(Dictionary<string, string> varNameMap)
    {
        foreach (var s in states)
        {
            s.ChangeVariableNames(varNameMap);
        }
    }

    #endregion

    public Model()
    {
      InitialState = new CapturedState("<initial>", null);
      states.Add(InitialState);
      True = new Boolean(this, true);
      elements.Add(True);
      elementsByName.Add("true", True);
      False = new Boolean(this, false);      
      elements.Add(False);
      elementsByName.Add("false", False);
    }

    public IEnumerable<Func> Functions { get { return functions; } }
    public IEnumerable<Element> Elements { get { return elements; } }
    public IEnumerable<CapturedState> States { get { return states; } }
    public readonly Element True, False;
    public readonly CapturedState InitialState;
    public bool ModelHasStatesAlready = false;

    public bool HasFunc(string name)
    {
      return functionsByName.ContainsKey(name);
    }

    public Func TryGetFunc(string name)
    {
      Func res;
      if (functionsByName.TryGetValue(name, out res))
        return res;
      else
        return null;
    }

    public Func GetFunc(string name)
    {
      Func res = TryGetFunc(name);
      if (res == null)
        throw new KeyNotFoundException("function '" + name + "' undefined in the model");
      return res;
    }

    public Func TryGetSkolemFunc(string name)
    {
      return Functions.Where(f => f.Name.StartsWith(name + "!")).FirstOrDefault();
    }

    public Element GetElement(string name)
    {
      Element res;
      if (elementsByName.TryGetValue(name, out res))
        return res;
      else
        throw new KeyNotFoundException("element '" + name + "' undefined in the model");
    }

    public Element MkIntElement(int v)
    {
      return MkElement(v.ToString());
    }

    public void Write(System.IO.TextWriter wr)
    {
      wr.WriteLine("*** MODEL");
      foreach (var f in Functions.OrderBy(f => f.Name)) {
        if (f.Arity == 0) {
          wr.WriteLine("{0} -> {1}", f.Name, f.GetConstant());
        }
      }
      foreach (var f in Functions.OrderBy(f => f.Name)) {
        if (f.Arity != 0) {
          wr.WriteLine("{0} -> {{", f.Name);
          // first, add the entries to a list, so that they can be sorted before printing
          List<Tuple<string, Element>> entries = new List<Tuple<string, Element>>();
          foreach (var app in f.Apps) {
            var args = "";
            foreach (var a in app.Args) {
              args += a + " ";
            }
            entries.Add(new Tuple<string, Element>(args, app.Result));
          }
          foreach (var entry in entries.OrderBy(pair => pair.Item1)) {
            wr.WriteLine("  {0}-> {1}", entry.Item1, entry.Item2);
          }
          if (f.Else != null) {
            wr.WriteLine("  else -> {0}", f.Else);
          }
          wr.WriteLine("}");
        }
      }
      foreach (var s in States) {
        if (s == InitialState && s.VariableCount == 0) {
          continue;
        }
        wr.WriteLine("*** STATE {0}", s.Name);
        foreach (var v in s.Variables.OrderBy(nm => nm)) {
          wr.WriteLine("  {0} -> {1}", v, s.TryGet(v));
        }
        wr.WriteLine("*** END_STATE", s.Name);
      }
      wr.WriteLine("*** END_MODEL");
    }

    public void Substitute(Dictionary<Element, Element> mapping) {
      foreach (var f in functions) f.Substitute(mapping);
    }

    public static List<Model> ParseModels(System.IO.TextReader rd)
    {
      ModelParser p = new ParserZ3();
      p.rd = rd;
      p.Run();
      return p.resModels;
    }
  }
}

