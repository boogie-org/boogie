//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class Model
  {
    #region Inner classes
    public enum ElementKind
    {
      Integer,
      BitVector,
      Boolean,
      Uninterpreted
    }

    abstract public class Element
    {
      protected readonly Model parent;
      internal List<FuncTuple> references = new List<FuncTuple>();
      public readonly int Id;

      public IEnumerable<FuncTuple> References { get { return references; } }
      
      public IEnumerable<FuncTuple> Names { 
        get {
          foreach (var f in references)
            if (f.Result == this) yield return f;
        } 
      }

      public IEnumerable<FuncTuple> ArgReferences
      {
        get
        {
          foreach (var f in references) {
            if (f.Result != this)
              yield return f;
            else
              foreach (var r in f.Args)
                if (r == this) { yield return f; break; }
          }
        }
      }

      protected Element(Model p) { parent = p; }
      public abstract ElementKind Kind { get; }
      public virtual int AsInt() { throw new NotImplementedException(); }
    }

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

    public class BitVector : Number
    {
      internal BitVector(Model p, string n, int sz) : base(p, n) { Size = sz; }
      public readonly int Size;
      public override ElementKind Kind { get { return ElementKind.BitVector; } }
      public override string ToString() { return string.Format("{0}:bv{1}", Numeral, Size); }
    }

    public class Boolean : Element
    {
      public bool Value;
      internal Boolean(Model p, bool v) : base(p) { Value = v; }
      public override ElementKind Kind { get { return ElementKind.Boolean; } }
      public override string ToString() { return Value ? "true" : "false"; }      
    }

    public class Func
    {
      private readonly Model Parent;
      public readonly string Name;
      public readonly int Arity;
      internal readonly List<FuncTuple> apps = new List<FuncTuple>();
      public IEnumerable<FuncTuple> Apps { get { return apps; } }

      internal Func(Model p, string n, int a) { Parent = p;  Name = n; Arity = a; }

      public void SetConstant(Element res)
      {
        if (Arity != 0 || apps.Count > 0)
          throw new ArgumentException();
        var t = new FuncTuple(this, res, null);
        apps.Add(t);
        res.references.Add(t);
      }

      public Element GetConstant()
      {
        if (Arity != 0)
          throw new ArgumentException();
        if (apps.Count == 0)
          SetConstant(Parent.MkElement("**" + Name));
        return apps[0].Result;
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

      public readonly Func Func;
      public readonly Element Result;
      public readonly Element[] Args;

      internal FuncTuple(Func func, Element res, Element[] args)
      {
        if (args == null) Args = EmptyArgs;
        else Args = args;
        Func = func;
        Result = res;
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

      if (Char.IsDigit(name[0]) || name[0] == '-') {
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

        for (int i = 1; i < name.Length; ++i)
          if (!Char.IsDigit(name[i]))
            return null;

        if (szi > 0)
          return new BitVector(this, name, szi);
        else
          return new Integer(this, name);
      } else if (name[0] == '*' || name.StartsWith("val!")) {
        return new Uninterpreted(this, name);
      } else {
        return null;
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
      public readonly string Name;

      public IEnumerable<string> Variables { get { return vars; } }
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
    #endregion

    public Model()
    {
      InitialState = new CapturedState("<initial>", null);
      True = new Boolean(this, true);
      False = new Boolean(this, false);
      elements.Add(True);
      elements.Add(False);
      elementsByName.Add("true", True);
      elementsByName.Add("false", False);
    }

    public IEnumerable<Func> Functions { get { return functions; } }
    public IEnumerable<Element> Elements { get { return elements; } }
    public IEnumerable<CapturedState> States { get { return states; } }
    public readonly Element True, False;
    public readonly CapturedState InitialState;

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

    public Element GetElement(string name)
    {
      Element res;
      if (elementsByName.TryGetValue(name, out res))
        return res;
      else
        throw new KeyNotFoundException("element '" + name + "' undefined in the model");
    }
  }
}
