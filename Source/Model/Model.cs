//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class Model
  {
    #region Elements and functions (inner classes)
    public enum ElementKind
    {
      Integer,
      BitVector,
      Boolean,
      Uninterpreted
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

      protected Element(Model p) { Model = p; }
      public abstract ElementKind Kind { get; }
      public virtual int AsInt() { throw new NotImplementedException(); }
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
    #endregion

    public class Func
    {
      public readonly Model Model;
      public readonly string Name;
      public readonly int Arity;
      internal readonly List<FuncTuple> apps = new List<FuncTuple>();
      public IEnumerable<FuncTuple> Apps { get { return apps; } }
      public int AppCount { get { return apps.Count; } }

      internal Func(Model p, string n, int a) { Model = p;  Name = n; Arity = a; }

      public void SetConstant(Element res)
      {
        if (Arity != 0 || apps.Count > 0)
          throw new ArgumentException();
        var t = new FuncTuple(this, res, null);
        apps.Add(t);
        res.references.Add(t);
      }

      public FuncTuple AppWithArg(int argIdx, Element elt)
      {
        foreach (var a in AppsWithArg(argIdx, elt))
          return a;
        return null;
      }

      public FuncTuple AppWithResult(Element elt)
      {
        foreach (var a in AppsWithResult(elt))
          return a;
        return null;
      }

      public IEnumerable<FuncTuple> AppsWithArg(int argIdx, Element elt)
      {
        foreach (var r in elt.References) {
          if (r.Func == this && r.Args[argIdx] == elt)
            yield return r;
        }
      }

      public IEnumerable<FuncTuple> AppsWithArgs(int argIdx0, Element elt0, int argIdx1, Element elt1) {
        foreach (var r in elt0.References) {
          if (r.Func == this && r.Args[argIdx0] == elt0 && r.Args[argIdx1] == elt1)
            yield return r;
        }
      }

      public IEnumerable<FuncTuple> AppsWithResult(Element elt)
      {
        foreach (var r in elt.References) {
          if (r.Func == this && r.Result == elt)
            yield return r;
        }
      }

      public Element GetConstant()
      {
        if (Arity != 0)
          throw new ArgumentException();
        if (apps.Count == 0)
          SetConstant(Model.MkElement("**" + Name));
        return apps[0].Result;
      }

      public Element TryEval(params Element[] args)
      {
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

      public bool IsTrue(params Element[] args)
      {
        var r = TryEval(args) as Boolean;
        return r != null && r.Value;
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
      states.Add(InitialState);
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

    public void Write(System.IO.TextWriter wr)
    {
      wr.WriteLine("*** MODEL");
      foreach (var f in Functions)
        if (f.Arity == 0) {
          wr.WriteLine("{0} -> {1}", f.Name, f.GetConstant());
        }
      foreach (var f in Functions)
        if (f.Arity != 0) {
          wr.WriteLine("{0} -> {1}", f.Name, "{");
          foreach (var app in f.Apps) {
            wr.Write("  ");
            foreach (var a in app.Args)
              wr.Write("{0} ", a);
            wr.WriteLine("-> {0}", app.Result);
          }
          wr.WriteLine("}");
        }
      foreach (var s in States) {
        if (s == InitialState && s.VariableCount == 0)
          continue;
        wr.WriteLine("*** STATE {0}", s.Name);
        foreach (var v in s.Variables)
          wr.WriteLine("  {0} -> {1}", v, s.TryGet(v));
        wr.WriteLine("*** END_STATE", s.Name);
      }
      wr.WriteLine("*** END_MODEL");
    }

    class Parser
    {
      internal System.IO.TextReader rd;
      string lastLine = "";
      int lineNo;
      bool v1model = false;
      Dictionary<string, Element> partitionMapping = new Dictionary<string, Element>(); // only used when v1model is true
      internal List<Model> resModels = new List<Model>();
      Model currModel;

      void BadModel(string msg)
      {
        throw new ArgumentException(string.Format("Invalid model: {0}, at line {1} ({2})", msg, lineNo, lastLine));
      }

      static char[] seps = new char[] { ' ' };

      string[] GetWords(string line)
      {
        if (line == null)
          return null;
        var words = line.Split(seps, StringSplitOptions.RemoveEmptyEntries);
        return words;
      }

      string ReadLine()
      {
        var l = rd.ReadLine();
        if (l != null) {
          lineNo++;
          lastLine = l;
        }
        return l;
      }

      Element GetElt(string name)
      {
        Element ret;

        if (v1model) {
          if (!partitionMapping.TryGetValue(name, out ret))
            BadModel("undefined partition " + name);
        } else {
          ret = currModel.TryMkElement(name);
          if (ret == null)
            BadModel("invalid element name " + name);
        }

        return ret;
      }

      void NewModel()
      {
        v1model = false;
        partitionMapping.Clear();
        lastLine = "";
        currModel = new Model();
        resModels.Add(currModel);
      }

      internal void Run()
      {
        for (; ; ) {
          var line = ReadLine();
          if (line == null) break; // end of model, everything fine

          if (line == "Counterexample:" || line == "Z3 error model: " || line == "*** MODEL") {
            NewModel();
            continue;
          }

          if (line.EndsWith(": Invalid.") || line.EndsWith(": Valid.")|| line.StartsWith("labels:"))
            continue;
          if (line == "END_OF_MODEL" || line == "." || line == "*** END_MODEL")
            continue;
          if (line == "partitions:" || line == "function interpretations:") {
            v1model = true;
            continue;
          }

          var words = GetWords(line);
          if (words.Length == 0) continue;
          var lastWord = words[words.Length - 1];

          if (currModel == null)
            BadModel("model begin marker not found");

          if (line.StartsWith("*** STATE ")) {
            var name = line.Substring(10);
            CapturedState cs;
            if (name == "<initial>")
              cs = currModel.InitialState;
            else
              cs = currModel.MkState(name);
            for (; ; ) {
              var tmpline = ReadLine();
              if (tmpline == "*** END_STATE") break;
              var tuple = GetWords(tmpline);
              if (tuple == null) BadModel("EOF in state table");
              if (tuple.Length == 0) continue;
              if (tuple.Length != 3 || tuple[1] != "->") BadModel("invalid state tuple definition");
              cs.AddBinding(tuple[0], GetElt(tuple[2]));
            }
            continue;
          }

          if (v1model && words[0][0] == '*') {
            var partName = words[0];
            var len = words.Length;
            Element elt;
            if (len >= 3 && words[len - 2] == "->") {
              elt = currModel.TryMkElement(lastWord);
              if (elt == null) BadModel("bad parition value " + lastWord);
              len -= 2;
            } else {
              elt = currModel.MkElement(words[0]);
            }
            partitionMapping.Add(partName, elt);
            for (int i = 1; i < len; ++i) {
              var name = words[i];
              if (i == 1 && name[0] == '{')
                name = name.Substring(1);
              if (i == len - 1 && name.EndsWith("}"))
                name = name.Substring(0, name.Length - 1);
              var cnst = currModel.MkFunc(name, 0);
              cnst.SetConstant(elt);
            }

          } else if (words.Length == 3 && words[1] == "->") {
            Func fn = null;
            var funName = words[0];

            if (lastWord == "{") {
              for (; ; ) {
                var tuple = GetWords(ReadLine());
                if (tuple == null) BadModel("EOF in function table");
                if (tuple.Length == 0) continue;
                if (tuple.Length == 1 && tuple[0] == "}") break;
                if (tuple.Length < 3 || tuple[tuple.Length - 2] != "->") BadModel("invalid function tuple definition");
                if (tuple[0] == "else") continue;
                if (fn == null)
                  fn = currModel.MkFunc(funName, tuple.Length - 2);
                var args = new Element[fn.Arity];
                for (int i = 0; i < fn.Arity; ++i)
                  args[i] = GetElt(tuple[i]);
                fn.AddApp(GetElt(tuple[tuple.Length - 1]), args);
              }
            } else {
              fn = currModel.MkFunc(funName, 0);
              fn.SetConstant(GetElt(lastWord));
            }
          } else {
            BadModel("unidentified line");
          }
        }
      }
    }

    public static List<Model> ParseModels(System.IO.TextReader rd)
    {
      var p = new Parser();
      p.rd = rd;
      p.Run();
      return p.resModels;
    }

  }
}
