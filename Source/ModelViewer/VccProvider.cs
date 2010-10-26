using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer.Vcc
{
  public class Provider : ILanguageProvider
  {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m)
    {
      return m.TryGetFunc("$is_ghost_field") != null && m.TryGetFunc("$fk_vol_version") != null;
    }

    public IEnumerable<IState> GetStates(Model m)
    {
      var vm = new VccModel(m);
      foreach (var s in m.States) {
        var sn = new StateNode(vm.states.Count, vm, s);
        vm.states.Add(sn);
      }
      foreach (var s in vm.states) {
        s.CopyNames();
      }
      foreach (var s in vm.states) {
        s.ComputeNames();
      }
      return vm.states;
    }
  }

  enum DataKind
  {
    Flat,
    PhysPtr,
    SpecPtr,
    Map
  }

  class VccModel
  {
    public readonly Model model;
    public readonly Model.Func f_ptr_to, f_phys_ptr_cast, f_spec_ptr_cast, f_mathint, f_local_value_is, f_spec_ptr_to, f_heap, f_select_field,
                               f_select_value, f_field_type, f_int_to_ptr, f_ptr_to_int, f_ptr, f_map_t;
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    public List<StateNode> states = new List<StateNode>();

    public VccModel(Model m)
    {
      model = m;
      f_ptr_to = m.MkFunc("$ptr_to", 1);
      f_spec_ptr_to = m.MkFunc("$spec_ptr_to", 1);
      f_phys_ptr_cast = m.MkFunc("$phys_ptr_cast", 2);
      f_spec_ptr_cast = m.MkFunc("$spec_ptr_cast", 2);
      f_mathint = m.MkFunc("^^mathint", 0);
      f_local_value_is = m.MkFunc("$local_value_is", 5);
      f_heap = m.MkFunc("$heap", 1);
      f_select_field = m.MkFunc("Select_[$field][$ptr]$int", 2);
      f_select_value = m.MkFunc("Select_[$ptr]$int", 2);
      f_field_type = m.MkFunc("$field_type", 1);
      f_int_to_ptr = m.MkFunc("$int_to_ptr", 1);
      f_ptr_to_int = m.MkFunc("$ptr_to_int", 1);
      f_ptr = m.MkFunc("$ptr", 2);
      f_map_t = m.MkFunc("$map_t", 2);
    }

    public string GetUserVariableName(string name)
    {
      if (name.StartsWith("L#") || name.StartsWith("P#"))
        return name.Substring(2);
      return null;
    }

    public Model.Element LocalType(string localName)
    {
      var v = GetUserVariableName(localName);
      if (v == null) v = localName;
      var c = model.TryGetFunc("#loc." + v);
      if (c != null) {
        var localIs = f_local_value_is.AppWithArg(2, c.GetConstant());
        if (localIs != null)
          return localIs.Args[4];
      }
      return f_mathint.GetConstant();
    }

    public Model.Element Image(Model.Element elt, Model.Func f)
    {
      var r = f.AppWithResult(elt);
      if (r != null)
        return r.Args[0];
      return null;
    }

    string TypeNameCore(Model.Element elt)
    {
      var deref = Image(elt, f_ptr_to);
      if (deref != null)
        return TypeName(deref) + "*";
      deref = Image(elt, f_spec_ptr_to);
      if (deref != null)
        return TypeName(deref) + "^";
      var mapt = f_map_t.AppWithResult(elt);
      if (mapt != null)
        return string.Format("{1}[{0}]", TypeName(mapt.Args[0]), TypeName(mapt.Args[1]));

      foreach (var app in elt.Names)
        if (app.Func.Arity == 0 && app.Func.Name.StartsWith("^")) {
          var n = app.Func.Name.Substring(1); 
          switch (n) {
            case "^i1": return "int8_t";
            case "^u1": return "uint8_t";
            case "^i2": return "int16_t";
            case "^u2": return "uint16_t";
            case "^i4": return "int32_t";
            case "^u4": return "uint32_t";
            case "^i8": return "int64_t";
            case "^u8": return "uint64_t";
            case "^bool": return "bool";
            default: return n;
          }          
        }
      return elt.ToString();
    }

    public string TypeName(Model.Element elt)
    {
      string res;
      if (!typeName.TryGetValue(elt, out res)) {
        typeName[elt] = elt.ToString(); // avoid infinite recursion
        res = TypeNameCore(elt);
        typeName[elt] = res;
      }
      return res;
    }

    public static readonly string[] synthethic_fields = new string[] { "$f_owns", "$f_ref_cnt", "$f_vol_version", "$f_root", "$f_group_root" };

    public string ConstantFieldName(Model.Element elt)
    {
      var bestScore = int.MaxValue;
      string bestName = null;

      foreach (var t in elt.Names) {
        var score = int.MaxValue;
        string name = null;
        if (t.Args.Length == 0) {
          name = t.Func.Name;
          score = 0;
          var dotIdx = name.IndexOf('.');
          if (dotIdx > 0) {
            score += 10;
            name = name.Substring(dotIdx + 1);
          }
          if (name.Contains('#')) score -= 1;
        } else if (synthethic_fields.Contains(t.Func.Name)) {
          name = string.Format("{0}<{1}>", t.Func.Name.Substring(3), TypeName(t.Args[0]));
          score = 5;
        }
        if (score < bestScore) {
          bestScore = score;
          bestName = name;
        }
      }

      return bestName;
    }

    public DataKind GetKind(Model.Element tp, out Model.FuncTuple tpl)
    {
      tpl = f_ptr_to.AppWithResult(tp);
      if (tpl != null) return DataKind.PhysPtr;
      tpl = f_spec_ptr_to.AppWithResult(tp);
      if (tpl != null) return DataKind.SpecPtr;
      tpl = f_map_t.AppWithResult(tp);
      if (tpl != null) return DataKind.Map;
      return DataKind.Flat;
    }

    public DataKind GetKind(Model.Element tp)
    {
      Model.FuncTuple dummy;
      return GetKind(tp, out dummy);
    }


    public Model.Element WrapForUse(Model.Element elt, Model.Element tp)
    {
      Model.FuncTuple tpl;
      var kind = GetKind(tp, out tpl);

      if (kind == DataKind.Flat) return elt;

      if (kind == DataKind.Map) {
        if (elt.Kind == Model.ElementKind.Integer) {
          Model.Element theMap = null;
          foreach (var conv in model.Functions)
            // really, we should reconstruct the name of this function, but this is painful
            if (conv.Arity == 1 && conv.Name.StartsWith("$int_to_map_t")) {
              var app = conv.AppWithArg(0, elt);
              if (app != null) {
                theMap = app.Result;          
                break;
              }
            }
          if (theMap == null) return elt;
          return theMap;
        }
        return elt;
      }

      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr) {
        if (elt.Kind == Model.ElementKind.Integer) {
          var tmp = f_int_to_ptr.TryEval(elt);
          if (tmp != null)
            elt = tmp;
        }
      }

      if (kind == DataKind.PhysPtr)
        return Util.OrElse(f_phys_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      if (kind == DataKind.SpecPtr)
        return Util.OrElse(f_spec_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      Util.Assert(false);
      return elt;
    }

    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt, Model.Element tp)
    {
      List<ElementNode> result = new List<ElementNode>();
      Model.FuncTuple tpl;

      var kind = GetKind(tp, out tpl);
      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr) {
        var heap = state.state.TryGet("$s");
        if (heap != null)
          heap = f_heap.TryEval(heap);
        if (heap != null) {
          foreach (var fld in f_select_field.AppsWithArg(0, heap)) {
            var val = f_select_value.TryEval(fld.Result, elt);
            if (val != null) {
              var ftp = f_field_type.TryEval(fld.Args[1]);
              val = WrapForUse(val, ftp);
              var nm = ConstantFieldName(fld.Args[1]);
              var edgname = nm == null ? new EdgeName(fld.Args[1].ToString()) { Score = 100 } : new EdgeName(state.namer, "%(%0->%)" + nm, elt) { Score = 10 };
              result.Add(new FieldNode(state, edgname, val, ftp));
            }
          }
          //result.Sort(CompareFields);
        }
      } else if (kind == DataKind.Map) {
        var elTp = tpl.Args[1];
        foreach (var sel in model.Functions)
          if (sel.Arity == 2 && sel.Name.StartsWith("$select.$map_t")) {
            foreach (var app in sel.AppsWithArg(0, elt)) {
              var val = WrapForUse(app.Result, elTp);
              var edgname = new EdgeName(state.namer, "%(%0%)[%1]", elt, app.Args[1]) { Score = 20 };
              result.Add(new MapletNode(state, edgname, val, elTp));
            }
          }
      }

      return result;
    }
  }

#if false
  class Namer
  {
    VccModel vm;
    Model model { get { return vm.model; } }
    List<StateNode> states { get { return vm.states; } }

    internal Namer(VccModel v) { vm = v; }

    public static readonly string[] synthethic_fields = new string[] { "$f_owns", "$f_ref_cnt", "$f_vol_version", "$f_root", "$f_group_root" };
    Dictionary<Model.Element, List<EltName>> names = new Dictionary<Model.Element, List<EltName>>();
    Dictionary<Model.Element, EltName> bestNameFor = new Dictionary<Model.Element, EltName>();
    List<EltName> resolutionOrder = new List<EltName>();
    Dictionary<Model.Element, string[]> finalNames = new Dictionary<Model.Element, string[]>();


    class EltName
    {
      public Model.Element For;
      public int Score;
      public string Format;
      public Model.Element[] Arguments;
      public string Resolved;
    }

    private void AddName(Model.Element elt, int sc, string fmt, params Model.Element[] args)
    {
      List<EltName> l;
      if (!names.TryGetValue(elt, out l)) {
        l = new List<EltName>();
        names.Add(elt, l);
      }
      l.Add(new EltName() { Arguments = args, Format = fmt, Score = sc, For = elt });
    }

    private void AddAnyName(Model.Element elt)
    {
      if (names.ContainsKey(elt)) return;
      var nm = new EltName() { Arguments = new Model.Element[0], Format = string.Format("<{0}>", elt.ToString()), Score = 50, For = elt };
      var l = new List<EltName>();
      l.Add(nm);
      names[elt] = l;
    }

    private int GetApproxScore(Model.Element e)
    {
      EltName n;
      if (bestNameFor.TryGetValue(e, out n))
        return n.Score;
      return 100;
    }

    private int CompareNames(EltName x, EltName y)
    {
      if (x == y) return 0;
      if (x.Score == y.Score) {
        if (x.Arguments.Length == y.Arguments.Length)
          return x.Arguments.Map(GetApproxScore).Sum() - y.Arguments.Map(GetApproxScore).Sum();
        else
          return x.Arguments.Length - y.Arguments.Length;
      } else {
        return x.Score - y.Score;
      }
    }


    private void WorkOutBestNameFor(Model.Element e)
    {
      if (bestNameFor.ContainsKey(e)) return;
      if (!names.ContainsKey(e)) AddAnyName(e);
      var nm = names[e];
      nm.Sort(CompareNames);
      var best = nm[0];
      bestNameFor[e] = best;
      foreach (var a in best.Arguments)
        WorkOutBestNameFor(a);
      resolutionOrder.Add(best);
    }

    private void ResolveNames()
    {
      var keys = names.Keys.ToArray();
      foreach (var e in keys)
        WorkOutBestNameFor(e);
      var res1 = resolutionOrder.ToArray();
      foreach (var nm in res1) {
        var nms = names[nm.For];
        foreach (var subname in nms.Skip(1)) {
          subname.Arguments.Iter(WorkOutBestNameFor);
          resolutionOrder.Add(subname);
        }
      }

      foreach (var nm in resolutionOrder) {
        var s = nm.Format;
        for (int i = nm.Arguments.Length - 1; i >= 0; --i) {
          var argName = bestNameFor[nm.Arguments[i]];
          var strName = argName.Resolved;
          if (strName == null) strName = argName.For.ToString();
          s = s.Replace("&" + i, strName);
        }
        nm.Resolved = s;
      }

      foreach (var e in names) {
        finalNames[e.Key] = e.Value.Map(n => n.Resolved).ToArray();
      }
    }

    public Dictionary<Model.Element,string[]> ComputeNames()
    {
      ComputeFields();
      ComputeLocals();
      ComputeLiterals();
      ComputeFieldRefs();

      ResolveNames();

      return finalNames;
    }

    private void ComputeFieldRefs()
    {
      var fieldStateId = new Dictionary<Model.Element, int>();
      for (int i = 0; i < states.Count; ++i) {
        var hp = vm.f_heap.TryEval(states[i].state.TryGet("$s"));
        foreach (var fld in vm.f_select_field.AppsWithArg(0, hp)) {
          if (!fieldStateId.ContainsKey(fld.Result)) {
            fieldStateId[fld.Result] = i;
            foreach (var sel in vm.f_select_value.AppsWithArg(0, fld.Result)) {
              var val = sel.Result;
              var ftp = vm.f_field_type.TryEval(fld.Args[1]);
              val = vm.WrapForUse(val, ftp);
              AddName(val, 20, string.Format("&0->&1.{0}", i), sel.Args[1], fld.Args[1]);
            }
          }
        }
      }
    }

    private void ComputeLiterals()
    {
      foreach (var e in model.Elements) {
        Model.Number n = e as Model.Number;
        if (n != null)
          AddName(n, 5, n.ToString());
      }
    }

    private void ComputeLocals()
    {
      var defined = new HashSet<Tuple<Model.Element, string>>();
      for (int i = 0; i < states.Count; ++i) {
        foreach (var v in states[i].vars) {
          var t = Tuple.Create(v.Element, v.Name);
          if (!defined.Contains(t)) {
            defined.Add(t);
            AddName(v.Element, 10, string.Format("{0}.{1}", v.Name, i));
          }
        }
      }
    }

    private void ComputeFields()
    {
      var fields = vm.f_select_field.Apps.Map(a => a.Args[1]).Concat(vm.f_ptr.Apps.Map(a => a.Args[0]));
      foreach (var f in fields) {
        foreach (var fn in synthethic_fields) {
          foreach (var tpl in model.MkFunc(fn, 1).AppsWithResult(f))
            AddName(f, 5, string.Format("{0}<{1}>", fn.Substring(3), vm.TypeName(tpl.Args[0])));
        }
        foreach (var nm in f.Names) {
          if (nm.Func.Arity == 0) {
            var n = nm.Func.Name;
            var idx = n.LastIndexOf('.');
            if (idx > 0) n = n.Substring(idx + 1);
            AddName(f, 5, n);
          }
        }
        AddAnyName(f);
      }
    }

  }
#endif
  
  class StateNode : IState
  {
    internal Model.CapturedState state;
    string name;
    internal VccModel vm;
    internal List<VariableNode> vars;
    internal Namer namer;
    internal int index;
    
    public StateNode(int i, VccModel parent, Model.CapturedState s)
    {
      this.namer = new Namer();
      this.vm = parent;
      state = s;
      index = i;

      name = s.Name;
      var idx = name.LastIndexOfAny(new char[] { '\\', '/' });
      if (idx > 0)
        name = name.Substring(idx + 1);
      var limit = 16;
      if (name.Length > limit) {
        idx = name.IndexOf('(');
        if (idx > 0) {
          var prefLen = limit - (name.Length - idx);
          if (prefLen > 2) {
            name = name.Substring(0,prefLen) + ".." + name.Substring(idx);
          }
        }
      }

      SetupVars();
    }

    void SetupVars()
    {
      if (vars != null) return;
      vars = new List<VariableNode>();

      var names = Util.Empty<string>();

      if (vm.states.Count > 0) {
        var prev = vm.states.Last();
        names = prev.vars.Map(v => v.realName);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names) {
        if (vm.GetUserVariableName(v) != null) {
          var tp = vm.LocalType(v);
          var val = state.TryGet(v);
          val = vm.WrapForUse(val, tp);
          var vn = new VariableNode(this, v, val, tp);
          vn.updatedHere = vm.states.Count > 0 && curVars.ContainsKey(v);
          vars.Add(vn);
        }
      }

      foreach (var e in vm.model.Elements) {
        Model.Number n = e as Model.Number;
        if (n != null)
          namer.AddName(n, new EdgeName(n.ToString()));
      }
    }

    IEnumerable<StateNode> OtherStates()
    {
      var i = index;
      for (var j = i - 1; j >= 0; j--)
        yield return vm.states[j];
      for (var j = i + 1; j < vm.states.Count; j++)
        yield return vm.states[j];
    }

    internal void CopyNames()
    {
      var named = new HashSet<Tuple<string,Model.Element>>();

      foreach (var v in vars) {
        named.Add(Tuple.Create(v.Name.ShortName(), v.Element));
      }

      foreach (var s in OtherStates()) {
        foreach (var v in s.vars) {
          var th = Tuple.Create(v.Name.ShortName(), v.Element);
          if (!named.Contains(th)) {
            named.Add(th);
            namer.AddName(v.Element, new EdgeName(v.Name.ShortName() + "." + s.index) { Score = 30 });
          }
        }
      }
    }

    internal void ComputeNames()
    {
      namer.ComputeNames(vars);
    }

    public string Name
    {
      get { return name; }
    }

    public IEnumerable<IDisplayNode> Nodes
    {
      get {
        return vars; 
      }
    }

  }

  class ElementNode : DisplayNode
  {
    protected StateNode stateNode;
    protected Model.Element elt, tp;
    protected VccModel vm { get { return stateNode.vm; } }
    protected List<ElementNode> children;

    public ElementNode(StateNode st, IEdgeName name, Model.Element elt, Model.Element tp)
      : base(name)
    {
      this.stateNode = st;
      this.tp = tp;
      this.elt = elt;
    }

    public ElementNode(StateNode st, string name, Model.Element elt, Model.Element tp)
      : this(st, new EdgeName(name), elt, tp) { }

    public override Model.Element Element
    {
      get
      {
        return elt;
      }
    }

    protected virtual void DoInitChildren()
    {
      children.AddRange(vm.GetExpansion(stateNode, elt, tp));
    }

    protected void InitChildren()
    {
      if (children == null) {
        children = new List<ElementNode>();
        DoInitChildren();
      }
    }

    public override IEnumerable<string> Values
    {
      get
      {
        Model.Boolean b = this.Element as Model.Boolean;
        if (b != null) {
          yield return b.ToString();
        } else {
          yield return Element.ToString();
          foreach (var edge in stateNode.namer.Aliases(Element))
            if (edge != Name)
              yield return edge.FullName();
        }
      }
    }

    public override string ToolTip
    {
      get
      {
        var sb = new StringBuilder();
        sb.AppendFormat("Type: {0}\n", vm.TypeName(tp));
        int limit = 30;
        foreach (var n in Values){
          sb.AppendFormat("   = {0}\n", n); 
          if (limit-- < 0) {
            sb.Append("...");
            break;
          }
        }
        return sb.ToString();
      }
    }

    public override bool Expandable
    {
      get
      {
        InitChildren();
        return children.Count > 0;
      }
    }

    public override IEnumerable<IDisplayNode> Expand()
    {
      InitChildren();
      return children;
    }
  }

  class FieldNode : ElementNode
  {
    public FieldNode(StateNode par, IEdgeName realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
      /*
      var idx = realName.LastIndexOf('.');
      if (idx > 0)
        name = realName.Substring(idx + 1);
       */
    }
  }

  class MapletNode : ElementNode
  {
    public MapletNode(StateNode par, IEdgeName realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
    }
  }

  class VariableNode : ElementNode
  {
    public bool updatedHere;
    public string realName;

    public VariableNode(StateNode par, string realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
      this.realName = realName;
      name = new EdgeName(vm.GetUserVariableName(realName));
    }

    public override NodeState State
    {
      get
      {
        return base.State | (updatedHere ? NodeState.Changed : NodeState.Normal);
      }
    }
  }
}
