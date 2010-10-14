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
        var sn = new StateNode(vm, s);
        vm.states.Add(sn);
      }
      vm.ComputeNames();
      return vm.states;
    }
  }

  class VccModel
  {
    public readonly Model model;
    public readonly Model.Func f_ptr_to, f_phys_ptr_cast, f_spec_ptr_cast, f_mathint, f_local_value_is, f_spec_ptr_to, f_heap, f_select_field,
                               f_select_value, f_field_type, f_int_to_ptr, f_ptr_to_int, f_ptr;
    Dictionary<Model.Element, string> primaryName = new Dictionary<Model.Element, string>();
    Dictionary<Model.Element, string[]> allNames = new Dictionary<Model.Element, string[]>();
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
    }

    public void ComputeNames()
    {
      var namer = new Namer(this);
      allNames = namer.ComputeNames();
      foreach (var e in allNames)
        primaryName[e.Key] = e.Value[0];
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
      foreach (var app in elt.Names)
        if (app.Func.Arity == 0 && app.Func.Name.StartsWith("^"))
          return app.Func.Name.Substring(1);
      return elt.ToString();
    }

    public string TypeName(Model.Element elt)
    {
      string res;
      if (!primaryName.TryGetValue(elt, out res)) {
        primaryName[elt] = elt.ToString(); // avoid infinite recursion
        res = TypeNameCore(elt);
        primaryName[elt] = res;
      }
      return res;
    }

    public string FieldName(Model.Element elt)
    {
      return primaryName[elt];
    }

    public int CompareFields(ElementNode f1, ElementNode f2)
    {
      var n1 = f1.Name;
      var n2 = f2.Name;
      int s1 = n1.Contains('<') ? 1 : 0;
      int s2 = n2.Contains('<') ? 1 : 0;
      if (s1 == s2)
        return string.CompareOrdinal(n1, n2);
      else
        return s2 - s1;
    }

    public Model.Element WrapForUse(Model.Element elt, Model.Element tp)
    {
      var derefPh = Image(tp, f_ptr_to);
      var derefSp = Image(tp, f_spec_ptr_to);

      if (derefPh == null && derefSp == null)
        return elt;

      Model.Element casted = null;

      if (elt.Kind == Model.ElementKind.Integer) {
        var tmp = f_int_to_ptr.TryEval(elt);
        if (tmp != null)
          elt = tmp;
      }

      if (derefPh != null) {
        casted = f_phys_ptr_cast.TryEval(elt, derefPh);
      } else if (derefSp != null) {
        casted = f_spec_ptr_cast.TryEval(elt, derefSp);
      }

      if (casted != null) return casted;
      return elt;
    }

    public IEnumerable<FieldNode> GetFields(StateNode state, Model.Element elt, Model.Element tp)
    {
      var heap = state.state.TryGet("$s");
      if (heap != null)
        heap = f_heap.TryEval(heap);
      if (heap != null) {
        foreach (var fld in f_select_field.AppsWithArg(0, heap)) {
          var val = f_select_value.TryEval(fld.Result, elt);
          if (val != null) {
            var ftp = f_field_type.TryEval(fld.Args[1]);
            val = WrapForUse(val, ftp);
            yield return new FieldNode(state, FieldName(fld.Args[1]), val, ftp);
          }
        }
      }
    }

    public string[] ElementNames(Model.Element elt)
    {
      string[] res;
      if (allNames.TryGetValue(elt, out res))
        return res;
      return new string[] { elt.ToString() };
    }

  }

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
  
  class StateNode : IState
  {
    internal Model.CapturedState state;
    string name;
    internal VccModel vm;
    internal List<VariableNode> vars;
    
    public StateNode(VccModel parent, Model.CapturedState s)
    {
      this.vm = parent;
      state = s;

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
        names = prev.vars.Map(v => v.EdgeName);
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
    protected string realName;
    protected VccModel vm { get { return stateNode.vm; } }
    protected List<ElementNode> children;

    public ElementNode(StateNode st, string name, Model.Element elt, Model.Element tp)
      : base(name)
    {
      this.stateNode = st;
      this.realName = name;
      this.tp = tp;
      this.elt = elt;
    }

    public override Model.Element Element
    {
      get
      {
        return elt;
      }
    }

    protected virtual void DoInitChildren()
    {
    }

    protected void InitChildren()
    {
      if (children == null) {
        children = new List<ElementNode>();
        DoInitChildren();
      }
    }

    public override string EdgeName
    {
      get
      {
        return this.realName;
      }
    }

    public override IEnumerable<string> Values
    {
      get
      {
        return vm.ElementNames(Element);
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
    public FieldNode(StateNode par, string realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
      /*
      var idx = realName.LastIndexOf('.');
      if (idx > 0)
        name = realName.Substring(idx + 1);
       */
    }

    protected override void DoInitChildren()
    {
      children.AddRange(vm.GetFields(stateNode, elt, tp));
      children.Sort(vm.CompareFields);
    }
  }


  class VariableNode : ElementNode
  {
    public bool updatedHere;

    public VariableNode(StateNode par, string realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
      name = vm.GetUserVariableName(realName);
    }

    protected override void DoInitChildren()
    {
      children.AddRange(vm.GetFields(stateNode, elt, tp));
      children.Sort(vm.CompareFields);
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
