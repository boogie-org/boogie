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
      return vm.states;
    }
  }

  class VccModel
  {
    public readonly Model model;
    public readonly Model.Func f_ptr_to, f_phys_ptr_cast, f_spec_ptr_cast, f_mathint, f_local_value_is, f_spec_ptr_to, f_heap, f_select_field, f_select_value, f_field_type;

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
    }

    public List<StateNode> states = new List<StateNode>();
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

    public string ConstantName(Model.Element elt)
    {
      foreach (var n in elt.Names) {
        if (n.Func.Arity == 0)
          return n.Func.Name;
      }
      return "<unknown>";
    }

    public IEnumerable<FieldNode> GetFields(StateNode state, Model.Element elt, Model.Element tp)
    {
      var deref = Image(tp, f_ptr_to);
      Model.Element casted = null;

      if (deref != null) {
        casted = f_phys_ptr_cast.TryEval(elt, deref);
      } else {
        deref = Image(tp, f_spec_ptr_to);
        if (deref != null)
          casted = f_spec_ptr_cast.TryEval(elt, deref);
      }

      if (deref != null && casted == null)
        casted = elt;

      if (casted != null) {
        var heap = state.state.TryGet("$s");
        if (heap != null)
          heap = f_heap.TryEval(heap);
        if (heap != null) {
          foreach (var fld in f_select_field.AppsWithArg(0, heap)) {
            var val = f_select_value.TryEval(fld.Result, casted);
            if (val != null) {
              yield return new FieldNode(state, ConstantName(fld.Args[1]), val, f_field_type.TryEval(fld.Args[1]));
            }
          }
        }
      }
    }
  }

  class StateNode : IState
  {
    internal Model.CapturedState state;
    string name;
    internal VccModel vm;
    List<VariableNode> vars = new List<VariableNode>();

    public StateNode(VccModel parent, Model.CapturedState s)
    {
      this.vm = parent;
      state = s;

      name = s.Name;
      var idx = name.LastIndexOfAny(new char[] { '\\', '/' });
      if (idx > 0)
        name = name.Substring(idx + 1);

      var names = Util.Empty<string>();

      if (parent.states.Count > 0) {
        var prev = parent.states.Last();
        names = prev.vars.Map(v => v.EdgeName);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names) {
        if (parent.GetUserVariableName(v) != null) {
          var vn = new VariableNode(this, v, state.TryGet(v));
          vn.updatedHere = parent.states.Count > 0 && curVars.ContainsKey(v);
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
      get { return vars; }
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
        if (!(elt is Model.Uninterpreted))
          yield return elt.ToString();
        foreach (var tupl in elt.Names) {
          if (tupl.Func.Arity == 0)
            yield return tupl.Func.Name;
        }
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
      var idx = realName.LastIndexOf('.');
      if (idx > 0)
        name = realName.Substring(idx + 1);
    }

    protected override void DoInitChildren()
    {
      children.AddRange(vm.GetFields(stateNode, elt, tp));
    }
  }


  class VariableNode : ElementNode
  {
    public bool updatedHere;

    public VariableNode(StateNode par, string realName, Model.Element elt)
      : base(par, realName, elt, par.vm.LocalType(realName))
    {
      name = vm.GetUserVariableName(realName);
    }

    protected override void DoInitChildren()
    {
      children.AddRange(vm.GetFields(stateNode, elt, tp));
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
