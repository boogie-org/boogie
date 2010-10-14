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
      var vm = new VccModel();
      foreach (var s in m.States) {
        var sn = new StateNode(vm, s);
        vm.states.Add(sn);
      }
      return vm.states;
    }
  }

  class VccModel
  {
    public List<StateNode> states = new List<StateNode>();
    public string GetUserVariableName(string name)
    {
      if (name.StartsWith("L#") || name.StartsWith("P#"))
        return name.Substring(2);
      return null;
    }
  }

  class StateNode : IState
  {
    Model.CapturedState state;
    string name;
    VccModel parent;
    List<VariableNode> vars = new List<VariableNode>();

    public StateNode(VccModel parent, Model.CapturedState s)
    {
      this.parent = parent;
      state = s;

      name = s.Name;
      var idx = name.LastIndexOfAny(new char[] { '\\', '/' });
      if (idx > 0)
        name = name.Substring(idx + 1);

      // var prev = parent.states.Last();

      foreach (var v in state.Variables) {
        var n = parent.GetUserVariableName(v);
        if (n != null){
          var vn = new VariableNode(n, state.TryGet(v));
          vn.realName = n;
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

  public class VariableNode : DisplayNode
  {
    protected Model.Element elt;
    public string realName;
    public bool updatedHere;

    public VariableNode(string name, Model.Element elt) : base(name)
    {
      this.elt = elt;
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
  }

  
}
