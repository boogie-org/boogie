using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer.Base
{
  public class Provider : ILanguageProvider
  {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m)
    {
      return true;
    }

    IEnumerable<IDisplayNode> GetStateNodes(Model m)
    {
      yield return GenericNodes.Functions(m);
      yield return GenericNodes.Constants(m);
      foreach (var s in m.States)
        yield return new StateNode(s);
    }

    public IEnumerable<IState> GetStates(Model m)
    {
      yield return new TopState("TOP", GetStateNodes(m));
    }

    public IEnumerable<string> SortFields(IEnumerable<string> fields)
    {
      return Namer.DefaultSortFields(fields);
    }
  }

  public class StateNode : DisplayNode
  {
    protected Model.CapturedState state;

    public StateNode(Model.CapturedState s) : base(s.Name)
    {
      state = s;
    }

    public override IEnumerable<string> Aliases
    {
      get { foreach (var v in state.Variables) yield return v; }
    }

    public override bool Expandable { get { return state.VariableCount != 0; } }

    public override IEnumerable<IDisplayNode> Expand()
    {
      foreach (var v in state.Variables) {
        yield return new ElementNode(v, state.TryGet(v));
      }
    }
  }

  public class ElementNode : DisplayNode
  {
    protected Model.Element elt;

    public ElementNode(string name, Model.Element elt) : base(name)
    {
      this.elt = elt;
    }

    public override IEnumerable<string> Aliases
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

  public static class GenericNodes
  {
    public static IDisplayNode Function(Model.Func f)
    {
      return new ContainerNode<Model.FuncTuple>(f.Name, a => new AppNode(a), f.Apps);
    }

    public static IDisplayNode Functions(Model m)
    {
      return new ContainerNode<Model.Func>("Functions", f => f.Arity == 0 ? null : Function(f), m.Functions);
    }

    public static IDisplayNode Constants(Model m)
    {
      return new ContainerNode<Model.Func>("Constants", f => f.Arity != 0 ? null : new AppNode(f.Apps.First()), m.Functions);
    }
  }

  public class AppNode : ElementNode
  {
    protected Model.FuncTuple tupl;

    public AppNode(Model.FuncTuple t)
      : base(t.Func.Name, t.Result)
    {
      tupl = t;
      var sb = new StringBuilder();
      sb.Append(t.Func.Name);
      if (t.Args.Length > 0) {
        sb.Append("(");
        foreach (var a in t.Args)
          sb.Append(a.ToString()).Append(", ");
        sb.Length -= 2;
        sb.Append(")");
      }
      name = new EdgeName(sb.ToString());
    }
  }

}
