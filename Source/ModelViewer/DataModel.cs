using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  public interface IDisplayNode
  {
    string Name { get; }
    IEnumerable<string> Values { get; }
    bool Expandable { get; }
    IEnumerable<IDisplayNode> Expand();
    object ViewSync { get; set; }
  }

  public class StateNode : IDisplayNode
  {
    protected Model.CapturedState state;

    public StateNode(Model.CapturedState s)
    {
      state = s;
    }

    public virtual string Name
    {
      get { return state.Name; }
    }

    public virtual IEnumerable<string> Values
    {
      get { foreach (var v in state.Variables) yield return v; }
    }

    public virtual bool Expandable { get { return state.VariableCount != 0; } }

    public virtual IEnumerable<IDisplayNode> Expand()
    {
      foreach (var v in state.Variables) {
        yield return new ElementNode(v, state.TryGet(v));
      }
    }

    public object ViewSync { get; set; }
  }

  public class ElementNode : IDisplayNode
  {
    protected Model.Element elt;
    protected string name;

    public ElementNode(string name, Model.Element elt)
    {
      this.name = name;
      this.elt = elt;
    }

    public virtual string Name
    {
      get { return name; }
    }

    public virtual IEnumerable<string> Values
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

    public virtual bool Expandable { get { return false; } }
    public virtual IEnumerable<IDisplayNode> Expand() { yield break; }

    public object ViewSync { get; set; }
  }


  public class ContainerNode<T> : IDisplayNode
  {
    protected string name;
    protected Func<T, IDisplayNode> convert;
    protected IEnumerable<T> data;

    public ContainerNode(string name, Func<T, IDisplayNode> convert, IEnumerable<T> data)
    {
      this.name = name;
      this.convert = convert;
      this.data = data;
    }

    public virtual string Name
    {
      get { return name; }
    }

    public virtual IEnumerable<string> Values
    {
      get { yield break; }
    }

    public virtual bool Expandable { get { return true; } }

    public virtual IEnumerable<IDisplayNode> Expand()
    {
      foreach (var f in data) {
        var res = convert(f);
        if (res != null)
          yield return res;
      }
    }

    public object ViewSync { get; set; }
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
      name = sb.ToString();
    }
  }

}
