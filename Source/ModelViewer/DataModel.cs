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
      get { return "State"; }
    }

    public virtual IEnumerable<string> Values
    {
      get { yield return state.Name; }
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
}
