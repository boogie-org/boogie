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

    public IEnumerable<IDisplayNode> GetStates(Model m)
    {
      foreach (var s in m.States)
        yield return new StateNode(s);
    }
  }

  public class StateNode : IDisplayNode
  {
    protected Model.CapturedState state;
    protected string name;

    public StateNode(Model.CapturedState s)
    {
      name = s.Name;
      var idx = name.LastIndexOfAny(new char[] { '\\', '/' });
      if (idx > 0)
        name = name.Substring(idx + 1);
      state = s;
    }

    public virtual string Name
    {
      get { return name; }
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
  
}
