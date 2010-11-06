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

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m)
    {
      return new GenericModel(m);
    }
  }

  public class GenericModel : LanguageModel
  {
    Model m;

    public GenericModel(Model m)
    {
      this.m = m;
    }

    public IDisplayNode Function(Model.Func f)
    {
      return new ContainerNode<Model.FuncTuple>(f.Name, a => new AppNode(this, a), f.Apps);
    }

    IEnumerable<IDisplayNode> GetStateNodes(Model.CapturedState st)
    {
      foreach (var v in st.Variables)
        yield return new ElementNode(this, v, st.TryGet(v));
      yield return new ContainerNode<Model.Func>("[Functions]", f => f.Arity == 0 ? null : Function(f), m.Functions);
      yield return new ContainerNode<Model.Func>("[Constants]", f => f.Arity != 0 ? null : new AppNode(this, f.Apps.First()), m.Functions);
    }

    public override IEnumerable<IState> States
    {
      get {
        foreach (var s in m.States)
          yield return new TopState(s.Name, GetStateNodes(s));
      }
    }
  }
  public class ElementNode : DisplayNode
  {
    public ElementNode(ILanguageSpecificModel p, string name, Model.Element elt) : base(p, name, elt) {}
  }

  public class AppNode : ElementNode
  {
    protected Model.FuncTuple tupl;

    public AppNode(ILanguageSpecificModel m, Model.FuncTuple t)
      : base(m, t.Func.Name, t.Result)
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
