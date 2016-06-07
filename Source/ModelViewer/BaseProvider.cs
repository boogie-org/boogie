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

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      return new GenericModel(m, opts);
    }
  }

  public class GenericModel : LanguageModel
  {
    List<BaseState> states = new List<BaseState>();

    public GenericModel(Model m, ViewOptions opts)
        : base(m, opts)
    {
      foreach (var s in m.States)
        states.Add(new BaseState(this, s) { Name = s.Name });
      foreach (var s in states)
        this.Flush(s.nodes);
    }

    public override IEnumerable<IState> States
    {
      get { return states; }
    }
  }

  public class BaseState : IState
  {
    internal GenericModel m;
    Model.CapturedState st;

    internal List<IDisplayNode> nodes = new List<IDisplayNode>();
    internal Dictionary<Model.Element, string> niceName = new Dictionary<Model.Element, string>();

    public BaseState(GenericModel m, Model.CapturedState st)
    {
      this.st = st;
      this.m = m;

      foreach (var v in st.AllVariables) {
        var e = st.TryGet(v);
        m.RegisterLocalValue(v, e);
        nodes.Add(new ElementNode(this, v, e));

        niceName[e] = v;
        foreach (var r in e.References) {
          if (r.Args.Length == 1 && r.Args[0] == e) {
            if (!niceName.ContainsKey(e))
              niceName[e] = r.Func.Name + "(" + v + ")";
          }
        }
      }

      nodes.Add(new ContainerNode<Model.Func>("[Functions]", f => f.Arity == 0 ? null : Function(f), m.model.Functions));
      nodes.Add(new ContainerNode<Model.Func>("[Constants]", f => f.Arity != 0 ? null : new AppNode(this, f.Apps.First()), m.model.Functions));
    }

    public virtual SourceViewState ShowSource()
    {
      return null;
    }

    IDisplayNode Function(Model.Func f)
    {
      return new ContainerNode<Model.FuncTuple>(f.Name, a => new AppNode(this, a), f.Apps);
    }

    public virtual string Name { get; set; }

    public virtual IEnumerable<IDisplayNode> Nodes
    {
      get { return nodes; }
    }
  }

  public class ElementNode : DisplayNode
  {
    BaseState st;

    public ElementNode(BaseState st, string name, Model.Element elt) : base(st.m, name, elt) { this.st = st; }

    protected override void ComputeChildren()
    {
      children.Add(new ContainerNode<Model.FuncTuple>(" == ", e => new AppNode(st, e), Element.References.Where(t => t.Result == Element)));
      foreach (var e in Element.References) {
        if (e.Args.Contains(Element))
          children.Add(new AppNode(st, e, x => x == Element ? "*" : st.niceName.GetWithDefault(x, null)));
      }
    }
  }

  public class AppNode : ElementNode
  {
    protected Model.FuncTuple tupl;

    public AppNode(BaseState m, Model.FuncTuple t) : this(m, t, _ => null) { }

    public AppNode(BaseState m, Model.FuncTuple t, Func<Model.Element, string> nameElement)
      : base(m, t.Func.Name, t.Result)
    {
      tupl = t;
      var sb = new StringBuilder();
      sb.Append(t.Func.Name);
      if (t.Args.Length > 0) {
        sb.Append("(");
        for (int i = 0; i < t.Args.Length; ++i) {
          var n = nameElement(t.Args[i]);
          if (n == null)
            sb.AppendFormat("%{0}, ", i);
          else
            sb.AppendFormat("{0}, ", n);
        }
        sb.Length -= 2;
        sb.Append(")");
      }
      name = new EdgeName(m.m, sb.ToString(), t.Args);
    }
  }

}
