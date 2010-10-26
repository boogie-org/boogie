using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  public interface ILanguageProvider
  {
    bool IsMyModel(Model m);
    IEnumerable<IState> GetStates(Model m);
  }

  [Flags]
  public enum NodeState
  {
    Normal = 0,
    Changed = 1
  }

  public interface IEdgeName
  {
    int CompareTo(IEdgeName other);
    string FullName();
    string ShortName();
    IEnumerable<Model.Element> Dependencies { get; }
    int Score { get; }
  }

  public interface IDisplayNode
  {
    /// <summary>
    ///  Used for indexing the state tree.
    /// </summary>
    IEdgeName Name { get; }

    /// <summary>
    /// Used to determine aliasing. Can be null.
    /// </summary>
    Model.Element Element { get; }

    bool Expandable { get; }
    IEnumerable<IDisplayNode> Expand();

    // Things displayed to the user.
    NodeState State { get; }
    string CanonicalValue { get; }
    IEnumerable<string> Aliases { get; }
    string ToolTip { get; }

    object ViewSync { get; set; }
  }

  public interface IState
  {
    string Name { get; }
    IEnumerable<IDisplayNode> Nodes { get; }
  }


  public class TopState : IState
  {
    protected IDisplayNode[] children;
    protected string name;

    public TopState(string name, IEnumerable<IDisplayNode> nodes)
    {
      this.name = name;
      children = nodes.ToArray();
    }

    public string Name
    {
      get { return name; }
    }

    public IEnumerable<IDisplayNode> Nodes
    {
      get { return children; }
    }
  }
  
  public abstract class DisplayNode : IDisplayNode
  {
    protected IEdgeName name;

    public DisplayNode(string n)
    { 
      name = new EdgeName(n);
    }

    public DisplayNode(IEdgeName n)
    {
      name = n;
    }

    public virtual string CanonicalValue
    {
      get { return name.FullName(); }
    }

    public virtual IEnumerable<string> Aliases
    {
      get { yield break; }
    }

    public virtual string ToolTip
    {
      get { return null; }
    }

    public virtual bool Expandable
    {
      get { return false; }
    }

    public virtual IEnumerable<IDisplayNode> Expand()
    {
      yield break;
    }

    public virtual NodeState State { get { return NodeState.Normal; } }

    public object ViewSync { get; set; }

    public virtual IEdgeName Name
    {
      get { return name; }
    }

    public virtual Model.Element Element
    {
      get { return null; }
    }
  }

  public class ContainerNode<T> : DisplayNode
  {
    protected Func<T, IDisplayNode> convert;
    protected IEnumerable<T> data;

    public ContainerNode(IEdgeName name, Func<T, IDisplayNode> convert, IEnumerable<T> data) : base(name)
    {
      this.convert = convert;
      this.data = data;
    }

    public ContainerNode(string name, Func<T, IDisplayNode> convert, IEnumerable<T> data)
      : this(new EdgeName(name), convert, data)
    {
    }

    public override bool Expandable { get { return true; } }
    public override IEnumerable<IDisplayNode> Expand()
    {
      foreach (var f in data) {
        var res = convert(f);
        if (res != null)
          yield return res;
      }
    }
  }


  public static class Util
  {
    public static void Assert(bool cond)
    {
      if (!cond) throw new System.Exception("assertion violation");
    }

    public static IEnumerable<T> Empty<T>() { yield break; }

    public static IEnumerable<T> Singleton<T>(T e) { yield return e; }

    public static IEnumerable<T> Concat1<T>(this IEnumerable<T> s, T e) { return s.Concat(Singleton(e)); }

    public static IEnumerable<T> Map<S, T>(this IEnumerable<S> inp, Func<S, T> conv)
    {
      foreach (var s in inp) yield return conv(s);
    }

    public static void Iter<T>(this IEnumerable<T> inp, Action<T> fn)
    {
      foreach (var s in inp) fn(s);
    }

    public static T OrElse<T>(T a, T b)
      where T : class
    {
      if (a != null) return a;
      return b;
    }
  }

}
