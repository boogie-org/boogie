using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  [Flags]
  public enum NodeState
  {
    Normal = 0,
    Changed = 1
  }

  public interface IDisplayNode
  {
    string Name { get; }
    IEnumerable<string> Values { get; }
    bool Expandable { get; }
    IEnumerable<IDisplayNode> Expand();
    object ViewSync { get; set; }
    NodeState State { get; }
  }

  public interface ILanguageProvider
  {
    bool IsMyModel(Model m);
    IEnumerable<IDisplayNode> GetStates(Model m);
  }

  public abstract class DisplayNode : IDisplayNode
  {
    protected string name;

    public DisplayNode(string n) { name = n; }

    public virtual string Name
    {
      get { return name; }
    }

    public virtual IEnumerable<string> Values
    {
      get { yield break; }
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
  }

  public static class SeqExtensions
  {
    public static IEnumerable<T> Map<S, T>(this IEnumerable<S> inp, Func<S, T> conv)
    {
      foreach (var s in inp) yield return conv(s);
    }
  }

  public class ContainerNode<T> : DisplayNode
  {
    protected Func<T, IDisplayNode> convert;
    protected IEnumerable<T> data;

    public ContainerNode(string name, Func<T, IDisplayNode> convert, IEnumerable<T> data) : base(name)
    {
      this.convert = convert;
      this.data = data;
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


}
