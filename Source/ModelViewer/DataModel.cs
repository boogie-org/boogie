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

  public interface ILanguageProvider
  {
    bool IsMyModel(Model m);
    IEnumerable<IDisplayNode> GetStates(Model m);
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
