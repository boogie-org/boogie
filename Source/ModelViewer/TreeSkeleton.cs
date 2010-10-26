using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  internal class SkeletonItem
  {
    readonly IEdgeName name;
    readonly List<SkeletonItem> children = new List<SkeletonItem>();
    internal readonly IDisplayNode[] displayNodes;
    readonly SkeletonItem parent;
    readonly Main main;
    internal readonly int level;
    internal bool expanded, wasExpanded;

    public void Iter(Action<SkeletonItem> handler)
    {
      handler(this);
      children.ForEach(u => u.Iter(handler));
    }

    public IEnumerable<SkeletonItem> RecChildren
    {
      get
      {
        if (expanded) {
          foreach (var c in children) {
            yield return c;
            foreach (var ch in c.RecChildren)
              yield return ch;
          }
        }
      }
    }

    public void PopulateRoot(IEnumerable<IState> states)
    {
      var i = 0;
      foreach (var s in states) {
        displayNodes[i++] = new ContainerNode<IDisplayNode>(this.name, x => x, s.Nodes);
      }
    }

    public SkeletonItem(Main m, int stateCount)
    {
      name = new EdgeName("<root>");
      main = m;
      displayNodes = new IDisplayNode[stateCount];
    }

    internal SkeletonItem(IEdgeName n, SkeletonItem par)
      : this(par.main, par.displayNodes.Length)
    {
      parent = par;
      name = n;
      level = par.level + 1;
    }

    public bool Expandable
    {
      get { return displayNodes.Any(d => d != null && d.Expandable); }
    }

    public bool Expanded
    {
      get { return expanded; }
      set
      {
        if (!value) {
          expanded = false;
        } else {
          if (expanded) return;
          expanded = true;
          if (wasExpanded) return;
          wasExpanded = true;

          var created = new Dictionary<string, SkeletonItem>();
          for (int i = 0; i < displayNodes.Length; ++i) {
            var dn = displayNodes[i];
            if (dn == null || !dn.Expandable) continue;
            foreach (var child in dn.Expand()) {
              SkeletonItem skelChild;
              if (!created.TryGetValue(child.Name.ShortName(), out skelChild)) {
                skelChild = new SkeletonItem(child.Name, this);
                created.Add(child.Name.ShortName(), skelChild);
                children.Add(skelChild);
              }
              skelChild.displayNodes[i] = child;
            }
          }
        }
      }
    }
  }

}
