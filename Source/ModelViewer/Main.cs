using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Linq;
using System.Text;
using System.Windows.Forms;

using System.IO;
using Microsoft.Boogie;

namespace Microsoft.Boogie.ModelViewer
{
  public partial class Main : Form
  {
    public string SearchText;
    SkeletonItem unfoldingRoot;
    int currentState;
    IState[] states;

    // TODO this should be dynamically loaded
    IEnumerable<ILanguageProvider> Providers()
    {
      yield return Vcc.Provider.Instance;
      yield return Base.Provider.Instance;
    }

    public Main()
    {
      InitializeComponent();


      var args = Environment.GetCommandLineArgs();
      Model m;

      using (var rd = File.OpenText(args[1])) {
        var models = Model.ParseModels(rd);
        m = models[0];
      }

      ILanguageProvider prov = null;
      foreach (var p in Providers()) {
        if (p.IsMyModel(m)) {
          prov = p;
          break;
        }
      }
      
      var items = new List<ListViewItem>();
      states = prov.GetStates(m).ToArray();
      unfoldingRoot = new SkeletonItem(this, states.Length);
      unfoldingRoot.PopulateRoot(states);

      foreach (var i in states) {
        var it = new ListViewItem(new string[] { i.Name, "" });
        it.Tag = i;
        items.Add(it);
      }
      stateList.Items.AddRange(items.ToArray());
      SetState(0);

      currentStateView.Columns[1].Width = currentStateView.Width - currentStateView.Columns[0].Width - 5;
    }

    void SetState(int id)
    {
      currentState = id;
      unfoldingRoot.SetStateId(id);

      SkeletonItem sel = null;
      if (currentStateView.SelectedItems.Count > 0)
        sel = ((DisplayItem)currentStateView.SelectedItems[0]).skel;

      currentStateView.BeginUpdate();
      currentStateView.Items.Clear();
      currentStateView.Items.AddRange(unfoldingRoot.DisplayItems().Skip(1).ToArray());
      if (sel != null && sel.DisplayItem != null) {
        var it = sel.DisplayItem;
        it.Selected = true;
        currentStateView.EnsureVisible(it.Index);
      }
      currentStateView.EndUpdate();
    }

    internal void Activate(TreeNode treeNode)
    {
      throw new NotImplementedException();
    }

    private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
    {

    }

    const int levelMult = 10;
    const int plusWidth = 16;

    static StringFormat center = new StringFormat() { Alignment = StringAlignment.Center };
    static Pen plusPen = new Pen(Color.FromArgb(0xaa, 0xaa, 0xaa));
    
    private void listView1_DrawItem(object sender, DrawListViewItemEventArgs e)
    {
      var item = (DisplayItem)e.Item;
      var rect = e.Bounds;
      rect.Y += 1;
      rect.Height -= 2;

      var textBrush = Brushes.Black;
      if (currentStateView.SelectedIndices.Count > 0 && currentStateView.SelectedIndices[0] == e.ItemIndex) {
        // Draw the background and focus rectangle for a selected item.
        e.Graphics.FillRectangle(Brushes.Navy, rect);
        // e.DrawFocusRectangle();
        textBrush = Brushes.White;
      } else {
        e.Graphics.FillRectangle(Brushes.White, rect);
      }

      var off = levelMult * item.skel.level;

      {
        var plusRect = rect;
        plusRect.Width = plusWidth;
        plusRect.X += off;
        var plusBorder = plusRect;
        plusBorder.Height = 8;
        plusBorder.Width = 8;
        plusBorder.X += 4;
        plusBorder.Y += 3;        
        e.Graphics.DrawRectangle(plusPen, plusBorder);
        if (item.displayNode.Expandable) {
          float midX = plusBorder.X + plusBorder.Width / 2;
          float midY = plusBorder.Y + plusBorder.Height / 2;
          e.Graphics.DrawLine(plusPen, plusBorder.X + 2, midY, plusBorder.Right - 2, midY);
          if (!item.skel.expanded)
            e.Graphics.DrawLine(plusPen, midX, plusBorder.Y + 2, midX, plusBorder.Bottom - 2);
        }
      }

      off += plusWidth + 3;
      var nameRect = rect;
      var font = currentStateView.Font;

      var sz = e.Graphics.MeasureString(item.displayNode.Name, font);
      nameRect.Width = currentStateView.Columns[0].Width - 1 - off;
      if (nameRect.Width < sz.Width + 2)
        nameRect.Width = (int)sz.Width + 20;
      nameRect.X += off;
      e.Graphics.DrawString(item.displayNode.Name, font, textBrush, nameRect);

      var valRect = rect;
      valRect.X = nameRect.X + nameRect.Width + 4;
      valRect.Width = currentStateView.Width - valRect.X;
      e.Graphics.DrawString(item.SubItems[1].Text, font, textBrush, valRect); // , StringFormat.GenericDefault);
    }

    private void listView1_DrawSubItem(object sender, DrawListViewSubItemEventArgs e)
    {
    }

    private void listView1_DrawColumnHeader(object sender, DrawListViewColumnHeaderEventArgs e)
    {
      e.DrawBackground();
      e.DrawText();
    }

    private void listView1_MouseMove(object sender, MouseEventArgs e)
    {
    }

    private void listView1_MouseUp(object sender, MouseEventArgs e)
    {
      var clickedItem = (DisplayItem)currentStateView.GetItemAt(5, e.Y);
      if (clickedItem != null) {
        clickedItem.Selected = true;
        clickedItem.Focused = true;

        var skel = clickedItem.skel;
        int plusLoc = skel.level * levelMult;
        if (clickedItem.displayNode.Expandable && e.X >= plusLoc && e.X <= plusLoc + plusWidth) {
          SetExpansion(clickedItem, !skel.expanded);
        }
      }
    }

    private void SetExpansion(DisplayItem clickedItem, bool exp)
    {
      var pos = clickedItem.Index + 1;
      var skel = clickedItem.skel;

      if (skel.expanded == exp) return;

      if (!skel.expanded) {
        skel.Expand(currentState);

        currentStateView.BeginUpdate();
        foreach (var it in skel.DisplayItems()) {
          currentStateView.Items.Insert(pos, it);
          pos++;
        }
        currentStateView.EndUpdate();
      } else {
        var cnt = skel.DisplayItems().Count();

        skel.Fold();

        currentStateView.BeginUpdate();
        for (int i = 0; i < cnt; ++i)
          currentStateView.Items.RemoveAt(pos);
        currentStateView.EndUpdate();
      }

      currentStateView.Invalidate();
    }

    private void listView1_ColumnWidthChanged(object sender, ColumnWidthChangedEventArgs e)
    {
      currentStateView.Invalidate();
    }

    private void listView1_Resize(object sender, EventArgs e)
    {
      currentStateView.Invalidate();
    }

    private void stateList_SelectedIndexChanged(object sender, EventArgs e)
    {
      if (stateList.SelectedItems.Count == 0) return;
      var sel = stateList.SelectedItems[0].Index;
      SetState(sel);
    }
  }

  internal class SkeletonItem
  {
    readonly string name;
    readonly List<SkeletonItem> inactiveChildren = new List<SkeletonItem>();
    readonly List<SkeletonItem> activeChildren = new List<SkeletonItem>();
    readonly IDisplayNode[] displayNodes;
    readonly IDisplayNode[][] displayNodeExpansions;
    readonly SkeletonItem parent;
    readonly Main main;
    internal readonly int level;
    internal bool expanded;
    DisplayItem currNode; // in the current view

    public void Iter(Action<SkeletonItem> handler)
    {
      handler(this);
      activeChildren.Iter(u => u.Iter(handler));
      inactiveChildren.Iter(u => u.Iter(handler));
    }

    public void SetStateId(int id)
    {
      expanded = true;
      Iter(u =>
      {
        u.currNode = null;
        u.inactiveChildren.AddRange(activeChildren);
        u.activeChildren.Clear();
      });
      CreateBacking(id);
    }

    public DisplayItem DisplayItem { get { return currNode; } }

    public IEnumerable<DisplayItem> DisplayItems()
    {
      Util.Assert(currNode != null);
      yield return currNode;
      if (expanded) {
        foreach (var ch in activeChildren)
          foreach (var d in ch.DisplayItems())
            yield return d;
      }
    }

    public void PopulateRoot(IEnumerable<IState> states)
    {
      var i = 0;
      foreach(var s in states) {
        displayNodes[i++] = new ContainerNode<IDisplayNode>(this.name, x => x, s.Nodes);
      }
    }

    public SkeletonItem(Main m, int stateCount)
    {
      name = "<root>";
      main = m;
      displayNodes = new IDisplayNode[stateCount];
      displayNodeExpansions = new IDisplayNode[stateCount][];
    }

    internal SkeletonItem(string n, SkeletonItem par)
      : this(par.main, par.displayNodes.Length)
    {
      parent = par;
      name = n;
      level = par.level + 1;
    }

    public void Fold()
    {
      expanded = false;
    }

    public void Expand(int stateId)
    {
      if(expanded) return;
      expanded = true;
      CreateBacking(stateId);
    }

    private void CreateBacking(int stateId)
    {
      var dn = displayNodes[stateId];
      if (currNode == null)
        currNode = new DisplayItem(dn, this);

      if (!expanded || activeChildren.Count > 0)
        return;

      if (displayNodeExpansions[stateId] == null) {
        if (dn.Expandable) {
          displayNodeExpansions[stateId] = dn.Expand().ToArray();
        } else {
          displayNodeExpansions[stateId] = new DisplayNode[0];
        }
      }

      if (activeChildren.Count == displayNodeExpansions[stateId].Length)
        return;

      var dict = inactiveChildren.ToDictionary(u => u.name);

      foreach (var d in displayNodeExpansions[stateId]) {
        SkeletonItem child;
        if (dict.TryGetValue(d.EdgeName, out child)) {
          dict.Remove(d.EdgeName);
        } else {
          child = new SkeletonItem(d.EdgeName, this);
        }
        activeChildren.Add(child);
        child.displayNodes[stateId] = d;
      }
      inactiveChildren.Clear();
      inactiveChildren.AddRange(dict.Values);

      activeChildren.Iter(c => c.CreateBacking(stateId));
    }
  }

  internal class DisplayItem : ListViewItem
  {
    internal readonly IDisplayNode displayNode;
    internal readonly SkeletonItem skel;

    internal DisplayItem(IDisplayNode d, SkeletonItem s)
       : base(d.Name)
    {
      displayNode = d;
      skel = s;

      var sb = new StringBuilder();
      foreach (var n in displayNode.Values) {
        sb.Append(n).Append(", ");
        if (sb.Length > 300)
          break;
      }
      if (sb.Length > 2) sb.Length -= 2;

      this.SubItems.Add(sb.ToString());
    }
  }
}
