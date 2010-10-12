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
      foreach (var i in prov.GetStates(m))
        items.Add(new DisplayItem(i));
      listView1.Items.AddRange(items.ToArray());

      listView1.Columns[1].Width = listView1.Width - listView1.Columns[0].Width - 5;
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
      if (listView1.SelectedIndices.Count > 0 && listView1.SelectedIndices[0] == e.ItemIndex) {
        // Draw the background and focus rectangle for a selected item.
        e.Graphics.FillRectangle(Brushes.Navy, rect);
        // e.DrawFocusRectangle();
        textBrush = Brushes.White;
      } else {
        e.Graphics.FillRectangle(Brushes.White, rect);
      }

      var off = levelMult * item.level;

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
          if (!item.expanded)
            e.Graphics.DrawLine(plusPen, midX, plusBorder.Y + 2, midX, plusBorder.Bottom - 2);
        }
      }

      off += plusWidth + 3;
      var nameRect = rect;
      var font = listView1.Font;

      var sz = e.Graphics.MeasureString(item.displayNode.Name, font);
      nameRect.Width = listView1.Columns[0].Width - 1 - off;
      if (nameRect.Width < sz.Width + 2)
        nameRect.Width = (int)sz.Width + 20;
      nameRect.X += off;
      e.Graphics.DrawString(item.displayNode.Name, font, textBrush, nameRect);

      var valRect = rect;
      valRect.X = nameRect.X + nameRect.Width + 4;
      valRect.Width = listView1.Width - valRect.X;
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
      var clickedItem = (DisplayItem)listView1.GetItemAt(5, e.Y);
      if (clickedItem != null) {
        clickedItem.Selected = true;
        clickedItem.Focused = true;

        int plusLoc = clickedItem.level * levelMult;
        if (clickedItem.displayNode.Expandable && e.X >= plusLoc && e.X <= plusLoc + plusWidth) {
          clickedItem.expanded = !clickedItem.expanded;

          if (clickedItem.expanded) {
            if (clickedItem.collapsedChildren == null) {
              var items = new List<DisplayItem>();
              foreach (var ch in clickedItem.displayNode.Expand()) {
                var it = new DisplayItem(ch);
                it.level = clickedItem.level + 1;
                items.Add(it);
              }
              clickedItem.collapsedChildren = items.ToArray();
            }
            var pos = clickedItem.Index + 1;
            listView1.BeginUpdate();
            foreach (var it in clickedItem.collapsedChildren) {
              listView1.Items.Insert(pos, it);
              pos++;
            }
            listView1.EndUpdate();
          } else {
            var collapsed = new List<DisplayItem>();
            var beg = clickedItem.Index + 1;
            for (int i = beg; i < listView1.Items.Count; ++i) {
              var curr = (DisplayItem)listView1.Items[i];
              if (curr.level <= clickedItem.level) break;
              collapsed.Add(curr);
            }
            clickedItem.collapsedChildren = collapsed.ToArray();
            listView1.BeginUpdate();
            for (int i = 0; i < collapsed.Count; ++i)
              listView1.Items.RemoveAt(beg);
            listView1.EndUpdate();
          }

          listView1.Invalidate();
        }
      }
    }

    private void listView1_ColumnWidthChanged(object sender, ColumnWidthChangedEventArgs e)
    {
      listView1.Invalidate();
    }

    private void listView1_Resize(object sender, EventArgs e)
    {
      listView1.Invalidate();
    }

  }

  internal class DisplayItem : ListViewItem
  {
    internal IDisplayNode displayNode;
    internal bool expanded;
    internal int level;
    internal DisplayItem[] collapsedChildren;

    internal DisplayItem(IDisplayNode d)
       : base(d.Name)
    {
      displayNode = d;
      displayNode.ViewSync = this;
      expanded = false;

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
