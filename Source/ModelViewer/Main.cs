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
    SkeletonItem[] allItems;
    int currentState;
    IState[] states;
    internal ILanguageProvider langProvider;
    internal ILanguageSpecificModel langModel;

    // TODO this should be dynamically loaded
    IEnumerable<ILanguageProvider> Providers()
    {
      yield return Vcc.Provider.Instance;
      yield return Dafny.Provider.Instance;
      yield return Base.Provider.Instance;
    }

    public Main()
    {
      InitializeComponent();

      var debugBreak = false;
      string filename = null;
      var args = Environment.GetCommandLineArgs();
      for (int i = 1; i < args.Length; i++) {
        var arg = args[i];
        if (arg == "/break")
          debugBreak = true;
        else
          filename = arg;
      }
      if (debugBreak) {
        System.Diagnostics.Debugger.Launch();
      }
      if (filename == null) {
        throw new Exception("error: usage:  ModelViewer.exe MyProgram.model");  // (where does this exception go?)
      }

      Model m;

      using (var rd = File.OpenText(filename)) {
        var models = Model.ParseModels(rd);
        m = models[0];
      }

      this.Text = Path.GetFileName(filename) + " - Boogie Verification Debugger";

      langProvider = null;
      foreach (var p in Providers()) {
        if (p.IsMyModel(m)) {
          langProvider = p;
          break;
        }
      }
      
      var items = new List<ListViewItem>();
      langModel = langProvider.GetLanguageSpecificModel(m);
      states = langModel.States.ToArray();
      unfoldingRoot = new SkeletonItem(this, states.Length);
      allItems = unfoldingRoot.PopulateRoot(states);

      var idx = 0;
      foreach (var i in states) {
        var it = new ListViewItem(new string[] { idx.ToString(), i.Name, "" });
        it.Tag = i;
        items.Add(it);
        idx++;
      }
      stateList.Items.AddRange(items.ToArray());
      unfoldingRoot.Expanded = true;
      SetState(0);
      stateList.Items[0].Selected = true;

      currentStateView.Columns[2].Width = currentStateView.Width - currentStateView.Columns[0].Width - currentStateView.Columns[1].Width - 5;
    }

    void SetState(int id)
    {
      currentState = id;
      UpdateMatches(true);
    }

    internal void Activate(TreeNode treeNode)
    {
      throw new NotImplementedException();
    }

    private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
    {

    }

    const int levelMult = 16;
    const int plusWidth = 16;

    static Color Col(int c)
    {
      return Color.FromArgb(c >> 16, (c >> 8) & 0xff, c & 0xff);
    }

    static StringFormat center = new StringFormat() { Alignment = StringAlignment.Center };
    static Pen plusPen = new Pen(Col(0xaaaaaa));
    static Brush grayedOut = new SolidBrush(Col(0xaaaaaa));
    static Brush nonPrimary = new SolidBrush(Col(0xeeeeee));
    static Brush matchBg = new SolidBrush(Col(0xFFFA6F));
    
    private void listView1_DrawItem(object sender, DrawListViewItemEventArgs e)
    {
      var item = (DisplayItem)e.Item;
      var skel = item.skel;
      var rect = e.Bounds;
      var listView = (ListView)sender;
      rect.Y += 1;
      rect.Height -= 2;

      var textBrush = Brushes.Black;
      if (listView.SelectedIndices.Count > 0 && listView.SelectedIndices[0] == e.ItemIndex) {
        e.Graphics.FillRectangle(Brushes.Navy, rect);
        textBrush = Brushes.White;
      } else {
        var bg = Brushes.White;
        if (item.active && !skel.isPrimary[currentState])
          bg = nonPrimary;
        if (item.skel.isMatch)
          bg = matchBg;
        e.Graphics.FillRectangle(bg, rect);
      }

      var off = levelMult * item.skel.level;
      if (item.IsMatchListItem)
        off = 0;

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
        if (skel.Expandable) {
          float midX = plusBorder.X + plusBorder.Width / 2;
          float midY = plusBorder.Y + plusBorder.Height / 2;
          e.Graphics.DrawLine(plusPen, plusBorder.X + 2, midY, plusBorder.Right - 2, midY);
          if (!item.skel.expanded)
            e.Graphics.DrawLine(plusPen, midX, plusBorder.Y + 2, midX, plusBorder.Bottom - 2);
        }
      }

      off += plusWidth + 3;
      var nameRect = rect;
      var font = listView.Font;

      if ((item.dispNode.State & NodeState.Changed) != 0)
        textBrush = Brushes.Red;
      if (!item.active)
        textBrush = grayedOut;

      nameRect.Width = listView.Columns[0].Width - 1 - off;
      nameRect.X += off;
      var width = DrawString(e.Graphics, item.SubItems[0].Text, font, textBrush, nameRect);

      nameRect.X += width + 4;
      nameRect.Width = listView.Columns[0].Width + listView.Columns[1].Width - nameRect.X;
      width = DrawString(e.Graphics, item.SubItems[1].Text, font, textBrush, nameRect);

      nameRect.X += width + 4;
      nameRect.Width = listView.Width - nameRect.X;
      width = DrawString(e.Graphics, item.SubItems[2].Text, font, textBrush, nameRect);
    }

    private int DrawString(Graphics g, string s, Font font, Brush textBrush, Rectangle minRect)
    {
      var sz = g.MeasureString(s, font).Width;
      if (sz > minRect.Width - 2) {
        minRect.Width = (int)(sz + 20);
      }
      g.DrawString(s, font, textBrush, minRect);
      return minRect.Width;
    }

    private void listView1_DrawColumnHeader(object sender, DrawListViewColumnHeaderEventArgs e)
    {
      e.DrawBackground();
      e.DrawText();
    }

    private void listView1_MouseUp(object sender, MouseEventArgs e)
    {
      var clickedItem = (DisplayItem)currentStateView.GetItemAt(5, e.Y);
      if (clickedItem != null) {
        clickedItem.Selected = true;
        clickedItem.Focused = true;

        var skel = clickedItem.skel;
        int plusLoc = skel.level * levelMult;
        if (skel.Expandable && e.X >= plusLoc && e.X <= plusLoc + plusWidth) {
          skel.Expanded = !skel.Expanded;
          SyncCurrentStateView();
        }
      }
    }

    private void SyncCurrentStateView()
    {
      SyncListView(unfoldingRoot.RecChildren, currentStateView, (x, y) => { });
    }

    private void SyncListView(IEnumerable<SkeletonItem> items, ListView listView, Action<DisplayItem, SkeletonItem> cb)
    {
      var ch = items.ToArray();
      var missing = ch.Length - listView.Items.Count;
      listView.BeginUpdate();
      if (missing < 0) {
        missing = -missing;
        while (missing-- > 0) {
          listView.Items.RemoveAt(listView.Items.Count - 1);
        }
      } else {
        while (missing-- > 0) {
          listView.Items.Add(new DisplayItem());
        }
      }
      for (int i = 0; i < ch.Length; ++i) {
        var di = (DisplayItem)listView.Items[i];
        cb(di, ch[i]);
        di.Set(ch[i], currentState);
      }
      listView.EndUpdate();
      listView.Invalidate();
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

      var normalFont = stateList.Font;
      var boldFont = new Font(normalFont, FontStyle.Bold);
      stateList.Items[currentState].Font = normalFont;
      stateList.Items[sel].Font = boldFont;

      SetState(sel);
    }

    private void currentStateView_SelectedIndexChanged(object sender, EventArgs e)
    {
      if (currentStateView.SelectedItems.Count == 0) return;
      var sel = (DisplayItem) currentStateView.SelectedItems[0];

      stateList.BeginUpdate();
      for (int i = 0; i < sel.skel.displayNodes.Length; ++i) {
        var dn = sel.skel.displayNodes[i];
        stateList.Items[i].SubItems[2].Text = dn == null ? "" : dn.Value;
      }
      stateList.EndUpdate();
    }

    private void ExpandParents(SkeletonItem item)
    {
      item = item.parent;
      while (item != null && !item.Expanded) {
        item.Expanded = true;
        item = item.parent;
      }
    }

    private void textBox1_TextChanged(object sender, EventArgs e)
    {
      UpdateMatches(false);
    }

    private void UpdateMatches(bool force)
    {
      var bad = false;
      Model.Element eltEq = null;
      var eltRef = new List<Model.Element>();
      var words = new List<string>();

      foreach (var w in textBox1.Text.Split(' ')) {
        if (w == "") continue;
        if (w.StartsWith("eq:")) {
          if (eltEq != null) bad = true;
          else {
            eltEq = langModel.FindElement(w.Substring(3));
            if (eltEq == null) bad = true;
          }
        } else if (w.StartsWith("use:")) {
          var e = langModel.FindElement(w.Substring(4));
          if (e == null) bad = true;
          else eltRef.Add(e);
        } else {
          words.Add(w.ToLower());
        }
      }

      textBox1.ForeColor = bad ? Color.Red : Color.Black;
      
      var wordsA = words.ToArray();
      var refsA = eltRef.ToArray();

      if (eltEq == null && wordsA.Length == 0 && refsA.Length == 0)
        bad = true;

      var changed = true; // force;
      var matches = new List<SkeletonItem>();

      foreach (var s in allItems) {
        var newMatch = false;
        if (s.isPrimary[currentState] && !bad) {
          newMatch = s.MatchesWords(wordsA, refsA, eltEq, currentState);
        }
        if (newMatch)
          matches.Add(s);
        if (s.isMatch != newMatch) {
          changed = true;
          s.isMatch = newMatch;
        }
      }

      if (changed) {
        SyncListView(matches, matchesList, (di, _) => { di.IsMatchListItem = true; });
        SyncCurrentStateView();
      }
    }

    private void matchesList_Resize(object sender, EventArgs e)
    {
      matchesList.Invalidate();
    }

    private void matchesList_DoubleClick(object sender, EventArgs e)
    {
      if (matchesList.SelectedItems.Count == 0) return;
      var sel = (DisplayItem) matchesList.SelectedItems[0];
      GotoNode(sel.skel);
    }

    private void linkLabel1_LinkClicked(object sender, LinkLabelLinkClickedEventArgs e)
    {
      foreach (DisplayItem it in matchesList.Items) {
        ExpandParents(it.skel);
      }
      SyncCurrentStateView();
    }

    private void SetSearch(string text)
    {
      textBox1.Text = text;
    }

    private void GotoNode(SkeletonItem skel)
    {
      ExpandParents(skel);
      SyncCurrentStateView();
      foreach (DisplayItem it in currentStateView.Items) {
        if (it.skel == skel) {
          it.Selected = true;
          currentStateView.EnsureVisible(it.Index);
          break;
        }
      }
    }

    private void stateViewMenu_Opening(object sender, CancelEventArgs e)
    {
      IDisplayNode sel = null;
      SkeletonItem skel = null;
      if (currentStateView.SelectedItems.Count > 0) {
        var it = currentStateView.SelectedItems[0];
        sel = ((DisplayItem)it).dispNode;
        skel = ((DisplayItem)it).skel;
      }

      var items = stateViewMenu.Items;
      items.Clear();

      if (sel == null) {
        items.Add(new ToolStripMenuItem("Unavailable") { Enabled = false });
        return;
      }

      var selName = langModel.CanonicalName(sel.Element);

      items.Add("Find uses...", null, (s, _) => SetSearch("use:" + selName));
      items.Add("Aliases...", null, (s, _) => SetSearch("eq:" + selName));

      var words = new string[0];
      var elts = new Model.Element[0];
      var max = 10;
      foreach (var s in allItems) {
        if (s != skel && s.isPrimary[currentState] && s.MatchesWords(words, elts, sel.Element, currentState)) {
          if (max-- < 0) {
            items.Add(new ToolStripMenuItem("...") { Enabled = false });
            break;
          }
          var tmp = s;
          items.Add("      " + s.LongName(currentState), null, (x, _) => GotoNode(tmp));
        }
      }
    }
  }

  internal class DisplayItem : ListViewItem
  {
    internal SkeletonItem skel;
    internal int stateId;
    internal bool active;
    internal IDisplayNode dispNode;

    public bool IsMatchListItem { get; set; }

    internal void Set(SkeletonItem s, int id)
    {
      if (skel == s && stateId == id)
        return;
      skel = s;
      stateId = id;

      dispNode = skel.displayNodes[stateId];
      active = dispNode != null;

      if (dispNode == null) {
        for (int i = stateId; i < skel.displayNodes.Length; ++i) {
          dispNode = skel.displayNodes[i];
          if (dispNode != null) break;
        }
        for (int i = stateId; i >= 0; --i) {
          if (dispNode != null) break;
          dispNode = skel.displayNodes[i];
        }
      }

      var tooltip = dispNode.ToolTip;
      var aliases = ""; // AliasesAsString(dispNode);
      if (IsMatchListItem)
        aliases = "";
      if (tooltip != null) {
        this.ToolTipText = tooltip;
      } else {
        this.ToolTipText = aliases;
      }

      var name = dispNode.Name;

      if (IsMatchListItem) {
        Util.Assert(active);
       name = skel.LongName(stateId);
      }

      this.SubItems[0].Text = name;
      this.SubItems[1].Text = active ? dispNode.Value : "";
      // this.SubItems[2].Text = active ? aliases : "";
    }

    internal DisplayItem()
       : base(new string[] { "", "", "" })
    {
    }

    /*
    static internal string AliasesAsString(IDisplayNode dn)
    {
      if (dn == null) return "";

      var sb = new StringBuilder();
      var canon = dn.CanonicalValue;
      foreach (var n in dn.Aliases) {
        if (n == canon)
          continue;
        sb.Append(n).Append(", ");
        if (sb.Length > 300)
          break;
      }
      if (sb.Length > 2) sb.Length -= 2;
      return sb.ToString();
    }
     */
  }
}
