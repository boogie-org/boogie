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
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.ModelViewer
{
  public partial class Main : Form
  {
    SkeletonItem unfoldingRoot;
    SkeletonItem[] allItems;
    public int CurrentState, PreviousState = -1;
    IState[] states;
    internal ILanguageProvider langProvider;
    public ILanguageSpecificModel LangModel;
    ToolStripMenuItem[] viewItems;
    Model currentModel;
    Model[] allModels;
    int modelId;
    string lastModelFileName;
    internal ViewOptions viewOpts = new ViewOptions();
    Font smallFont, largeFont;
    int lineHeight;

    // TODO this should be dynamically loaded
    IEnumerable<ILanguageProvider> Providers()
    {
      yield return BCT.Provider.Instance;
      yield return Vcc.Provider.Instance;
      yield return Dafny.Provider.Instance;
      yield return Base.Provider.Instance;
    }

    public Main(string[] args, bool runAsHostedWindow = false)
    {
      InitializeComponent();

      smallFont = stateList.Font;

      if (runAsHostedWindow) {
        this.fileToolStripMenuItem.Enabled = false;
        this.fileToolStripMenuItem.Visible = false;
      }

      viewItems = new ToolStripMenuItem[] {
        normalToolStripMenuItem,
        expertToolStripMenuItem,
        everythingToolStripMenuItem,
        includeTheKitchenSinkToolStripMenuItem
      };

      var debugBreak = false;
      string filename = null;

      for (int i = 1; i < args.Length; i++) {
        var arg = args[i];
        if (arg == "/break" || arg == "-break")
          debugBreak = true;
        else
          filename = arg;
      }

      if (debugBreak) {
        System.Diagnostics.Debugger.Launch();
      }

      if (filename != null) {
        var idx = filename.IndexOf(':');
        if (idx > 0) {
          modelId = int.Parse(filename.Substring(idx + 1));
          filename = filename.Substring(0, idx);
        }
      }

      this.ReadModels(filename, this.modelId);
    }

    private void SetWindowTitle(string fileName)
    {
      if (fileName == null) {
        this.Text = "Boogie Verification Debugger";
      } else {
        this.Text = Path.GetFileName(fileName) + " - Boogie Verification Debugger";
      }
    }

    public void ReadModel(string model, int setModelIdTo = 0)
    {
      Contract.Requires(model != null);

      using (var rd = new StringReader(model))
      {
        allModels = Model.ParseModels(rd).ToArray();
      }

      AddAndLoadModel(setModelIdTo);
    }

    public void ReadModels(string modelFileName, int setModelIdTo)
    {
      this.lastModelFileName = modelFileName;
      this.langProvider = Base.Provider.Instance;

      if (!string.IsNullOrWhiteSpace(modelFileName) && File.Exists(modelFileName)) {
        using (var rd = File.OpenText(modelFileName)) {
          allModels = Model.ParseModels(rd).ToArray();
        }

        AddAndLoadModel(setModelIdTo);
      } else {
        currentModel = new Model();
      }

      this.SetWindowTitle(modelFileName);
    }

    private void AddAndLoadModel(int setModelIdTo)
    {
      modelId = setModelIdTo;

      if (modelId >= allModels.Length)
        modelId = 0;

      currentModel = allModels[modelId];
      AddModelMenu();

      foreach (var p in Providers())
      {
        if (p.IsMyModel(currentModel))
        {
          this.langProvider = p;
          break;
        }
      }

      LoadModel(modelId);
    }

    private void LoadModel(int idx)
    {
      var i = 0;

      //var stateIdx = stateList.SelectedIndices.Count == 0 ? 0 : stateList.SelectedIndices[0];

      modelId = idx;
      foreach (ToolStripMenuItem it in modelsToolStripMenuItem.DropDownItems) {
        it.Checked = i++ == idx;
      }
      currentModel = allModels[idx];
      BuildModel();

      /*
      if (stateList.Items.Count <= stateIdx)
        stateIdx = 0;
      stateList.Items[stateIdx].Selected = true;      
       */
    }

    private void AddModelMenu()
    {
      modelsToolStripMenuItem.DropDownItems.Clear();
      var idx = 0;
      foreach (var m in allModels) {
        var currIdx = idx++; // this local needs to be in this block
        var menuItem = modelsToolStripMenuItem.DropDownItems.Add(string.Format("Model #&{0}", currIdx), null, (s, a) => LoadModel(currIdx)) as ToolStripMenuItem;
        if (currIdx <= 9) {
          menuItem.ShortcutKeys = Keys.Control | (Keys)(currIdx + Keys.D0);
        }
      }
    }

    private void BuildModel()
    {
      stateList.Items.Clear();

      var items = new List<ListViewItem>();
      LangModel = langProvider.GetLanguageSpecificModel(currentModel, viewOpts);
      states = LangModel.States.ToArray();
      var oldRoot = unfoldingRoot;
      SkeletonItem selectedSkel = null;
      if (oldRoot != null && SelectedNode() != null) {
        selectedSkel = SelectedNode().skel;
      }
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

      if (oldRoot == null) {
        SetState(0);
        stateList.Items[0].Selected = true;
        SetColumnSizes();
      } else {
        var mapping = new Dictionary<SkeletonItem, SkeletonItem>();
        unfoldingRoot.SyncWith(mapping, oldRoot);
        SkeletonItem newIt = null;
        while (selectedSkel != null) {
          if (mapping.TryGetValue(selectedSkel, out newIt)) break;
          selectedSkel = selectedSkel.parent;
        }
        if (CurrentState >= stateList.Items.Count)
          CurrentState = 0;
        if (PreviousState >= stateList.Items.Count)
          PreviousState = -1;
        if (newIt != null) GotoNode(newIt);
        SyncStateListValues();
        UpdateMatches(true);
      }
    }

    private void SetColumnSizes()
    {
      currentStateView.Columns[0].Width = currentStateView.Width - currentStateView.Columns[1].Width - currentStateView.Columns[2].Width - 25;
      stateList.Columns[1].Width = stateList.Width - stateList.Columns[0].Width - stateList.Columns[2].Width - 25;
    }

    public void SetState(int id, bool updateView = false)
    {
      if (updateView)
      {
        stateList.SelectedIndices.Clear();
        stateList.SelectedIndices.Add(id);
      }
      if (CurrentState != id) {
        PreviousState = CurrentState;
        CurrentState = id;
      }
      UpdateMatches(true);
    }

    public void HideStateList()
    {
      stateList.Hide();
      splitContainer1.Panel2.Hide();
      splitContainer1.Panel2Collapsed = true;
      splitContainer1.SplitterDistance = splitContainer1.Width;
    }

    public void HideMenuStrip()
    {
      menuStrip1.Hide();
    }

    internal void Activate(TreeNode treeNode)
    {
      throw new NotImplementedException();
    }

    private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
    {

    }

    static Color Col(int c)
    {
      return Color.FromArgb(c >> 16, (c >> 8) & 0xff, c & 0xff);
    }

    static StringFormat center = new StringFormat() { Alignment = StringAlignment.Center };
    static Pen plusPen = new Pen(Col(0xaaaaaa));
    static Brush grayedOut = new SolidBrush(Col(0xaaaaaa));
    static Brush nonPrimary = new SolidBrush(Col(0xeeeeee));
    static Brush matchBg = new SolidBrush(Col(0xFFFA6F));

    static SolidBrush currentStateBrush = new SolidBrush(Color.Red);
    static SolidBrush regularStateBrush = new SolidBrush(Color.Black);
    static SolidBrush previousStateBrush = new SolidBrush(Color.Blue);

    static SolidBrush[] categoryBrushes = new SolidBrush[] {
      new SolidBrush(Color.Black), // Local
      new SolidBrush(Color.Black), // PhysField
      new SolidBrush(Color.Green), // SpecField
      new SolidBrush(Color.Peru), // MethodologyProperty
      new SolidBrush(Color.Green), // UserFunction
      new SolidBrush(Color.Black), // Maplet
    };

    private void listView1_DrawItem(object sender, DrawListViewItemEventArgs e)
    {
      var item = (DisplayItem)e.Item;
      var skel = item.skel;
      var rect = e.Bounds;
      var listView = (ListView)sender;
      lineHeight = rect.Height;
      rect.Y += 1;
      rect.Height -= 2;

      var textBrush = Brushes.Black;
      if (listView.SelectedIndices.Count > 0 && listView.SelectedIndices[0] == e.ItemIndex) {
        e.Graphics.FillRectangle(Brushes.Aquamarine, rect);
        textBrush = Brushes.White;
      } else {
        var bg = Brushes.White;
        if (item.active && !skel.isPrimary[CurrentState])
          bg = nonPrimary;
        if (item.skel.isMatch)
          bg = matchBg;
        e.Graphics.FillRectangle(bg, rect);
      }

      var off = lineHeight * item.skel.level;
      if (item.IsMatchListItem)
        off = 0;

      {
        var plusRect = rect;
        plusRect.Width = lineHeight;
        plusRect.X += off;
        var plusBorder = plusRect;
        plusBorder.Height = lineHeight / 2;
        plusBorder.Width = lineHeight / 2;
        plusBorder.X += lineHeight / 4;
        plusBorder.Y += lineHeight / 4;
        e.Graphics.DrawRectangle(plusPen, plusBorder);
        if (skel.Expandable) {
          float midX = plusBorder.X + plusBorder.Width / 2;
          float midY = plusBorder.Y + plusBorder.Height / 2;
          e.Graphics.DrawLine(plusPen, plusBorder.X + 2, midY, plusBorder.Right - 2, midY);
          if (!item.skel.expanded)
            e.Graphics.DrawLine(plusPen, midX, plusBorder.Y + 2, midX, plusBorder.Bottom - 2);
        }
      }

      off += lineHeight + 3;
      var nameRect = rect;
      var font = listView.Font;

      textBrush = categoryBrushes[(int)item.dispNode.Category];

      if (!item.active)
        textBrush = grayedOut;

      nameRect.Width = listView.Columns[0].Width - 1 - off;
      nameRect.X += off;
      var width = DrawString(e.Graphics, item.SubItems[0].Text, font, textBrush, nameRect);

      textBrush = item.active ? Brushes.Black : grayedOut;
      nameRect.X += width + 4;
      nameRect.Width = listView.Columns[0].Width + listView.Columns[1].Width - nameRect.X;
      width = DrawString(e.Graphics, item.SubItems[1].Text, font, textBrush, nameRect);

      nameRect.X += width + 4;
      nameRect.Width = listView.Width - nameRect.X;
      var t = item.SubItems[2].Text;
      width = DrawString(e.Graphics, t, font, t == item.SubItems[1].Text ? grayedOut : Brushes.Black, nameRect);
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
      var brush = regularStateBrush;
      if (e.Header.Index == 1)
        brush = currentStateBrush;
      else if (e.Header.Index == 2)
        brush = previousStateBrush;

      Rectangle r = e.Bounds;
      r.X += 5;
      r.Y += 4;
      DrawString(e.Graphics, e.Header.Text, e.Header.ListView.Font, brush, r);
    }

    private void listView1_MouseUp(object sender, MouseEventArgs e)
    {
      var clickedItem = (DisplayItem)currentStateView.GetItemAt(5, e.Y);
      if (clickedItem != null) {
        clickedItem.Selected = true;
        clickedItem.Focused = true;

        var skel = clickedItem.skel;
        int plusLoc = skel.level * lineHeight;
        if (skel.Expandable && e.X >= plusLoc && e.X <= plusLoc + lineHeight) {
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
        di.Set(ch[i], CurrentState, PreviousState);
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
      SetColumnSizes();
      currentStateView.Invalidate();
    }

    private void stateList_SelectedIndexChanged(object sender, EventArgs e)
    {
      if (stateList.SelectedItems.Count == 0) return;
      var sel = stateList.SelectedItems[0].Index;

      if (PreviousState >= 0)
        stateList.Items[PreviousState].ForeColor = regularStateBrush.Color;

      SetState(sel);
    }

    DisplayItem SelectedNode()
    {
      if (currentStateView.SelectedItems.Count == 0) return null;
      return (DisplayItem)currentStateView.SelectedItems[0];
    }

    private void currentStateView_SelectedIndexChanged(object sender, EventArgs e)
    {
      SyncStateListValues();
    }

    private void SyncStateListValues()
    {
      var sel = SelectedNode();
      if (sel == null) return;

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
      while (item != null) {
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
            eltEq = LangModel.FindElement(w.Substring(3));
            if (eltEq == null) bad = true;
          }
        } else if (w.StartsWith("use:")) {
          var e = LangModel.FindElement(w.Substring(4));
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
        if (s.isPrimary[CurrentState] && !bad) {
          newMatch = s.MatchesWords(wordsA, refsA, eltEq, CurrentState);
        }
        if (newMatch)
          matches.Add(s);
        if (s.isMatch != newMatch) {
          changed = true;
          s.isMatch = newMatch;
        }
      }

      if (PreviousState >= 0)
        stateList.Items[PreviousState].ForeColor = previousStateBrush.Color;
      stateList.Items[CurrentState].ForeColor = currentStateBrush.Color;

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
      var sel = (DisplayItem)matchesList.SelectedItems[0];
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

    private IEnumerable<SkeletonItem> NamesFor(Model.Element elt)
    {
      var words = new string[0];
      var elts = new Model.Element[0];

      foreach (var s in allItems) {
        if (s.isPrimary[CurrentState] && s.MatchesWords(words, elts, elt, CurrentState)) {
          yield return s;
        }
      }
    }

    private void AddMenuItems(IEnumerable<SkeletonItem> skels, ToolStripItemCollection items, string pref, int max)
    {
      var skelsM = skels.Take(max).ToArray();

      foreach (var s in skelsM) {
        var tmp = s;
        items.Add(pref + s.LongName(CurrentState), null, (x, _) => GotoNode(tmp));
      }

      if (skelsM.Length == max)
        items.Add(new ToolStripMenuItem("...") { Enabled = false });
    }

    private void stateViewMenu_Opening(object sender, CancelEventArgs e)
    {
      IDisplayNode sel = null;
      SkeletonItem skel = null;
      if (SelectedNode() != null) {
        sel = SelectedNode().dispNode;
        skel = SelectedNode().skel;
      }

      var items = stateViewMenu.Items;
      items.Clear();

      if (sel == null) {
        items.Add(new ToolStripMenuItem("Unavailable") { Enabled = false });
        return;
      }

      foreach (var x in sel.References.Where(q => q != sel.Element)) {
        var t = new ToolStripMenuItem(LangModel.CanonicalName(x));
        items.Add(t);
        AddMenuItems(NamesFor(x), t.DropDownItems, "= ", 20);
      }

      if (sel.Element != null) {
        var selName = LangModel.CanonicalName(sel.Element);
        items.Add("Find uses...", null, (s, _) => SetSearch("use:" + selName));

        var aliases = NamesFor(sel.Element).Where(s => s != skel).ToArray();
        if (aliases.Length > 0) {
          items.Add("Aliases...", null, (s, _) => SetSearch("eq:" + selName));
          AddMenuItems(aliases, items, "   = ", 10);
        }
      }
    }

    private void normalToolStripMenuItem_Click(object sender, EventArgs e)
    {
      int viewLev = -1;
      for (int i = 0; i < viewItems.Length; ++i) {
        if (viewItems[i] == sender) {
          viewLev = i;
          viewItems[i].Checked = true;
        } else {
          viewItems[i].Checked = false;
        }
      }
      if (viewLev != -1 && viewLev != viewOpts.ViewLevel) {
        viewOpts.ViewLevel = viewLev;
        BuildModel();
      }
    }

    private void debugToolStripMenuItem_Click(object sender, EventArgs e)
    {
      debugToolStripMenuItem.Checked = !debugToolStripMenuItem.Checked;
      viewOpts.DebugMode = debugToolStripMenuItem.Checked;
      BuildModel();
    }

    private void exitToolStripMenuItem_Click(object sender, EventArgs e)
    {
      this.Close();
    }

    private void reloadModelFileToolStripMenuItem_Click(object sender, EventArgs e)
    {
      ReadModels(this.lastModelFileName, this.modelId);
    }

    private SourceView sourceView;
    private void ShowSource()
    {
      if (stateList.SelectedItems.Count == 0) return;
      var li = stateList.SelectedItems[0] as ListViewItem;
      if (li != null) {
        var r = ((IState)li.Tag).ShowSource();
        if (r != null) {
          if (sourceView == null) {
            sourceView = new SourceView();
          }
          sourceView.largeFont = largeFontToolStripMenuItem.Checked;
          sourceView.SetSourceLocation(r);
          sourceView.BringToFront();
        }
      }
    }

    private void showSourceToolStripMenuItem_Click(object sender, EventArgs e)
    {
      ShowSource();
    }

    private void stateList_DoubleClick(object sender, EventArgs e)
    {
      ShowSource();
    }

    private void openModelMenuItem_Click(object sender, EventArgs e)
    {
      if (this.openModelFileDialog.ShowDialog() == System.Windows.Forms.DialogResult.OK) {
        this.ReadModels(this.openModelFileDialog.FileName, 0);
      }
    }

    private void largeFontToolStripMenuItem_Click(object sender, EventArgs e)
    {
      largeFontToolStripMenuItem.Checked = !largeFontToolStripMenuItem.Checked;

      if (largeFont == null) {
        largeFont = new Font(smallFont.FontFamily, smallFont.Size * 2, smallFont.Unit);
      }

      SetFont(largeFontToolStripMenuItem.Checked ? largeFont : smallFont);
      //textBox1.Font = font;
      //linkLabel1.Font = font;
      //label1.Font = font;
    }

    public void SetFont(System.Drawing.Font font)
    {
      stateList.Font = font;
      currentStateView.Font = font;
      matchesList.Font = font;
    }

    private void Main_Load(object sender, EventArgs e)
    {

    }

    private void currentStateView_KeyDown(object sender, KeyEventArgs e)
    {
      var node = SelectedNode();
      if (node == null) return;

      if (e.KeyCode == Keys.Right && !node.skel.Expanded && node.skel.Expandable) {
        node.skel.Expanded = true;
        SyncCurrentStateView();
        return;
      }

      if (e.KeyCode == Keys.Left) {
        if (node.skel.Expanded) {
          node.skel.Expanded = false;
          SyncCurrentStateView();
          return;
        } else {
          var par = node.skel.parent;
          if (par != null && par.parent != null) {
            // par.Expanded = false;
            foreach (DisplayItem it in currentStateView.Items) {
              it.Selected = it.skel == par;
              it.Focused = it.skel == par;
              if (it.Selected) {
                it.EnsureVisible();
              }
            }
            SyncCurrentStateView();
          }
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

    internal void Set(SkeletonItem s, int id, int prevId)
    {
      if (skel == s && stateId == id)
        return;
      skel = s;
      stateId = id;

      dispNode = skel.displayNodes[stateId];
      active = dispNode != null;

      var closeStateId = stateId;

      if (dispNode == null) {
        while (closeStateId < skel.displayNodes.Length && skel.displayNodes[closeStateId] == null)
          closeStateId++;
        if (closeStateId >= skel.displayNodes.Length) {
          closeStateId = stateId;
          while (closeStateId >= 0 && skel.displayNodes[closeStateId] == null)
            closeStateId--;
        }
        dispNode = skel.displayNodes[closeStateId];
      }

      var fullName = skel.LongName(closeStateId);
      var tooltip = dispNode.ToolTip;
      if (tooltip == null)
        tooltip = "";
      if(tooltip.Length > 0 && tooltip[tooltip.Length - 1] != '\n')
        tooltip += "\n";
      tooltip += "Full name: " + fullName;
      if (tooltip != null) {
        this.ToolTipText = tooltip;
      }

      var name = dispNode.Name;
      if (name != dispNode.ShortName)
      {
        name = dispNode.ShortName;
      }

      if (IsMatchListItem) {
        Util.Assert(active);
        name = fullName;
      }

      this.SubItems[0].Text = name;
      this.SubItems[1].Text = active ? dispNode.Value : "";

      var prev = "";

      if (!IsMatchListItem && prevId >= 0 && skel.displayNodes[prevId] != null) {
        prev = skel.displayNodes[prevId].Value;
      }

      this.SubItems[2].Text = prev;
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
