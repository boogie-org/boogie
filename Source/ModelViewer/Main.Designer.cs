namespace Microsoft.Boogie.ModelViewer
{
  partial class Main
  {
    /// <summary>
    /// Required designer variable.
    /// </summary>
    private System.ComponentModel.IContainer components = null;

    /// <summary>
    /// Clean up any resources being used.
    /// </summary>
    /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
    protected override void Dispose(bool disposing)
    {
      if (disposing && (components != null)) {
        components.Dispose();
      }
      base.Dispose(disposing);
    }

    #region Windows Form Designer generated code

    /// <summary>
    /// Required method for Designer support - do not modify
    /// the contents of this method with the code editor.
    /// </summary>
    private void InitializeComponent()
    {
      this.components = new System.ComponentModel.Container();
      System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(Main));
      this.currentStateView = new System.Windows.Forms.ListView();
      this.name = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.value = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.prevValue = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.stateViewMenu = new System.Windows.Forms.ContextMenuStrip(this.components);
      this.dummyItemToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.splitContainer1 = new System.Windows.Forms.SplitContainer();
      this.splitContainer2 = new System.Windows.Forms.SplitContainer();
      this.matchesList = new System.Windows.Forms.ListView();
      this.columnHeader4 = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.columnHeader5 = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.linkLabel1 = new System.Windows.Forms.LinkLabel();
      this.label1 = new System.Windows.Forms.Label();
      this.textBox1 = new System.Windows.Forms.TextBox();
      this.stateList = new System.Windows.Forms.ListView();
      this.columnHeader3 = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.columnHeader1 = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.columnHeader2 = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.contextMenuStrip1 = new System.Windows.Forms.ContextMenuStrip(this.components);
      this.showSourceToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.menuStrip1 = new System.Windows.Forms.MenuStrip();
      this.fileToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.openModelMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripSeparator1 = new System.Windows.Forms.ToolStripSeparator();
      this.reloadModelFileToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.exitToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.viewToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.normalToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.expertToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.everythingToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.includeTheKitchenSinkToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.toolStripMenuItem1 = new System.Windows.Forms.ToolStripSeparator();
      this.debugToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.largeFontToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.modelsToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
      this.openModelFileDialog = new System.Windows.Forms.OpenFileDialog();
      this.stateViewMenu.SuspendLayout();
      ((System.ComponentModel.ISupportInitialize)(this.splitContainer1)).BeginInit();
      this.splitContainer1.Panel1.SuspendLayout();
      this.splitContainer1.Panel2.SuspendLayout();
      this.splitContainer1.SuspendLayout();
      ((System.ComponentModel.ISupportInitialize)(this.splitContainer2)).BeginInit();
      this.splitContainer2.Panel1.SuspendLayout();
      this.splitContainer2.Panel2.SuspendLayout();
      this.splitContainer2.SuspendLayout();
      this.contextMenuStrip1.SuspendLayout();
      this.menuStrip1.SuspendLayout();
      this.SuspendLayout();
      // 
      // currentStateView
      // 
      this.currentStateView.BackColor = System.Drawing.SystemColors.Window;
      this.currentStateView.Columns.AddRange(new System.Windows.Forms.ColumnHeader[] {
            this.name,
            this.value,
            this.prevValue});
      this.currentStateView.ContextMenuStrip = this.stateViewMenu;
      this.currentStateView.Dock = System.Windows.Forms.DockStyle.Fill;
      this.currentStateView.FullRowSelect = true;
      this.currentStateView.GridLines = true;
      this.currentStateView.HeaderStyle = System.Windows.Forms.ColumnHeaderStyle.Nonclickable;
      this.currentStateView.Location = new System.Drawing.Point(0, 0);
      this.currentStateView.MultiSelect = false;
      this.currentStateView.Name = "currentStateView";
      this.currentStateView.OwnerDraw = true;
      this.currentStateView.ShowItemToolTips = true;
      this.currentStateView.Size = new System.Drawing.Size(596, 344);
      this.currentStateView.TabIndex = 0;
      this.currentStateView.UseCompatibleStateImageBehavior = false;
      this.currentStateView.View = System.Windows.Forms.View.Details;
      this.currentStateView.ColumnWidthChanged += new System.Windows.Forms.ColumnWidthChangedEventHandler(this.listView1_ColumnWidthChanged);
      this.currentStateView.DrawColumnHeader += new System.Windows.Forms.DrawListViewColumnHeaderEventHandler(this.listView1_DrawColumnHeader);
      this.currentStateView.DrawItem += new System.Windows.Forms.DrawListViewItemEventHandler(this.listView1_DrawItem);
      this.currentStateView.SelectedIndexChanged += new System.EventHandler(this.currentStateView_SelectedIndexChanged);
      this.currentStateView.KeyDown += new System.Windows.Forms.KeyEventHandler(this.currentStateView_KeyDown);
      this.currentStateView.MouseUp += new System.Windows.Forms.MouseEventHandler(this.listView1_MouseUp);
      this.currentStateView.Resize += new System.EventHandler(this.listView1_Resize);
      // 
      // name
      // 
      this.name.Text = "Name";
      this.name.Width = 298;
      // 
      // value
      // 
      this.value.Text = "Value";
      this.value.Width = 126;
      // 
      // prevValue
      // 
      this.prevValue.Text = "Previous";
      this.prevValue.Width = 100;
      // 
      // stateViewMenu
      // 
      this.stateViewMenu.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.dummyItemToolStripMenuItem});
      this.stateViewMenu.Name = "stateViewMenu";
      this.stateViewMenu.Size = new System.Drawing.Size(145, 26);
      this.stateViewMenu.Opening += new System.ComponentModel.CancelEventHandler(this.stateViewMenu_Opening);
      // 
      // dummyItemToolStripMenuItem
      // 
      this.dummyItemToolStripMenuItem.Name = "dummyItemToolStripMenuItem";
      this.dummyItemToolStripMenuItem.Size = new System.Drawing.Size(144, 22);
      this.dummyItemToolStripMenuItem.Text = "Dummy item";
      // 
      // splitContainer1
      // 
      this.splitContainer1.Dock = System.Windows.Forms.DockStyle.Fill;
      this.splitContainer1.Location = new System.Drawing.Point(0, 24);
      this.splitContainer1.Name = "splitContainer1";
      // 
      // splitContainer1.Panel1
      // 
      this.splitContainer1.Panel1.Controls.Add(this.splitContainer2);
      // 
      // splitContainer1.Panel2
      // 
      this.splitContainer1.Panel2.Controls.Add(this.stateList);
      this.splitContainer1.Size = new System.Drawing.Size(915, 449);
      this.splitContainer1.SplitterDistance = 596;
      this.splitContainer1.TabIndex = 1;
      // 
      // splitContainer2
      // 
      this.splitContainer2.Dock = System.Windows.Forms.DockStyle.Fill;
      this.splitContainer2.Location = new System.Drawing.Point(0, 0);
      this.splitContainer2.Name = "splitContainer2";
      this.splitContainer2.Orientation = System.Windows.Forms.Orientation.Horizontal;
      // 
      // splitContainer2.Panel1
      // 
      this.splitContainer2.Panel1.Controls.Add(this.currentStateView);
      // 
      // splitContainer2.Panel2
      // 
      this.splitContainer2.Panel2.Controls.Add(this.matchesList);
      this.splitContainer2.Panel2.Controls.Add(this.linkLabel1);
      this.splitContainer2.Panel2.Controls.Add(this.label1);
      this.splitContainer2.Panel2.Controls.Add(this.textBox1);
      this.splitContainer2.Size = new System.Drawing.Size(596, 449);
      this.splitContainer2.SplitterDistance = 344;
      this.splitContainer2.TabIndex = 1;
      // 
      // matchesList
      // 
      this.matchesList.Anchor = ((System.Windows.Forms.AnchorStyles)((((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Bottom) 
            | System.Windows.Forms.AnchorStyles.Left) 
            | System.Windows.Forms.AnchorStyles.Right)));
      this.matchesList.Columns.AddRange(new System.Windows.Forms.ColumnHeader[] {
            this.columnHeader4,
            this.columnHeader5});
      this.matchesList.FullRowSelect = true;
      this.matchesList.GridLines = true;
      this.matchesList.HeaderStyle = System.Windows.Forms.ColumnHeaderStyle.None;
      this.matchesList.Location = new System.Drawing.Point(0, 29);
      this.matchesList.MultiSelect = false;
      this.matchesList.Name = "matchesList";
      this.matchesList.OwnerDraw = true;
      this.matchesList.ShowItemToolTips = true;
      this.matchesList.Size = new System.Drawing.Size(596, 72);
      this.matchesList.TabIndex = 4;
      this.matchesList.UseCompatibleStateImageBehavior = false;
      this.matchesList.View = System.Windows.Forms.View.Details;
      this.matchesList.ColumnWidthChanged += new System.Windows.Forms.ColumnWidthChangedEventHandler(this.listView1_ColumnWidthChanged);
      this.matchesList.DrawColumnHeader += new System.Windows.Forms.DrawListViewColumnHeaderEventHandler(this.listView1_DrawColumnHeader);
      this.matchesList.DrawItem += new System.Windows.Forms.DrawListViewItemEventHandler(this.listView1_DrawItem);
      this.matchesList.DoubleClick += new System.EventHandler(this.matchesList_DoubleClick);
      this.matchesList.Resize += new System.EventHandler(this.matchesList_Resize);
      // 
      // columnHeader4
      // 
      this.columnHeader4.Text = "Name";
      this.columnHeader4.Width = 300;
      // 
      // columnHeader5
      // 
      this.columnHeader5.Text = "Value";
      this.columnHeader5.Width = 250;
      // 
      // linkLabel1
      // 
      this.linkLabel1.Anchor = ((System.Windows.Forms.AnchorStyles)((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Right)));
      this.linkLabel1.AutoSize = true;
      this.linkLabel1.Location = new System.Drawing.Point(536, 5);
      this.linkLabel1.Name = "linkLabel1";
      this.linkLabel1.Size = new System.Drawing.Size(57, 13);
      this.linkLabel1.TabIndex = 3;
      this.linkLabel1.TabStop = true;
      this.linkLabel1.Text = "Show All...";
      this.linkLabel1.VisitedLinkColor = System.Drawing.Color.Blue;
      this.linkLabel1.LinkClicked += new System.Windows.Forms.LinkLabelLinkClickedEventHandler(this.linkLabel1_LinkClicked);
      // 
      // label1
      // 
      this.label1.AutoSize = true;
      this.label1.Location = new System.Drawing.Point(3, 5);
      this.label1.Name = "label1";
      this.label1.Size = new System.Drawing.Size(44, 13);
      this.label1.TabIndex = 2;
      this.label1.Text = "Search:";
      // 
      // textBox1
      // 
      this.textBox1.Anchor = ((System.Windows.Forms.AnchorStyles)((((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Bottom) 
            | System.Windows.Forms.AnchorStyles.Left) 
            | System.Windows.Forms.AnchorStyles.Right)));
      this.textBox1.Location = new System.Drawing.Point(53, 3);
      this.textBox1.Name = "textBox1";
      this.textBox1.Size = new System.Drawing.Size(477, 20);
      this.textBox1.TabIndex = 1;
      this.textBox1.TextChanged += new System.EventHandler(this.textBox1_TextChanged);
      // 
      // stateList
      // 
      this.stateList.Columns.AddRange(new System.Windows.Forms.ColumnHeader[] {
            this.columnHeader3,
            this.columnHeader1,
            this.columnHeader2});
      this.stateList.ContextMenuStrip = this.contextMenuStrip1;
      this.stateList.Dock = System.Windows.Forms.DockStyle.Fill;
      this.stateList.FullRowSelect = true;
      this.stateList.GridLines = true;
      this.stateList.HeaderStyle = System.Windows.Forms.ColumnHeaderStyle.Nonclickable;
      this.stateList.Location = new System.Drawing.Point(0, 0);
      this.stateList.MultiSelect = false;
      this.stateList.Name = "stateList";
      this.stateList.ShowItemToolTips = true;
      this.stateList.Size = new System.Drawing.Size(315, 449);
      this.stateList.TabIndex = 0;
      this.stateList.UseCompatibleStateImageBehavior = false;
      this.stateList.View = System.Windows.Forms.View.Details;
      this.stateList.SelectedIndexChanged += new System.EventHandler(this.stateList_SelectedIndexChanged);
      this.stateList.DoubleClick += new System.EventHandler(this.stateList_DoubleClick);
      // 
      // columnHeader3
      // 
      this.columnHeader3.Text = "#";
      this.columnHeader3.Width = 22;
      // 
      // columnHeader1
      // 
      this.columnHeader1.Text = "State";
      this.columnHeader1.Width = 169;
      // 
      // columnHeader2
      // 
      this.columnHeader2.Text = "Value";
      this.columnHeader2.Width = 116;
      // 
      // contextMenuStrip1
      // 
      this.contextMenuStrip1.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.showSourceToolStripMenuItem});
      this.contextMenuStrip1.Name = "contextMenuStrip1";
      this.contextMenuStrip1.Size = new System.Drawing.Size(142, 26);
      // 
      // showSourceToolStripMenuItem
      // 
      this.showSourceToolStripMenuItem.Name = "showSourceToolStripMenuItem";
      this.showSourceToolStripMenuItem.Size = new System.Drawing.Size(141, 22);
      this.showSourceToolStripMenuItem.Text = "Show source";
      this.showSourceToolStripMenuItem.Click += new System.EventHandler(this.showSourceToolStripMenuItem_Click);
      // 
      // menuStrip1
      // 
      this.menuStrip1.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.fileToolStripMenuItem,
            this.viewToolStripMenuItem,
            this.modelsToolStripMenuItem});
      this.menuStrip1.Location = new System.Drawing.Point(0, 0);
      this.menuStrip1.Name = "menuStrip1";
      this.menuStrip1.Size = new System.Drawing.Size(915, 24);
      this.menuStrip1.TabIndex = 1;
      this.menuStrip1.Text = "menuStrip1";
      // 
      // fileToolStripMenuItem
      // 
      this.fileToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.openModelMenuItem,
            this.toolStripSeparator1,
            this.reloadModelFileToolStripMenuItem,
            this.exitToolStripMenuItem});
      this.fileToolStripMenuItem.Name = "fileToolStripMenuItem";
      this.fileToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Alt | System.Windows.Forms.Keys.F4)));
      this.fileToolStripMenuItem.Size = new System.Drawing.Size(37, 20);
      this.fileToolStripMenuItem.Text = "&File";
      // 
      // openModelMenuItem
      // 
      this.openModelMenuItem.Name = "openModelMenuItem";
      this.openModelMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.O)));
      this.openModelMenuItem.Size = new System.Drawing.Size(211, 22);
      this.openModelMenuItem.Text = "&Open model file...";
      this.openModelMenuItem.Click += new System.EventHandler(this.openModelMenuItem_Click);
      // 
      // toolStripSeparator1
      // 
      this.toolStripSeparator1.Name = "toolStripSeparator1";
      this.toolStripSeparator1.Size = new System.Drawing.Size(208, 6);
      // 
      // reloadModelFileToolStripMenuItem
      // 
      this.reloadModelFileToolStripMenuItem.Name = "reloadModelFileToolStripMenuItem";
      this.reloadModelFileToolStripMenuItem.ShortcutKeys = System.Windows.Forms.Keys.F5;
      this.reloadModelFileToolStripMenuItem.Size = new System.Drawing.Size(211, 22);
      this.reloadModelFileToolStripMenuItem.Text = "&Reload model file";
      this.reloadModelFileToolStripMenuItem.Click += new System.EventHandler(this.reloadModelFileToolStripMenuItem_Click);
      // 
      // exitToolStripMenuItem
      // 
      this.exitToolStripMenuItem.Name = "exitToolStripMenuItem";
      this.exitToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Alt | System.Windows.Forms.Keys.F4)));
      this.exitToolStripMenuItem.Size = new System.Drawing.Size(211, 22);
      this.exitToolStripMenuItem.Text = "&Exit";
      this.exitToolStripMenuItem.Click += new System.EventHandler(this.exitToolStripMenuItem_Click);
      // 
      // viewToolStripMenuItem
      // 
      this.viewToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.normalToolStripMenuItem,
            this.expertToolStripMenuItem,
            this.everythingToolStripMenuItem,
            this.includeTheKitchenSinkToolStripMenuItem,
            this.toolStripMenuItem1,
            this.debugToolStripMenuItem,
            this.largeFontToolStripMenuItem});
      this.viewToolStripMenuItem.Name = "viewToolStripMenuItem";
      this.viewToolStripMenuItem.Size = new System.Drawing.Size(44, 20);
      this.viewToolStripMenuItem.Text = "&View";
      // 
      // normalToolStripMenuItem
      // 
      this.normalToolStripMenuItem.Name = "normalToolStripMenuItem";
      this.normalToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.N)));
      this.normalToolStripMenuItem.Size = new System.Drawing.Size(240, 22);
      this.normalToolStripMenuItem.Text = "&Normal";
      this.normalToolStripMenuItem.Click += new System.EventHandler(this.normalToolStripMenuItem_Click);
      // 
      // expertToolStripMenuItem
      // 
      this.expertToolStripMenuItem.Checked = true;
      this.expertToolStripMenuItem.CheckState = System.Windows.Forms.CheckState.Checked;
      this.expertToolStripMenuItem.Name = "expertToolStripMenuItem";
      this.expertToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.X)));
      this.expertToolStripMenuItem.Size = new System.Drawing.Size(240, 22);
      this.expertToolStripMenuItem.Text = "E&xpert";
      this.expertToolStripMenuItem.Click += new System.EventHandler(this.normalToolStripMenuItem_Click);
      // 
      // everythingToolStripMenuItem
      // 
      this.everythingToolStripMenuItem.Name = "everythingToolStripMenuItem";
      this.everythingToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.E)));
      this.everythingToolStripMenuItem.Size = new System.Drawing.Size(240, 22);
      this.everythingToolStripMenuItem.Text = "&Everything";
      this.everythingToolStripMenuItem.Click += new System.EventHandler(this.normalToolStripMenuItem_Click);
      // 
      // includeTheKitchenSinkToolStripMenuItem
      // 
      this.includeTheKitchenSinkToolStripMenuItem.Name = "includeTheKitchenSinkToolStripMenuItem";
      this.includeTheKitchenSinkToolStripMenuItem.ShortcutKeys = ((System.Windows.Forms.Keys)((System.Windows.Forms.Keys.Control | System.Windows.Forms.Keys.K)));
      this.includeTheKitchenSinkToolStripMenuItem.Size = new System.Drawing.Size(240, 22);
      this.includeTheKitchenSinkToolStripMenuItem.Text = "&Include the kitchen sink";
      this.includeTheKitchenSinkToolStripMenuItem.Click += new System.EventHandler(this.normalToolStripMenuItem_Click);
      // 
      // toolStripMenuItem1
      // 
      this.toolStripMenuItem1.Name = "toolStripMenuItem1";
      this.toolStripMenuItem1.Size = new System.Drawing.Size(237, 6);
      // 
      // debugToolStripMenuItem
      // 
      this.debugToolStripMenuItem.Name = "debugToolStripMenuItem";
      this.debugToolStripMenuItem.Size = new System.Drawing.Size(240, 22);
      this.debugToolStripMenuItem.Text = "Debug";
      this.debugToolStripMenuItem.Click += new System.EventHandler(this.debugToolStripMenuItem_Click);
      // 
      // largeFontToolStripMenuItem
      // 
      this.largeFontToolStripMenuItem.Name = "largeFontToolStripMenuItem";
      this.largeFontToolStripMenuItem.Size = new System.Drawing.Size(240, 22);
      this.largeFontToolStripMenuItem.Text = "Large font";
      this.largeFontToolStripMenuItem.Click += new System.EventHandler(this.largeFontToolStripMenuItem_Click);
      // 
      // modelsToolStripMenuItem
      // 
      this.modelsToolStripMenuItem.Name = "modelsToolStripMenuItem";
      this.modelsToolStripMenuItem.Size = new System.Drawing.Size(58, 20);
      this.modelsToolStripMenuItem.Text = "&Models";
      // 
      // openModelFileDialog
      // 
      this.openModelFileDialog.Filter = "Model files (*.model)|*.model|All files (*.*)|*.*";
      this.openModelFileDialog.Title = "Open model file";
      // 
      // Main
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(915, 473);
      this.Controls.Add(this.splitContainer1);
      this.Controls.Add(this.menuStrip1);
      this.Icon = ((System.Drawing.Icon)(resources.GetObject("$this.Icon")));
      this.Name = "Main";
      this.Text = "Boogie Verification Debugger";
      this.Load += new System.EventHandler(this.Main_Load);
      this.stateViewMenu.ResumeLayout(false);
      this.splitContainer1.Panel1.ResumeLayout(false);
      this.splitContainer1.Panel2.ResumeLayout(false);
      ((System.ComponentModel.ISupportInitialize)(this.splitContainer1)).EndInit();
      this.splitContainer1.ResumeLayout(false);
      this.splitContainer2.Panel1.ResumeLayout(false);
      this.splitContainer2.Panel2.ResumeLayout(false);
      this.splitContainer2.Panel2.PerformLayout();
      ((System.ComponentModel.ISupportInitialize)(this.splitContainer2)).EndInit();
      this.splitContainer2.ResumeLayout(false);
      this.contextMenuStrip1.ResumeLayout(false);
      this.menuStrip1.ResumeLayout(false);
      this.menuStrip1.PerformLayout();
      this.ResumeLayout(false);
      this.PerformLayout();

    }

    #endregion

    private System.Windows.Forms.ListView currentStateView;
    private System.Windows.Forms.ColumnHeader name;
    private System.Windows.Forms.ColumnHeader value;
    private System.Windows.Forms.SplitContainer splitContainer1;
    private System.Windows.Forms.ListView stateList;
    private System.Windows.Forms.ColumnHeader columnHeader1;
    private System.Windows.Forms.ColumnHeader columnHeader2;
    private System.Windows.Forms.ColumnHeader columnHeader3;
    private System.Windows.Forms.ColumnHeader prevValue;
    private System.Windows.Forms.SplitContainer splitContainer2;
    private System.Windows.Forms.ListView matchesList;
    private System.Windows.Forms.ColumnHeader columnHeader4;
    private System.Windows.Forms.ColumnHeader columnHeader5;
    private System.Windows.Forms.LinkLabel linkLabel1;
    private System.Windows.Forms.Label label1;
    private System.Windows.Forms.TextBox textBox1;
    private System.Windows.Forms.ContextMenuStrip stateViewMenu;
    private System.Windows.Forms.ToolStripMenuItem dummyItemToolStripMenuItem;
    private System.Windows.Forms.MenuStrip menuStrip1;
    private System.Windows.Forms.ToolStripMenuItem fileToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem exitToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem viewToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem normalToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem expertToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem everythingToolStripMenuItem;
    private System.Windows.Forms.ToolStripSeparator toolStripMenuItem1;
    private System.Windows.Forms.ToolStripMenuItem debugToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem modelsToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem includeTheKitchenSinkToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem reloadModelFileToolStripMenuItem;
    private System.Windows.Forms.ContextMenuStrip contextMenuStrip1;
    private System.Windows.Forms.ToolStripMenuItem showSourceToolStripMenuItem;
    private System.Windows.Forms.ToolStripMenuItem openModelMenuItem;
    private System.Windows.Forms.ToolStripSeparator toolStripSeparator1;
    private System.Windows.Forms.OpenFileDialog openModelFileDialog;
    private System.Windows.Forms.ToolStripMenuItem largeFontToolStripMenuItem;


  }
}

