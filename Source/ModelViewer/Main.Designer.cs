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
      this.currentStateView = new System.Windows.Forms.ListView();
      this.name = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.value = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.splitContainer1 = new System.Windows.Forms.SplitContainer();
      this.stateList = new System.Windows.Forms.ListView();
      this.columnHeader1 = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      this.columnHeader2 = ((System.Windows.Forms.ColumnHeader)(new System.Windows.Forms.ColumnHeader()));
      ((System.ComponentModel.ISupportInitialize)(this.splitContainer1)).BeginInit();
      this.splitContainer1.Panel1.SuspendLayout();
      this.splitContainer1.Panel2.SuspendLayout();
      this.splitContainer1.SuspendLayout();
      this.SuspendLayout();
      // 
      // currentStateView
      // 
      this.currentStateView.Columns.AddRange(new System.Windows.Forms.ColumnHeader[] {
            this.name,
            this.value});
      this.currentStateView.Dock = System.Windows.Forms.DockStyle.Fill;
      this.currentStateView.FullRowSelect = true;
      this.currentStateView.GridLines = true;
      this.currentStateView.HeaderStyle = System.Windows.Forms.ColumnHeaderStyle.Nonclickable;
      this.currentStateView.Location = new System.Drawing.Point(0, 0);
      this.currentStateView.MultiSelect = false;
      this.currentStateView.Name = "currentStateView";
      this.currentStateView.OwnerDraw = true;
      this.currentStateView.ShowItemToolTips = true;
      this.currentStateView.Size = new System.Drawing.Size(614, 706);
      this.currentStateView.TabIndex = 0;
      this.currentStateView.UseCompatibleStateImageBehavior = false;
      this.currentStateView.View = System.Windows.Forms.View.Details;
      this.currentStateView.ColumnWidthChanged += new System.Windows.Forms.ColumnWidthChangedEventHandler(this.listView1_ColumnWidthChanged);
      this.currentStateView.DrawColumnHeader += new System.Windows.Forms.DrawListViewColumnHeaderEventHandler(this.listView1_DrawColumnHeader);
      this.currentStateView.DrawItem += new System.Windows.Forms.DrawListViewItemEventHandler(this.listView1_DrawItem);
      this.currentStateView.DrawSubItem += new System.Windows.Forms.DrawListViewSubItemEventHandler(this.listView1_DrawSubItem);
      this.currentStateView.SelectedIndexChanged += new System.EventHandler(this.currentStateView_SelectedIndexChanged);
      this.currentStateView.MouseMove += new System.Windows.Forms.MouseEventHandler(this.listView1_MouseMove);
      this.currentStateView.MouseUp += new System.Windows.Forms.MouseEventHandler(this.listView1_MouseUp);
      this.currentStateView.Resize += new System.EventHandler(this.listView1_Resize);
      // 
      // name
      // 
      this.name.Text = "Name";
      this.name.Width = 174;
      // 
      // value
      // 
      this.value.Text = "Value";
      this.value.Width = 394;
      // 
      // splitContainer1
      // 
      this.splitContainer1.Dock = System.Windows.Forms.DockStyle.Fill;
      this.splitContainer1.Location = new System.Drawing.Point(0, 0);
      this.splitContainer1.Name = "splitContainer1";
      // 
      // splitContainer1.Panel1
      // 
      this.splitContainer1.Panel1.Controls.Add(this.currentStateView);
      // 
      // splitContainer1.Panel2
      // 
      this.splitContainer1.Panel2.Controls.Add(this.stateList);
      this.splitContainer1.Size = new System.Drawing.Size(875, 706);
      this.splitContainer1.SplitterDistance = 614;
      this.splitContainer1.TabIndex = 1;
      // 
      // stateList
      // 
      this.stateList.Columns.AddRange(new System.Windows.Forms.ColumnHeader[] {
            this.columnHeader1,
            this.columnHeader2});
      this.stateList.Dock = System.Windows.Forms.DockStyle.Fill;
      this.stateList.FullRowSelect = true;
      this.stateList.GridLines = true;
      this.stateList.HeaderStyle = System.Windows.Forms.ColumnHeaderStyle.Nonclickable;
      this.stateList.Location = new System.Drawing.Point(0, 0);
      this.stateList.MultiSelect = false;
      this.stateList.Name = "stateList";
      this.stateList.ShowItemToolTips = true;
      this.stateList.Size = new System.Drawing.Size(257, 706);
      this.stateList.TabIndex = 0;
      this.stateList.UseCompatibleStateImageBehavior = false;
      this.stateList.View = System.Windows.Forms.View.Details;
      this.stateList.SelectedIndexChanged += new System.EventHandler(this.stateList_SelectedIndexChanged);
      // 
      // columnHeader1
      // 
      this.columnHeader1.Text = "State";
      this.columnHeader1.Width = 112;
      // 
      // columnHeader2
      // 
      this.columnHeader2.Text = "Value";
      this.columnHeader2.Width = 128;
      // 
      // Main
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(875, 706);
      this.Controls.Add(this.splitContainer1);
      this.Name = "Main";
      this.Text = "Boogie Model Viewer";
      this.splitContainer1.Panel1.ResumeLayout(false);
      this.splitContainer1.Panel2.ResumeLayout(false);
      ((System.ComponentModel.ISupportInitialize)(this.splitContainer1)).EndInit();
      this.splitContainer1.ResumeLayout(false);
      this.ResumeLayout(false);

    }

    #endregion

    private System.Windows.Forms.ListView currentStateView;
    private System.Windows.Forms.ColumnHeader name;
    private System.Windows.Forms.ColumnHeader value;
    private System.Windows.Forms.SplitContainer splitContainer1;
    private System.Windows.Forms.ListView stateList;
    private System.Windows.Forms.ColumnHeader columnHeader1;
    private System.Windows.Forms.ColumnHeader columnHeader2;


  }
}

