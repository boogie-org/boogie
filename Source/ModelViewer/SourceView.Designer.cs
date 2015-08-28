namespace Microsoft.Boogie.ModelViewer
{
  partial class SourceView
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
      this.richTextBox1 = new System.Windows.Forms.RichTextBox();
      this.SuspendLayout();
      // 
      // richTextBox1
      // 
      this.richTextBox1.DetectUrls = false;
      this.richTextBox1.Dock = System.Windows.Forms.DockStyle.Fill;
      this.richTextBox1.Font = new System.Drawing.Font("Lucida Sans Typewriter", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
      this.richTextBox1.HideSelection = false;
      this.richTextBox1.Location = new System.Drawing.Point(0, 0);
      this.richTextBox1.Name = "richTextBox1";
      this.richTextBox1.ReadOnly = true;
      this.richTextBox1.Size = new System.Drawing.Size(715, 582);
      this.richTextBox1.TabIndex = 0;
      this.richTextBox1.Text = "#include <vcc.h>\n\nint main()\n{\n\\foo\n}";
      this.richTextBox1.WordWrap = false;
      // 
      // SourceView
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(715, 582);
      this.Controls.Add(this.richTextBox1);
      this.Name = "SourceView";
      this.Text = "SourceView";
      this.ResumeLayout(false);

    }

    #endregion

    private System.Windows.Forms.RichTextBox richTextBox1;
  }
}