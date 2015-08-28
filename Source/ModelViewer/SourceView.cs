using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;

namespace Microsoft.Boogie.ModelViewer
{
  public partial class SourceView : Form
  {
    public bool largeFont;
    bool prevLarge;

    public SourceView()
    {
      InitializeComponent();
      //richTextBox1.Font = new Font(richTextBox1.Font.FontFamily, fontSize, richTextBox1.Font.Unit);
      richTextBox1.BackColor = Color.White;
    }

    string prevRtf;

    string prefix =
        @"{\rtf1\ansi\ansicpg1252\deff0\deflang1033{\fonttbl{\f0\fnil\fcharset0 Lucida Sans Typewriter;}}\r\n" +
        @"{\colortbl;\red0\green0\blue0;\red255\green0\blue0;\red0\green255\blue0;\red255\green255\blue0;\red0\green0\blue0;\red160\green160\blue160;}" +
        @"\viewkind4\uc1\pard\f0";

    internal void SetSourceLocation(SourceViewState r)
    {      
      if (r.RichTextContent != prevRtf || prevLarge != largeFont) {
        richTextBox1.Rtf = prefix + (largeFont ? "\\fs30 " : "\\fs17 ") + r.RichTextContent + "\r\n}\r\n";
        prevRtf = r.RichTextContent;
        prevLarge = largeFont;
      }

      richTextBox1.Select(r.Location, 9);

      this.Text = r.Header;      
      this.Show();
    }

    protected override void OnClosing(CancelEventArgs e)
    {
      base.OnClosing(e);
      e.Cancel = true;
      Hide();
    }
  }
}
