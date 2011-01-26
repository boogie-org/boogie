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
    public SourceView()
    {
      InitializeComponent();
    }

    string prevRtf;

    string prefix =
        @"{\rtf1\ansi\ansicpg1252\deff0\deflang1033{\fonttbl{\f0\fnil\fcharset0 Lucida Sans Typewriter;}}\r\n" +
        @"{\colortbl;\red0\green0\blue0;\red255\green0\blue0;\red0\green255\blue0;\red0\green0\blue255;\red255\green255\blue255;\red100\green100\blue100;}" +
        @"\viewkind4\uc1\pard\f0\fs17 ";

    internal void SetSourceLocation(SourceLocation r)
    {      
      if (r.RichTextContent != prevRtf) {
        richTextBox1.Rtf = prefix + r.RichTextContent + "\r\n}\r\n";
        prevRtf = r.RichTextContent;
      }

      richTextBox1.Select(r.Location, 6);

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
