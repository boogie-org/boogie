using System;
using System.Collections.Generic;
using System.Linq;
using System.Windows.Forms;

namespace Microsoft.Boogie.ModelViewer
{
  static class Program
  {
    /// <summary>
    /// The main entry point for the application.
    /// </summary>
    [STAThread]
    static void Main()
    {
      Application.EnableVisualStyles();
      Application.SetCompatibleTextRenderingDefault(false);
      try
      {
        Application.Run(new Main(System.Environment.GetCommandLineArgs()));
      }
      catch (Exception exc)
      {
        MessageBox.Show(exc.Message, "Model Viewer Error", MessageBoxButtons.OK, MessageBoxIcon.Error, MessageBoxDefaultButton.Button1);
      }
    }
  }
}
