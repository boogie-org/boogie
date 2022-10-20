using System;

namespace Microsoft.Boogie.SMTLib
{
  public static class Z3
  {
    // Do not access this field directly! Use method GetVersion.
    private static Version Z3Version = null;

    public static Version GetVersion(string proverPath)
    {
      if (Z3Version == null)
      {
        var proc = new System.Diagnostics.Process();
        proc.StartInfo.FileName = proverPath;
        proc.StartInfo.Arguments = "--version";
        proc.StartInfo.RedirectStandardOutput = true;
        proc.StartInfo.RedirectStandardError = true;
        proc.StartInfo.UseShellExecute = false;
        proc.StartInfo.CreateNoWindow = true;
        proc.Start();
        string answer = proc.StandardOutput.ReadToEnd();
        proc.WaitForExit();
        if (proc.ExitCode == 0)
        {
          var firstdot = answer.IndexOf('.');
          if (firstdot >= 0)
          {
            var seconddot = answer.IndexOf('.', firstdot + 1);
            if (seconddot >= firstdot + 1)
            {
              var spacebeforefirstdot = answer.LastIndexOf(' ', firstdot);
              if (spacebeforefirstdot >= 0)
              {
                var spaceafterseconddot = answer.IndexOf(' ', seconddot + 1);
                if (spaceafterseconddot >= 0)
                {
                  var majorstr = answer.Substring(spacebeforefirstdot, firstdot - spacebeforefirstdot);
                  var minorstr = answer.Substring(firstdot + 1, seconddot - firstdot - 1);
                  var patchstr = answer.Substring(seconddot + 1, spaceafterseconddot - seconddot - 1);
                  Z3Version = new Version(Convert.ToInt32(majorstr), Convert.ToInt32(minorstr),
                    Convert.ToInt32(patchstr));
                  return Z3Version;
                }
              }
            }
          }
        }
      }

      throw new ProverException("Cannot obtain Z3 version number");
    }

    public static string TimeoutOption = "timeout";

    public static string RlimitOption = "rlimit";

    public static string SmtRandomSeed = "smt.random_seed";
    public static string SatRandomSeed = "sat.random_seed";
    
    public static void SetDefaultOptions(SMTLibSolverOptions options)
    {
      options.AddWeakSmtOption("smt.mbqi", "false"); // default: true

      // {:captureState} does not work with compressed models
      options.AddWeakSmtOption("model.compact", "false"); // default: false
      options.AddWeakSmtOption("model.v2", "true"); // default: false

      // Make sure we get something that is parsable as a bitvector
      options.AddWeakSmtOption("pp.bv_literals", "false"); // default: true
    }
  }
}
