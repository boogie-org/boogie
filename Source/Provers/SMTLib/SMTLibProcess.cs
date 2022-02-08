using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;
using System.Threading;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibProcess : SMTLibSolver
  {
    readonly Process prover;
    readonly Inspector inspector;
    readonly SMTLibProverOptions options;
    readonly Queue<string> proverOutput = new();
    readonly Queue<string> proverErrors = new();
    readonly TextWriter toProver;
    readonly int smtProcessId;
    static int smtProcessIdSeq = 0;
    ConsoleCancelEventHandler cancelEvent;

    public SMTLibProcess(SMTLibOptions libOptions, SMTLibProverOptions options)
    {
      this.options = options;
      smtProcessId = smtProcessIdSeq++;

      var psi = new ProcessStartInfo(options.ExecutablePath(), options.SolverArguments.Concat(" "))
      {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardInput = true,
        RedirectStandardOutput = true,
        RedirectStandardError = true
      };

      if (options.Inspector != null)
      {
        this.inspector = new Inspector(options);
      }

      if (libOptions.RunningBoogieFromCommandLine)
      {
        cancelEvent = ControlCHandler;
        Console.CancelKeyPress += cancelEvent;
      }

      if (options.Verbosity >= 1)
      {
        Console.WriteLine("[SMT-{0}] Starting {1} {2}", smtProcessId, psi.FileName, psi.Arguments);
      }

      try
      {
        prover = new Process();
        prover.StartInfo = psi;
        prover.ErrorDataReceived += prover_ErrorDataReceived;
        prover.OutputDataReceived += prover_OutputDataReceived;
        prover.Start();
        toProver = prover.StandardInput;
        prover.BeginErrorReadLine();
        prover.BeginOutputReadLine();
      }
      catch (System.ComponentModel.Win32Exception e)
      {
        throw new ProverException(string.Format("Unable to start the process {0}: {1}", psi.FileName, e.Message));
      }
    }

    [NoDefaultContract] // important, since we have no idea what state the object might be in when this handler is invoked
    void ControlCHandler(object o, ConsoleCancelEventArgs a)
    {
      if (prover != null)
      {
        TerminateProver();
      }
    }

    private void TerminateProver(Int32 timeout = 2000)
    {
      try
      {
        // Let the prover know that we're done sending input.
        prover.StandardInput.Close();

        // Give it a chance to exit cleanly (e.g. to flush buffers)
        if (!prover.WaitForExit(timeout))
        {
          prover.Kill();
        }
      }
      catch
      {
        /* Swallow errors */
      }
    }

    public override void Send(string cmd)
    {
      if (options.Verbosity >= 2)
      {
        var log = cmd;
        if (log.Length > 50)
        {
          log = log.Substring(0, 50) + "...";
        }

        log = log.Replace("\r", "").Replace("\n", " ");
        Console.WriteLine("[SMT-INP-{0}] {1}", smtProcessId, log);
      }

      toProver.WriteLine(cmd);
    }

    internal Inspector Inspector
    {
      get { return inspector; }
    }

    public override SExpr GetProverResponse()
    {
      toProver.Flush();

      while (true)
      {
        var exprs = ParseSExprs(true).ToArray();
        Contract.Assert(exprs.Length <= 1);
        if (exprs.Length == 0)
        {
          return null;
        }

        var resp = exprs[0];
        if (resp.Name == "error")
        {
          if (resp.Arguments.Length == 1 && resp.Arguments[0].IsId)
          {
            if (resp.Arguments[0].Name.Contains("max. resource limit exceeded"))
            {
              return resp;
            }
            else {
              HandleError(resp.Arguments[0].Name);
              return null;
            }
          }
          else {
            HandleError(resp.ToString());
            return null;
          }
        }
        else if (resp.Name == "progress")
        {
          if (inspector != null)
          {
            var sb = new StringBuilder();
            foreach (var a in resp.Arguments)
            {
              if (a.Name == "labels")
              {
                sb.Append("STATS LABELS");
                foreach (var x in a.Arguments)
                {
                  sb.Append(" ").Append(x.Name);
                }
              }
              else if (a.Name.StartsWith(":"))
              {
                sb.Append("STATS NAMED_VALUES ").Append(a.Name);
                foreach (var x in a.Arguments)
                {
                  sb.Append(" ").Append(x.Name);
                }
              }
              else
              {
                continue;
              }

              inspector.StatsLine(sb.ToString());
              sb.Clear();
            }
          }
        }
        else if (resp.Name == "unsupported")
        {
          // Skip -- this may be a benign "unsupported" from a previous command.
          // Of course, this is suboptimal.  We should really be using
          // print-success to identify the errant command and determine whether
          // the response is benign.
        }
        else
        {
          return resp;
        }
      }
    }

    public override void NewProblem(string descriptiveName)
    {
      Inspector?.NewProblem(descriptiveName);
    }


    // NOTE: this field is used by Corral.
    // https://github.com/boogie-org/corral/blob/master/source/Driver.cs
    public static System.TimeSpan TotalUserTime = System.TimeSpan.Zero;

    public override void Close()
    {
      try
      {
        TotalUserTime += prover.UserProcessorTime;
      }
      catch (Exception e)
      {
        if (options.Verbosity >= 1)
        {
          Console.Error.WriteLine("Warning: prover time not incremented due to {0}", e.GetType());
        }
      }

      TerminateProver();
      DisposeProver();
    }

    public override event Action<string> ErrorHandler;
    int errorCnt;

    protected override void HandleError(string msg)
    {
      if (options.Verbosity >= 2)
      {
        Console.WriteLine("[SMT-ERR-{0}] Handling error: {1}", smtProcessId, msg);
      }

      ErrorHandler?.Invoke(msg);
    }

    #region SExpr parsing

    int linePos;
    string currLine;

    char SkipWs()
    {
      while (true)
      {
        if (currLine == null)
        {
          currLine = ReadProver();
          if (currLine == null)
          {
            return '\0';
          }
        }


        while (linePos < currLine.Length && char.IsWhiteSpace(currLine[linePos]))
        {
          linePos++;
        }

        if (linePos < currLine.Length && currLine[linePos] != ';')
        {
          return currLine[linePos];
        }
        else
        {
          currLine = null;
          linePos = 0;
        }
      }
    }

    void Shift()
    {
      linePos++;
    }

    string ParseId()
    {
      var sb = new StringBuilder();

      var beg = SkipWs();

      var quoted = beg == '"' || beg == '|';
      if (quoted)
      {
        Shift();
      }

      while (true)
      {
        if (linePos >= currLine.Length)
        {
          if (quoted)
          {
            do
            {
              sb.Append("\n");
              currLine = ReadProver();
            } while (currLine == "");
            if (currLine == null)
            {
              break;
            }

            linePos = 0;
          }
          else
          {
            break;
          }
        }

        var c = currLine[linePos++];
        if (quoted && c == beg)
        {
          break;
        }

        if (!quoted && (char.IsWhiteSpace(c) || c == '(' || c == ')'))
        {
          linePos--;
          break;
        }

        if (quoted && c == '\\' && linePos < currLine.Length && currLine[linePos] == '"')
        {
          sb.Append('"');
          linePos++;
          continue;
        }

        sb.Append(c);
      }

      return sb.ToString();
    }

    void ParseError(string msg)
    {
      HandleError("Error parsing prover output: " + msg);
    }

    IEnumerable<SExpr> ParseSExprs(bool top)
    {
      while (true)
      {
        var c = SkipWs();
        if (c == '\0')
        {
          break;
        }

        if (c == ')')
        {
          if (top)
          {
            ParseError("stray ')'");
          }

          break;
        }

        string id;

        if (c == '(')
        {
          Shift();
          c = SkipWs();
          if (c == '\0')
          {
            ParseError("expecting something after '('");
            break;
          }
          else if (c == '(')
          {
            id = "";
          }
          else
          {
            id = ParseId();
          }

          var args = ParseSExprs(false).ToArray();

          c = SkipWs();
          if (c == ')')
          {
            Shift();
          }
          else
          {
            ParseError("unclosed '(" + id + "'");
          }

          yield return new SExpr(id, args);
        }
        else
        {
          id = ParseId();
          yield return new SExpr(id);
        }

        if (top)
        {
          break;
        }
      }
    }

    #endregion

    #region handling input from the prover

    string ReadProver()
    {
      string error = null;
      while (true)
      {
        if (error != null)
        {
          HandleError(error);
          errorCnt++;
          error = null;
        }

        lock (this)
        {
          while (proverOutput.Count == 0 && proverErrors.Count == 0 && !prover.HasExited)
          {
            Monitor.Wait(this, 100);
          }

          if (proverErrors.Count > 0)
          {
            error = proverErrors.Dequeue();
            continue;
          }

          if (proverOutput.Count > 0)
          {
            return proverOutput.Dequeue();
          }

          if (prover.HasExited)
          {
            DisposeProver();
            return null;
          }
        }
      }
    }

    void DisposeProver()
    {
      if (cancelEvent != null)
      {
        Console.CancelKeyPress -= cancelEvent;
        cancelEvent = null;
      }
    }

    void prover_OutputDataReceived(object sender, DataReceivedEventArgs e)
    {
      lock (this)
      {
        if (e.Data != null)
        {
          if (options.Verbosity >= 2 || (options.Verbosity >= 1 && !e.Data.StartsWith("(:name ")))
          {
            Console.WriteLine("[SMT-OUT-{0}] {1}", smtProcessId, e.Data);
          }

          proverOutput.Enqueue(e.Data);
          Monitor.Pulse(this);
        }
      }
    }

    void prover_ErrorDataReceived(object sender, DataReceivedEventArgs e)
    {
      lock (this)
      {
        if (e.Data != null)
        {
          if (options.Verbosity >= 1)
          {
            Console.WriteLine("[SMT-ERR-{0}] {1}", smtProcessId, e.Data);
          }

          proverErrors.Enqueue(e.Data);
          Monitor.Pulse(this);
        }
      }
    }

    #endregion
  }
}
