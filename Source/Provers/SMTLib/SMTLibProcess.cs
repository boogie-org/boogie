using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibProcess : SMTLibSolver {
    private readonly Process solver;
    private readonly SMTLibSolverOptions options;
    // Used to synchronise between solver output and the request currently being processed.
    private readonly AsyncQueue<string> solverOutput = new();
    // Used to synchronise between requests into this class.
    private readonly SemaphoreSlim asyncLock = new(1);
    private TextWriter toProver;
    private readonly int smtProcessId;
    private static int smtProcessIdSeq = 0;
    private ConsoleCancelEventHandler cancelEvent;

    public SMTLibProcess(SMTLibOptions libOptions, SMTLibSolverOptions options)
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
        this.Inspector = new Inspector(options);
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
        solver = new Process();
        solver.StartInfo = psi;
        solver.ErrorDataReceived += SolverErrorDataReceived;
        solver.OutputDataReceived += SolverOutputDataReceived;
        solver.Exited += SolverExited;
        solver.Start();
        toProver = solver.StandardInput;
        solver.BeginErrorReadLine();
        solver.BeginOutputReadLine();
      }
      catch (System.ComponentModel.Win32Exception e)
      {
        throw new ProverException(string.Format("Unable to start the process {0}: {1}", psi.FileName, e.Message));
      }
    }

    private void SolverExited(object sender, EventArgs e)
    {
      lock (this) {
        while (outputReceivers.TryDequeue(out var source)) {
          source.SetResult(null);
        }
      }

      DisposeProver();
    }

    [NoDefaultContract] // important, since we have no idea what state the object might be in when this handler is invoked
    void ControlCHandler(object o, ConsoleCancelEventArgs a)
    {
      if (solver != null)
      {
        TerminateProver();
      }
    }

    private void IndicateEndOfInput()
    {
      solver.StandardInput.Close();
      toProver = null;
    }

    private void TerminateProver(Int32 timeout = 2000)
    {
      try
      {
        // Let the prover know that we're done sending input.
        IndicateEndOfInput();

        // Give it a chance to exit cleanly (e.g. to flush buffers)
        if (!solver.WaitForExit(timeout))
        {
          solver.Kill();
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
      toProver.Flush();
    }

    // TODO, consider building in a PingPong to catch a missing response.
    public override async Task<SExpr> SendRequest(string request) {
      SExpr previousResponse = null;
      try {
        await asyncLock.WaitAsync();
        Send(request);
        Send(PingRequest);
        while (true) {
          var response = await GetProverResponse();
          if (IsPong(response)) {
            if (previousResponse == null) {
              throw new Exception("Request returned no response");
            }
            return previousResponse;
          }
          previousResponse = response;
        }
      }
      finally {
        asyncLock.Release();
      }
    }

    public override async Task PingPong() {
      try {
        await asyncLock.WaitAsync();
        Send(PingRequest);
        while (true) {
          var response = await GetProverResponse();
          if (response == null)
          {
            throw new ProverDiedException();
          }

          if (IsPong(response))
          {
            return;
          }

          HandleError("Invalid PING response from the prover: " + response.ToString());
        }
      }
      finally {
        asyncLock.Release();
      }
    }

    public override async Task<IReadOnlyList<SExpr>> SendRequestsAndCloseInput(IReadOnlyList<string> requests) {
      try {
        await asyncLock.WaitAsync();
        var result = new List<SExpr>();
        foreach (var request in requests) {
          Send(request);
        }
        IndicateEndOfInput();
        foreach (var request in requests) {
          var response = await GetProverResponse();
          if (response.Name.Equals("timeout")) {
            throw new TimeoutException();
          }
          result.Add(response);
        }

        return result;
      }
      finally {
        asyncLock.Release();
      }
    }

    private Inspector Inspector { get; }

    private async Task<SExpr> GetProverResponse()
    {
      if (toProver != null) {
        await toProver.FlushAsync();
      }

      while (true) {
        var exprs = await ParseSExprs(true).ToListAsync();
        Contract.Assert(exprs.Count <= 1);
        if (exprs.Count == 0) {
          return null;
        }

        var resp = exprs[0];
        if (resp.Name == "error") {
          if (resp.Arguments.Length == 1 && resp.Arguments[0].IsId) {
            if (resp.Arguments[0].Name.Contains("max. resource limit exceeded")) {
              return resp;
            } else if (resp.Arguments[0].Name.Contains("model is not available")) {
              return null;
            } else if (resp.Arguments[0].Name.Contains("context is unsatisfiable")) {
              return null;
            } else if (resp.Arguments[0].Name.Contains("Cannot get model")) {
              return null;
            } else if (resp.Arguments[0].Name.Contains("last result wasn't unknown")) {
              return null;
            } else {
              HandleError(resp.Arguments[0].Name);
              return null;
            }
          } else {
            HandleError(resp.ToString());
            return null;
          }
        } else if (resp.Name == "progress") {
          if (Inspector != null) {
            var sb = new StringBuilder();
            foreach (var a in resp.Arguments) {
              if (a.Name == "labels") {
                sb.Append("STATS LABELS");
                foreach (var x in a.Arguments) {
                  sb.Append(" ").Append(x.Name);
                }
              } else if (a.Name.StartsWith(":")) {
                sb.Append("STATS NAMED_VALUES ").Append(a.Name);
                foreach (var x in a.Arguments) {
                  sb.Append(" ").Append(x.Name);
                }
              } else {
                continue;
              }

              Inspector.StatsLine(sb.ToString());
              sb.Clear();
            }
          }
        } else if (resp.Name == "unsupported") {
          // Skip -- this may be a benign "unsupported" from a previous command.
          // Of course, this is suboptimal.  We should really be using
          // print-success to identify the errant command and determine whether
          // the response is benign.
        } else {
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
        TotalUserTime += solver.UserProcessorTime;
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

    private void HandleError(string msg)
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

    async Task<char> SkipWs()
    {
      while (true)
      {
        if (currLine == null)
        {
          currLine = await ReadProver();
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

    async Task<string> ParseId()
    {
      var sb = new StringBuilder();

      var begin = await SkipWs();

      var quoted = begin == '"' || begin == '|';
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
              currLine = await ReadProver();
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
        if (quoted && c == begin)
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

    async IAsyncEnumerable<SExpr> ParseSExprs(bool top)
    {
      while (true)
      {
        var c = await SkipWs();
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
          c = await SkipWs();
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
            id = await ParseId();
          }

          var args = await ParseSExprs(false).ToListAsync();

          c = await SkipWs();
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
          id = await ParseId();
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

    private readonly Queue<TaskCompletionSource<string>> outputReceivers = new();

    /// <summary>
    /// This asynchronous method can not be cancelled because prover output is not reusable
    /// so once it is expected to arrive it has to be consumed to keep the output queue free of garbage.
    /// </summary>
    Task<string> ReadProver()
    {
      return solverOutput.Dequeue(CancellationToken.None);
    }

    void DisposeProver()
    {
      if (cancelEvent != null)
      {
        Console.CancelKeyPress -= cancelEvent;
        cancelEvent = null;
      }
    }

    void SolverOutputDataReceived(object sender, DataReceivedEventArgs e)
    {
        if (e.Data == null)
        {
          return;
        }

        if (options.Verbosity >= 2 || (options.Verbosity >= 1 && !e.Data.StartsWith("(:name ")))
        {
          Console.WriteLine("[SMT-OUT-{0}] {1}", smtProcessId, e.Data);
        }

        solverOutput.Enqueue(e.Data);
    }

    void SolverErrorDataReceived(object sender, DataReceivedEventArgs e)
    {
      if (e.Data == null)
      {
        return;
      }

      lock (this) {

        if (options.Verbosity >= 1)
        {
          Console.WriteLine("[SMT-ERR-{0}] {1}", smtProcessId, e.Data);
        }

        HandleError(e.Data);
      }
    }

    #endregion
  }
}