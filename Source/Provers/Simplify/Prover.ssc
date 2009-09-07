//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Diagnostics;
using System.Collections;
using System.Collections.Generic;
using util;
using Microsoft.Contracts;
using Microsoft.Boogie;

// Simplified interface to an external prover like Simplify or the z3 process, taken from Bird.
namespace Microsoft.Boogie.Simplify
{
  /// <summary>
  /// An interface to Simplify theorem prover.
  /// </summary>
  public abstract class ProverProcess 
  {
    [Rep]
    protected readonly Process! simplify;
    
    [Rep] readonly TextReader! fromSimplify;
    [Rep] readonly TextWriter! toSimplify;
    [Rep] readonly TextReader! fromStdError;

    protected bool readTimedOut;
    
    int nFormulasChecked = 0;
    public int NumFormulasChecked {
      get { return nFormulasChecked; }
    }
    
    // Note: In the Everett build (.NET framework < 2.0), Process.PeakVirtualMemorySize64
    // is not defined, but rather a version that returns an 'int' rather than a 'long'.
    public long PeakVirtualMemorySize {
      [NoDefaultContract]
      get
        requires IsPeerConsistent;
        modifies this.*;
      {
        expose (this) {
          simplify.Refresh();
#if WHIDBEY
            return simplify.PeakVirtualMemorySize64;
#else
            return simplify.PeakPagedMemorySize64;
#endif
        }
      }
    }
    
    public bool HasExited {
      get { return simplify.HasExited; }
    }
    
    public ProverProcess(ProcessStartInfo! psi, string! proverPath)
    { // throws ProverException
      try 
      {
        Process simplify = Process.Start(psi);
        this.simplify = simplify;
        fromSimplify = simplify.StandardOutput;
        toSimplify = simplify.StandardInput;
        fromStdError = simplify.StandardError;
      } 
      catch (System.ComponentModel.Win32Exception e)
      {
        throw new ProverException(string.Format("Unable to start the process {0}: {1}", proverPath, e.Message));
      }
      // base();
    }

    public abstract string! OptionComments();
    [Pure(false)]
    public virtual IEnumerable<string!>! ParameterSettings { get { yield break; } }
    
    public void Close()
      modifies this.*; 
    {
      expose (this) {
        toSimplify.Flush();
        if (this.simplify != null) 
        {
          if (!simplify.HasExited)
          {
            this.Kill();
          }
          simplify.Close();
        }
      }
    }
    
    [NoDefaultContract]  // this method assumes nothing about the object, other than that it has been constructed (which means simplify!=null)
    [Verify(false)]  // The call simplify.Kill will require simplify.IsPeerConsistent, but since we don't know the state of "this" and "simplify", we cannot afford the run-time check that an assume statement here would impose
    public void Kill() {
      try { 
        if (CommandLineOptions.Clo.ProverShutdownLimit > 0) { 
          toSimplify.Close(); 
          for (int i = 0; !simplify.HasExited && i <= CommandLineOptions.Clo.ProverShutdownLimit * 1000; i += 100)
          {		
            System.Threading.Thread.Sleep(100); 
          } 
        }
        if (!simplify.HasExited) { simplify.Kill(); }
      } catch (InvalidOperationException) { /* already exited */ }
        catch (System.ComponentModel.Win32Exception) { /* already exiting */ }
    }

    public virtual void AddAxioms(string! s) 
      modifies this.*;
      modifies Console.Out.*, Console.Error.*;
      throws UnexpectedProverOutputException;
    {
      expose (this) {
        toSimplify.Write("(BG_PUSH ");
        toSimplify.Write(s);
        toSimplify.WriteLine(")");
      }
    }

    public virtual void Feed(string! s, int statementCount) 
      modifies this.*;
      modifies Console.Out.*, Console.Error.*;
      throws UnexpectedProverOutputException;
    {
      expose (this) {
        toSimplify.Write(s);
      }
    }

    public virtual void PopAxioms() 
      modifies this.*;
      modifies Console.Out.*, Console.Error.*;
      throws UnexpectedProverOutputException;
    {
      expose (this) {
        toSimplify.WriteLine("(BG_POP)");
      }
    }

    public void ToFlush()
      modifies this.*;
    {
      expose (this) {
        toSimplify.Flush();
      }
    }

    public enum ProverOutcome { Valid, NotValid, TimeOut, OutOfMemory, Inconclusive }
    
    /// <summary>
    /// Passes the formula to Simplify.
    /// </summary>
    public void BeginCheck(string! descriptiveName, string! formula)
      modifies this.*;
      modifies Console.Out.*, Console.Error.*;
    {
      DoBeginCheck(descriptiveName, formula);
      nFormulasChecked++;
    }
    
    /// <summary>
    /// Reports the outcome of formula checking.  If the outcome is Invalid,
    /// then the "handler" is invoked with each counterexample.
    /// </summary>
    public abstract ProverOutcome CheckOutcome(Microsoft.Boogie.ProverInterface.ErrorHandler! handler)
      modifies this.**;
      modifies Console.Out.*, Console.Error.*;
      modifies handler.*;
      throws UnexpectedProverOutputException;
    
    protected abstract void DoBeginCheck(string! descriptiveName, string! formula)
      modifies this.*;
      modifies Console.Out.*, Console.Error.*;

    /// <summary>
    /// Returns an array of the labels in "labels", with "|" brackets (if any)
    /// stripped off.
    /// Assumes that every label begins with "|+" or "|@", or just "+" or "@",
    /// and ends with "|" if it started with one, and that these "|" brackets are
    /// the only "|"s in "labels".
    /// </summary>
    protected static List<string!>! ParseLabels(string! labels) 
    {
      List<string!> list = new List<string!>();
      int j = 0;
      while (true)
        // invariant: j is the number of characters of "labels" consumed so far
        // invariant: an even number of '|' characters remain in "labels"
        invariant 0 <= j && j <= labels.Length;
      {
        j = labels.IndexOfAny(new char[]{'|', '+', '@'}, j);
        if (j < 0) {
          // no more labels
          return list;
        }
        char ch = labels[j];
        if (ch == '|') {
          j++;  // skip the '|'
          assume j < labels.Length;  // there should now be a '+' or '@'
          ch = labels[j];
        }
        assume ch == '+' || ch == '@';
        j++;  // skip the '+' or '@'
        int k = labels.IndexOfAny(new char[]{'|', ' ', ')'}, j);
        assume j+2 <= k;
        string s = labels.Substring(j, k-j);
        list.Add(s);
        j = k+1;
      }
    }

    [Rep] char[] expectBuffer = null;

    /// <summary>
    /// Expects s[0]==ch and the next s.Length-1 characters of the input to be s[1,..]
    /// If not, more characters may be read from "fromSimplify" to provide additional context
    /// for the UnexpectedProverOutputException exception that will be thrown.
    /// </summary>
    protected void Expect(int ch, string! s) 
      requires 1 <= s.Length;
      modifies this.*;
      throws UnexpectedProverOutputException;
    { 
      if (ch == -1) {
        // a return of -1 from FromReadChar means that there is no StdOutput
        // to treat this we can return the error message we get from Z3 on StdError and then
        // declare this case to be inconclusive 
        string str = FromStdErrorAll();
        if (str == "") {
          throw new ProverDiedException();
        } else {
          throw new UnexpectedProverOutputException("Expected \"" + s + "\", found:\r\n<<<start>>>\r\n" + str + "<<<end>>>");
        }
      }
        
      string badInputPrefix;
      if (ch != s[0]) 
      {
        badInputPrefix = Char.ToString((char)ch);
      } 
      else 
      {
        int len = s.Length - 1;
        if (expectBuffer == null || expectBuffer.Length < len) 
        {
          expose (this) {
            expectBuffer = new char[len];
          }
        }
        try 
        {
          string s0;
          expose (this) {
            fromSimplify.ReadBlock(expectBuffer, 0, len);
            s0 = new string(expectBuffer, 0, len);
          }
          string s1 = s.Substring(1, len);
          if (s0.CompareTo(s1) == 0) 
          {
            badInputPrefix = null;  // no error
          } 
          else 
          {
            badInputPrefix = (char)ch + s0;
          }
        } 
        catch (IOException) 
        {
          throw new UnexpectedProverOutputException("Expected \"" + s + "\", encountered IO exception.");
        }
      }

      if (badInputPrefix != null) 
      {
        // Read the rest of the available input, without blocking!
        // Despite the confusing documentation for the Read method, it seems
        // that Read does block.  It if didn't, I would have written:
        //    string remaining = "";
        //    char[] buf = new char[1024];
        //    while (true) {
        //        int len = fromSimplify.Read(buf, 0, buf.Length);
        //        remaining += new String(buf, 0, len);
        //        if (len != buf.Length) {
        //            break;
        //        }
        //    }
        // But instead, I'll just hope that one line of input is available and read
        // it.
        string remaining = fromSimplify.ReadLine() + "\r\n";
        throw new UnexpectedProverOutputException("Expected \"" + s + "\", found:\r\n<<<start>>>\r\n" + badInputPrefix + remaining + "<<<end>>>");
      }
    }
    
    protected int FromReadChar()
      modifies this.*;
    {
      expose (this) {
        return fromSimplify.Read();
      }
    }

    private void KillProver(object state)
    {
      expose (this) {
        this.readTimedOut = true;
        simplify.Kill();
      }
    }
    
    protected int FromReadChar(int timeout)
      requires -1 <= timeout;
      modifies this.*;
    {
      expose (this) {
        this.readTimedOut = false;
        System.Threading.Timer t = new System.Threading.Timer(this.KillProver, null, timeout, System.Threading.Timeout.Infinite);
        int ch = fromSimplify.Read();
        t.Change(System.Threading.Timeout.Infinite, System.Threading.Timeout.Infinite);
        t.Dispose();
        return ch;
      }
    }
    
    protected string! FromReadLine()
      modifies this.*;
    {
      expose (this) {
        string s = fromSimplify.ReadLine();
        if (s == null) {
          // this is what ReadLine returns if all characters have been read
          s = "";
        }
        return s;
      }
    }
    
    protected string! FromStdErrorAll ()
      modifies this.*;
    {
      expose (this) {
        if (fromStdError != null) {
          string s = fromStdError.ReadToEnd();
          if (s == null) {
            // this is what ReadLine returns if all characters have been read
            s = "";
          }
          return s;
        }
        // there is no StdErrorReader available
        else {
          return "";
        }
      }
    }
    
    protected void ToWriteLine(string! s)
      modifies this.*;
    {
      expose (this) {
        toSimplify.WriteLine(s);
      }
    }
  }
 
  // derived by Z3ProverProcess
  public class SimplifyProverProcess : ProverProcess {
    public SimplifyProverProcess(string! proverPath, bool dummy)
    { // throws ProverException
      ProcessStartInfo psi = new ProcessStartInfo(proverPath, "-labelsonly");
      psi.CreateNoWindow = true;
      psi.UseShellExecute = false;
      psi.RedirectStandardInput = true;
      psi.RedirectStandardOutput = true;
      psi.RedirectStandardError = true;
      assume psi.EnvironmentVariables != null;  // by inspecting the code through Reflector; the documentation says this property is "null by default", whatever that means  --KRML
      if (0 <= CommandLineOptions.Clo.ProverKillTime) {
        psi.EnvironmentVariables["PROVER_KILL_TIME"] = CommandLineOptions.Clo.ProverKillTime.ToString();
      }
      if (0 <= CommandLineOptions.Clo.SimplifyProverMatchDepth) {
        psi.EnvironmentVariables["PROVER_MATCH_DEPTH"] = CommandLineOptions.Clo.SimplifyProverMatchDepth.ToString();
      }
      if (0 <= CommandLineOptions.Clo.ProverCCLimit) {
        psi.EnvironmentVariables["PROVER_CC_LIMIT"] = CommandLineOptions.Clo.ProverCCLimit.ToString();
      }
      
      base(psi, proverPath);
    }

    public override string! OptionComments()
    {
      // would we want the timeout stuff here?
      return "";
    }

    [NotDelayed]
    // TODO it complains about things not beeing peer consistent upon call to EatPrompt()
    // not sure what is it about... --micmo
    [Verify(false)] 
    public SimplifyProverProcess(string! proverPath)
      modifies Console.Out.*, Console.Error.*;
      throws UnexpectedProverOutputException;
    {
      this(proverPath, true);
      EatPrompt();
    }

    private void EatPrompt() 
      modifies this.*;
      modifies Console.Out.*, Console.Error.*;
      throws UnexpectedProverOutputException;
    {
      // skips text matching the regular expression: (white space)* ">\t"
      ToFlush();

      int ch = 0;
      do {
        ch = FromReadChar();
      } while (Char.IsWhiteSpace((char)ch));
      
      while (ch == 'W') {
        ch = ConsumeWarnings(ch, null);
      }
      
      Expect(ch, ">\t");
    }
    
    public override void AddAxioms(string! s) 
      throws UnexpectedProverOutputException;
    {
      //ToWriteLine("(PROMPT_OFF)");
      base.AddAxioms(s);
      //ToWriteLine("(PROMPT_ON)");
      EatPrompt();
    }
    
    public override void Feed(string! s, int statementCount) 
      throws UnexpectedProverOutputException;
    {
      //ToWriteLine("(PROMPT_OFF)");
      base.Feed(s, statementCount);
      //ToWriteLine("(PROMPT_ON)");
      for (int i = 0; i < statementCount; i++) {
        EatPrompt();
      }
    }
    
    public override void PopAxioms() 
      throws UnexpectedProverOutputException;
    {
      base.PopAxioms();
      EatPrompt();
    }

    protected override void DoBeginCheck(string! descriptiveName, string! formula)
    {
      //simplify.Refresh();
      //this.Comment("@@@@ Virtual Memory:  " + simplify.PeakVirtualMemorySize64);
      //this.Comment("@@@@ Working Set:  " + simplify.PeakWorkingSet64);
      //this.Comment("@@@@ Paged Memory:  " + simplify.PeakPagedMemorySize64);
    
      ToWriteLine(formula);
      ToFlush();
    }

    public override ProverOutcome CheckOutcome(Microsoft.Boogie.ProverInterface.ErrorHandler! handler)
      throws UnexpectedProverOutputException;
    {
      ProverOutcome outcome;

      if (this.simplify == null) {
        return ProverOutcome.Inconclusive;
      }
      
      int ch = FromReadChar();
      while (ch == 'W') 
      {
        ch = ConsumeWarnings(ch, handler);
      }
      if (ch == 'E')
      {
        Expect(ch, "Exceeded PROVER_KILL_TIME -- discontinuing search for counterexamples.");
        FromReadLine();
        ch = FromReadChar();
        if (ch == '\n')
        {
          ch = FromReadChar();
        }
        Expect(ch, "  labels:");
        FromReadLine();
        ch = FromReadChar();
        ch = FromReadChar();
        ch = FromReadChar();
        FromReadLine();
        ch = FromReadChar();
        ch = FromReadChar();
        ch = FromReadChar();
        return ProverOutcome.TimeOut;
      }
      if ('0' <= ch && ch <= '9') 
      {
        // Valid!
        do {
          ch = FromReadChar();
        } while ('0' <= ch && ch <= '9');
        Expect(ch, ": Valid.");
        outcome = ProverOutcome.Valid;
        ToWriteLine(String.Format(";   FORMULA {0} IS VALID!", NumFormulasChecked + 1 /*Simplify starts at 1*/));
      } 
      else 
      {
        // now we expect one or more counterexample contexts, each proving a list of labels
        do {
          List<string!> labels = ReadLabels(ch);
          handler.OnModel(labels, null);
          ch = FromReadChar();
        } while (ch == 'C');
        // now we expect "<N>: Invalid" where <N> is some number
        while ('0' <= ch && ch <= '9') 
        {
          ch = FromReadChar();
        }
        Expect(ch, ": Invalid.");
        outcome = ProverOutcome.NotValid;
        ToWriteLine(String.Format(";   FORMULA {0} IS INVALID", NumFormulasChecked + 1 /*Simplify starts at 1*/));
      }

      EatPrompt();
      return outcome;
    }

    List<string!>! ReadLabels(int ch) 
      modifies this.*;
      throws UnexpectedProverOutputException;
    {
      Expect(ch, "Counterexample:\n");  // FIX! ?  Is there a problem with \r\n here?
      ch = FromReadChar();
      List<string!> theLabels;
      if (ch == ' ') 
      {
        // there are labels
        Expect(ch, "  labels: ");
        string labels = FromReadLine();  // reads "(A B C ...)\n"
        theLabels = ParseLabels(labels);
        ch = FromReadChar();
      }
      else
      {
        theLabels = new List<string!>();
      }
      Expect(ch, "\n");  // empty line

      return theLabels;
    }
    
    int ConsumeWarnings(int ch, Microsoft.Boogie.ProverInterface.ErrorHandler handler)
      requires ch == 'W';
      modifies this.*;
      modifies Console.Out.*, Console.Error.*;
      throws UnexpectedProverOutputException;
    {
      Expect(ch, "Warning: ");
      string w = FromReadLine();
      if (w.StartsWith("triggerless quantifier body")) {
        FromReadLine();  // blank line
        w = "triggerless quantifier body: " + FromReadLine();  // expression (body)
        FromReadLine();  // blank line
        FromReadLine();  // "with X pattern variable(s)...
        FromReadLine();  // blank line
        FromReadLine();  // expression (entire quantifier)
      }
      
      if (handler != null) handler.OnProverWarning(w);
      
      ch = FromReadChar();
      if (ch == '\n') 
      {
        // make up for a poorly designed ReadLine routine (only the first
        // character of the DOS end-of-line sequence "\r\n" is read)
        ch = FromReadChar();
      }
      return ch;
    }
  }
  
}

