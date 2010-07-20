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
using Microsoft.Boogie.Simplify;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.Z3
{
  internal class FindLabelsVisitor : TraversingVCExprVisitor<bool, bool> {
    public Dictionary<string!,bool>! Labels = new Dictionary<string!,bool>();

    public static Dictionary<string!,bool>! FindLabels(VCExpr! expr) {
      FindLabelsVisitor! visitor = new FindLabelsVisitor();
      visitor.Traverse(expr, true);
      return visitor.Labels;
    }
    
    protected override bool StandardResult(VCExpr! node, bool arg) {
      VCExprNAry nary = node as VCExprNAry;
      if (nary != null) {
        VCExprLabelOp lab = nary.Op as VCExprLabelOp;
        if (lab != null) {
          Labels[lab.label] = lab.pos;
        }
      }
      return true;      
    }
  }

  internal class Inspector {
    [Rep] protected readonly Process! inspector;
    [Rep] readonly TextReader! fromInspector;
    [Rep] readonly TextWriter! toInspector;

    public Inspector(Z3InstanceOptions! opts)
    {
      ProcessStartInfo! psi = new ProcessStartInfo(opts.Inspector);
      psi.CreateNoWindow = true;
      psi.UseShellExecute = false;
      psi.RedirectStandardInput = true;
      psi.RedirectStandardOutput = true;
      psi.RedirectStandardError = false;

      try 
      {
        Process inspector = Process.Start(psi);
        this.inspector = inspector;
        fromInspector = inspector.StandardOutput;
        toInspector = inspector.StandardInput;
      } 
      catch (System.ComponentModel.Win32Exception e)
      {
        throw new Exception(string.Format("Unable to start the inspector process {0}: {1}", opts.Inspector, e.Message));
      }
    }

    public void NewProver()
    {
    }

    public void NewProblem(string! descriptiveName, VCExpr! vc, ProverInterface.ErrorHandler! handler)
    {
      Dictionary<string!,bool>! labels = FindLabelsVisitor.FindLabels(vc);
      toInspector.WriteLine("PROBLEM " + descriptiveName);
      toInspector.WriteLine("TOKEN BEGIN");
      foreach (string! lab in labels.Keys) {
        string! no = lab.Substring(1);
        Absy! absy = handler.Label2Absy(no);
        IToken tok = absy.tok;
        AssertCmd assrt = absy as AssertCmd;
        Block blk = absy as Block;
        string val = tok.val; // might require computation, so cache it
        if (val == "foo" || tok.filename == null) continue; // no token

        toInspector.Write("TOKEN ");
        toInspector.Write(lab);
        toInspector.Write(" ");

        if (assrt != null) {
          toInspector.Write("ASSERT");
          string errData = assrt.ErrorData as string;
          if (errData != null) {
            val = errData;
          } else if (assrt.ErrorMessage != null) {
            val = assrt.ErrorMessage;
          }
        } else if (blk != null) {
          toInspector.Write("BLOCK ");
          toInspector.Write(blk.Label);
        } else {
          assume false;
        }
        if (val == null || val == "assert" || val == "ensures") { val = ""; }

        if (absy is LoopInitAssertCmd) {
          val += " (loop entry)";
        } else if (absy is LoopInvMaintainedAssertCmd) {
          val += " (loop body)";
        } else if (val.IndexOf("#VCCERR") >= 0) { 
          // skip further transformations
        } else if (absy is AssertRequiresCmd) {
          AssertRequiresCmd req = (AssertRequiresCmd)absy;
          IToken t2 = req.Requires.tok;
          string tval = t2.val;
          if (tval == "requires")
            tval = string.Format("{0}({1},{2}))", t2.filename, t2.line, t2.col);
          string call = "";
          if (val != "call") call = " in call to " + val;
          val = string.Format("precondition {0}{1}", tval, call);
        }

        val = val.Replace("\r", "").Replace("\n", " ");

        toInspector.WriteLine(string.Format(" {0} {1} :@:{2}:@:{3}", tok.line, tok.col, tok.filename, val));
      }
      toInspector.WriteLine("TOKEN END");
    }

    public void StatsLine(string! line)
    {
      toInspector.WriteLine(line);
      toInspector.Flush();
    }
  }
}
