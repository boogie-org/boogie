//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Contracts;
using System.Collections.Generic;
using Microsoft.Basetypes;

namespace VC {
  public class VCContext 
  {
    [Rep] public readonly Hashtable/*<int, Absy!>*/! Label2absy;
    [Rep] public readonly ProverContext! Ctxt;
    public readonly Variable ControlFlowVariable;
    
    public VCContext(Hashtable/*<int, Absy!>*/! label2absy, ProverContext! ctxt)
    {
      this.Label2absy = label2absy;
      this.Ctxt = ctxt;
      // base();
    }
    
    public VCContext(Hashtable/*<int, Absy!>*/! label2absy, ProverContext! ctxt, Variable controlFlowVariable)
    {
      this.Label2absy = label2absy;
      this.Ctxt = ctxt;
      this.ControlFlowVariable = controlFlowVariable;
    }
    
  }

  #region A class to compute wlp of a passive command program
  
  public class Wlp
  {
    public static VCExpr! Block(Block! b, VCExpr! N, VCContext! ctxt)
      modifies ctxt.*;
    {
      VCExpressionGenerator! gen = ctxt.Ctxt.ExprGen;
      VCExpr! res = N;
      
      for (int i = b.Cmds.Length; --i>=0; )
      {
        res = Cmd((!) b.Cmds[i], res, ctxt);
      }
      
      int id = b.UniqueId;
      expose (ctxt) {
        ctxt.Label2absy[id] = b;
        if (ctxt.ControlFlowVariable != null)
          return res;
        else 
          return gen.Implies(gen.LabelPos((!)id.ToString(), VCExpressionGenerator.True), res);
      }
    }

    /// <summary>
    /// Computes the wlp for an assert or assume command "cmd".
    /// </summary>
    public static VCExpr! Cmd(Cmd! cmd, VCExpr! N, VCContext! ctxt)
    {
      VCExpressionGenerator! gen = ctxt.Ctxt.ExprGen;
      if (cmd is AssertCmd) {
        AssertCmd ac = (AssertCmd)cmd;
        VCExpr C = ctxt.Ctxt.BoogieExprTranslator.Translate(ac.Expr);
        if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
          return gen.Implies(C, N);
        } else {
          int id = ac.UniqueId;
          ctxt.Label2absy[id] = ac;
          switch (Subsumption(ac)) {
            case CommandLineOptions.SubsumptionOption.Never:
              break;
            case CommandLineOptions.SubsumptionOption.Always:
              N = gen.Implies(C, N);
              break;
            case CommandLineOptions.SubsumptionOption.NotForQuantifiers:
              if (!(C is VCExprQuantifier)) {
                N = gen.Implies(C, N);
              }
              break;
            default:
              assert false;  // unexpected case
          }
          
          // (MSchaef) Hack: This line might be useless, but at least it is not harmfull
          // need to test it
          if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) 
            return gen.Implies(C, N);
          
          if (ctxt.ControlFlowVariable != null)
          {
            VCExpr! controlFlowVariableExpr = 
              ctxt.Ctxt.BoogieExprTranslator.LookupVariable(ctxt.ControlFlowVariable);
            VCExpr! controlFlowFunctionAppl1 = 
              gen.ControlFlowFunctionApplication(controlFlowVariableExpr, gen.Integer(BigNum.FromInt(id)));
            VCExpr! controlFlowFunctionAppl2 = 
              gen.ControlFlowFunctionApplication(controlFlowVariableExpr, gen.Integer(BigNum.FromInt(id)));
            VCExpr! assertFailure = gen.Eq(controlFlowFunctionAppl1, gen.Integer(BigNum.FromInt(0)));
            VCExpr! assertSuccess = gen.Neq(controlFlowFunctionAppl2, gen.Integer(BigNum.FromInt(0)));
            return gen.And(gen.Implies(assertFailure, C), gen.Implies(assertSuccess, N));
          }
          else
            return gen.AndSimp(gen.LabelNeg((!)id.ToString(), C), N);
        }

      } else if (cmd is AssumeCmd) {
        AssumeCmd ac = (AssumeCmd)cmd;

        if(CommandLineOptions.Clo.StratifiedInlining > 0) {
          // Label the assume if it is a procedure call
          NAryExpr naryExpr = ac.Expr as NAryExpr;
          if (naryExpr != null) {
            if (naryExpr.Fun is FunctionCall) {
              int id = ac.UniqueId;
              ctxt.Label2absy[id] = ac;
              return gen.ImpliesSimp(gen.LabelPos((!)"si_fcall_" + id.ToString(), ctxt.Ctxt.BoogieExprTranslator.Translate(ac.Expr)), N);
            }
          }
        }
        
        return gen.ImpliesSimp(ctxt.Ctxt.BoogieExprTranslator.Translate(ac.Expr), N);

      } else {
      Console.WriteLine(cmd.ToString());
        assert false;  // unexpected command
      }
    }
    
    public static CommandLineOptions.SubsumptionOption Subsumption(AssertCmd! ac) {
      int n = QKeyValue.FindIntAttribute(ac.Attributes, "subsumption", -1);
      switch (n) {
        case 0:  return CommandLineOptions.SubsumptionOption.Never;
        case 1:  return CommandLineOptions.SubsumptionOption.NotForQuantifiers;
        case 2:  return CommandLineOptions.SubsumptionOption.Always;
        default:  return CommandLineOptions.Clo.UseSubsumption;
      }
    }

    public static VCExpr! RegExpr(RE! r, VCExpr! N, VCContext! ctxt)
    {
      if ( r is AtomicRE )
      {
        AtomicRE ar = (AtomicRE) r;
        return Block(ar.b, N, ctxt);
      }
      else if ( r is Sequential )
      {
        Sequential s = (Sequential) r;
        return RegExpr(s.first, RegExpr(s.second, N, ctxt), ctxt);
      }
      else if ( r is Choice )
      {
        Choice ch = (Choice) r;
        VCExpr! res;
        if (ch.rs == null || ch.rs.Length==0) 
        {
          res = N;
        } 
        else 
        {
          VCExpr currentWLP = RegExpr((!)ch.rs[0], N, ctxt);
          for (int i = 1, n = ch.rs.Length; i < n; i++)
          {
            currentWLP = ctxt.Ctxt.ExprGen.And(currentWLP, RegExpr((!)ch.rs[i], N, ctxt));
          }
          res = currentWLP;
        }
        return res;
      }
      else
      {
        assert false;  // unexpected RE subtype
      }
    }
  }
  #endregion

}
