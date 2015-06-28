//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;
using System.IO;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
    internal class Evc {
        
        public DoomErrorHandler ErrorHandler {
            set {
                m_ErrorHandler = value;
            }
        }
        
      [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(m_Checker!=null);
}

        private Checker m_Checker;
        private DoomErrorHandler m_ErrorHandler;
        
        [NotDelayed]
        public Evc(Checker check) {
          Contract.Requires(check != null);
            m_Checker = check;
                   
        }
        
        public void Initialize(VCExpr evc) {
          Contract.Requires(evc != null);
            m_Checker.PushVCExpr(evc);
        }
        
    
        public bool CheckReachvar(List<Variable> lv,Dictionary<Expr, int> finalreachvars, 
            int k, int l, bool usenew , out ProverInterface.Outcome outcome) {
          Contract.Requires(lv != null);

          VCExpr vc = VCExpressionGenerator.False;
          if (usenew )
          {
              foreach (Variable v in lv)
              {

                  vc = m_Checker.VCExprGen.Or(
                      m_Checker.VCExprGen.Neq(
                          m_Checker.VCExprGen.Integer(BigNum.ZERO),
                          m_Checker.TheoremProver.Context.BoogieExprTranslator.LookupVariable(v)),
                      vc);
              }
              //Console.WriteLine("TPQuery k={0}, l={1}, |Sp|={2}", k, l, finalreachvars.Count);

              VCExpr vc21 = m_Checker.VCExprGen.Integer(BigNum.ZERO); // Ask: is the necessary or can we use the same instance term in two inequalities?
              VCExpr vc22 = m_Checker.VCExprGen.Integer(BigNum.ZERO);

                  foreach (KeyValuePair<Expr, int> kvp in finalreachvars)
                  {

                      vc21 = m_Checker.VCExprGen.Add(vc21, m_Checker.TheoremProver.Context.BoogieExprTranslator.Translate(kvp.Key));
                      vc22 = m_Checker.VCExprGen.Add(vc22, m_Checker.TheoremProver.Context.BoogieExprTranslator.Translate(kvp.Key));
                  }                  

              VCExpr post = m_Checker.VCExprGen.Gt(m_Checker.VCExprGen.Integer(BigNum.FromInt(l)), vc21);

              if (k != -1)
              {
                  post = m_Checker.VCExprGen.Or(
                        post, m_Checker.VCExprGen.Gt(vc22, m_Checker.VCExprGen.Integer(BigNum.FromInt(k)))
                        );
              }
              vc = (m_Checker.VCExprGen.Or(vc, (post) ));

          }
          else
          {
              
              foreach (Variable v in lv)
              {

                  vc = m_Checker.VCExprGen.Or(
                      m_Checker.VCExprGen.Eq(
                          m_Checker.VCExprGen.Integer(BigNum.ONE),
                          m_Checker.TheoremProver.Context.BoogieExprTranslator.LookupVariable(v)),
                      vc);
              }
              Contract.Assert(vc != null);

              // Add the desired outcome of the reachability variables
              foreach (KeyValuePair<Expr, int> kvp in finalreachvars)
              {
                  vc = m_Checker.VCExprGen.Or(
                      m_Checker.VCExprGen.Neq(
                          m_Checker.VCExprGen.Integer(BigNum.FromInt(kvp.Value)),
                          m_Checker.TheoremProver.Context.BoogieExprTranslator.Translate(kvp.Key)),
                      vc);
              }

          }

            // Todo: Check if vc is trivial true or false            
            outcome = ProverInterface.Outcome.Undetermined;
            Contract.Assert(m_ErrorHandler != null);
            try
            {
              m_Checker.BeginCheck(lv[0].Name, vc, m_ErrorHandler);
              m_Checker.ProverTask.Wait();
              outcome = m_Checker.ReadOutcome();
            }
            catch (UnexpectedProverOutputException e)
            {
              if (CommandLineOptions.Clo.TraceVerify)
              {
                Console.WriteLine("Prover is unable to check {0}! Reason:", lv[0].Name);
                Console.WriteLine(e.ToString());
              }
              return false;
            }
            finally
            {
              m_Checker.GoBackToIdle();
            }
            return true;
        }
    }

    internal class DoomCheck {
        
      [ContractInvariantMethod]
        void ObjectInvariant() 
        {
            Contract.Invariant(Label2Absy!=null);
            Contract.Invariant(m_Check != null);
            Contract.Invariant(m_Evc != null);
            Contract.Invariant(m_Order != null);
        }

        #region Attributes
        public Dictionary<int, Absy> Label2Absy;
        public DoomErrorHandler ErrorHandler {
            set {
                m_ErrHandler = value;
                m_Evc.ErrorHandler = value;
            }
            
            get {
                return m_ErrHandler;
            }
        }
        
        private DoomErrorHandler m_ErrHandler;
        private Checker m_Check;
        private DoomDetectionStrategy m_Order;
        private Evc m_Evc;
        #endregion
        
        public void __DEBUG_PrintStatistics()
        {
            Console.WriteLine("Checked/Total: Bl {0} / {1} EQ {2} / {3} {4} Tr {5} {6} / {7}", m_Order.__DEBUG_BlocksChecked, m_Order.__DEBUG_BlocksTotal, m_Order.__DEBUG_EQCChecked, m_Order.__DEBUG_EQCTotal, m_Order.__DEBUG_EQCLeaf,  m_Order.__DEBUG_TracesChecked, m_Order.__DEBUG_InfeasibleTraces, m_Order.__DEBUG_TracesTotal);
        }

        [NotDelayed]
        public DoomCheck (Implementation passive_impl, Block unifiedExit, Checker check, List<Block> uncheckable, out int assertionCount) {
          Contract.Requires(passive_impl != null);
          Contract.Requires(check != null);
          Contract.Requires(uncheckable != null);
            m_Check = check;            

            int replaceThisByCmdLineOption = CommandLineOptions.Clo.DoomStrategy ;
            if (CommandLineOptions.Clo.DoomStrategy!=-1) Console.Write("Running experiments using {0} /", replaceThisByCmdLineOption);
            switch (replaceThisByCmdLineOption)
            {
                default:
                    {
                        if (CommandLineOptions.Clo.DoomStrategy != -1) Console.WriteLine("Path Cover specialK Strategy");
                        m_Order = new PathCoverStrategyK(passive_impl, unifiedExit, uncheckable);
                        break;
                    }
                case 1:
                    {
                        if (CommandLineOptions.Clo.DoomStrategy != -1) Console.WriteLine("Path Cover L Strategy");
                        m_Order = new PathCoverStrategy(passive_impl, unifiedExit, uncheckable);
                        break;
                    }
                case 2:
                    {
                        if (CommandLineOptions.Clo.DoomStrategy != -1) Console.WriteLine("hasse strategy");
                        m_Order = new HierachyStrategy(passive_impl, unifiedExit, uncheckable);

                        break;
                    }
                case 3:
                    {
                        if (CommandLineOptions.Clo.DoomStrategy != -1) Console.WriteLine("hasse+ce strategy");
                        m_Order = new HierachyCEStrategy(passive_impl, unifiedExit, uncheckable);
                        break;
                    }
                case 4:
                    {
                        if (CommandLineOptions.Clo.DoomStrategy != -1) Console.WriteLine("no strategy");
                        m_Order = new NoStrategy(passive_impl, unifiedExit, uncheckable);
                        break;
                    }
                    
            }

            Label2Absy = new Dictionary<int, Absy>(); // This is only a dummy
            m_Evc = new Evc(check);
            Dictionary<int, Absy> l2a = null;
            VCExpr vce = this.GenerateEVC(passive_impl, out l2a, check, out assertionCount);
            Contract.Assert(vce != null);
            Contract.Assert( l2a!=null);
            Label2Absy = l2a;
          
            m_Evc.Initialize(vce);
        }


        public void RespawnChecker(Implementation passive_impl, Checker check)
        {
            Contract.Requires(check != null);
            m_Check = check;
            Label2Absy = new Dictionary<int, Absy>(); // This is only a dummy
            m_Evc = new Evc(check);
            Dictionary<int, Absy> l2a = null;
            int assertionCount;  // compute and then ignore
            VCExpr vce = this.GenerateEVC(passive_impl, out l2a, check, out assertionCount);
            Contract.Assert(vce != null);
            Contract.Assert(l2a != null);
            Label2Absy = l2a;

            m_Evc.Initialize(vce);            
        }

        /* - Set b to the next block that needs to be checked.
           - Returns false and set b to null if all blocks are checked.           
           - Has to be alternated with CheckLabel; might crash otherwise
        */
        public bool GetNextBlock(out List<Block> lb)
        {
            return m_Order.GetNextBlock(out lb);
        }

        public Stopwatch DEBUG_ProverTime = new Stopwatch();

        /*  - Checking a label means to ask the prover if |= ( rvar=false -> vc ) holds.            
            - outcome is set to Outcome.Invalid if the Block denoted by reachvar is doomed.            
            - returns false if the theorem prover throws an exception, otherwise true.            
        */
        public bool CheckLabel(List<Variable> lv,Dictionary<Expr, int> finalreachvars, out ProverInterface.Outcome outcome) {
           Contract.Requires(lv != null);
            outcome = ProverInterface.Outcome.Undetermined;
            DEBUG_ProverTime.Reset();
            DEBUG_ProverTime.Start();
            if (m_Evc.CheckReachvar(lv,finalreachvars,m_Order.MaxBlocks,m_Order.MinBlocks,m_Order.HACK_NewCheck,  out outcome) ) {
                DEBUG_ProverTime.Stop();
                if (!m_Order.SetCurrentResult(lv, outcome, m_ErrHandler)) {
                    outcome = ProverInterface.Outcome.Undetermined;
                }
                return true;
            } else {
                DEBUG_ProverTime.Stop();
                Console.WriteLine(outcome);
                m_Order.SetCurrentResult(lv, ProverInterface.Outcome.Undetermined, m_ErrHandler);
                return false;
            }
        }

        public List<List<Block/*!>!>!*/>> DoomedSequences { 
            get {
              Contract.Ensures(Contract.ForAll(Contract.Result<List<List<Block>>>(), i=> cce.NonNullElements(i)));

                return m_Order.DetectedBlock;
            }
        }


        #region Error Verification Condition Generation
       /*
                   #region _TESTING_NEW_STUFF_
            CommandLineOptions.Clo.vcVariety = CommandLineOptions.VCVariety.Block;
            //VCExpr wp = Wlp.Block(block, SuccCorrect, context); // Computes wp.S.true
            
            CommandLineOptions.Clo.vcVariety = CommandLineOptions.VCVariety.Doomed;
            #endregion

       */

        VCExpr GenerateEVC(Implementation impl, out Dictionary<int, Absy> label2absy, Checker ch, out int assertionCount) {
          Contract.Requires(impl != null);
          Contract.Requires(ch != null);
          Contract.Ensures(Contract.Result<VCExpr>() != null);

          TypecheckingContext tc = new TypecheckingContext(null);
          impl.Typecheck(tc);
          label2absy = new Dictionary<int, Absy>();
          VCExpr vc;
          switch (CommandLineOptions.Clo.vcVariety) {
            case CommandLineOptions.VCVariety.Doomed:
              vc = LetVC(cce.NonNull(impl.Blocks[0]), label2absy, ch.TheoremProver.Context, out assertionCount);
              break;

            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected enumeration value
          }
          return vc;
        }

        public VCExpr LetVC(Block startBlock,
                            Dictionary<int, Absy> label2absy,
                            ProverContext proverCtxt,
                            out int assertionCount)
        {
          Contract.Requires(startBlock != null);
          Contract.Requires(label2absy != null);
          Contract.Requires(proverCtxt != null);
          Contract.Ensures(Contract.Result<VCExpr>() != null);

          Hashtable/*<Block, LetVariable!>*/ blockVariables = new Hashtable/*<Block, LetVariable!!>*/();
          List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
          VCExpr startCorrect = LetVC(startBlock, label2absy, blockVariables, bindings, proverCtxt, out assertionCount);
          if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
            return proverCtxt.ExprGen.Let(bindings, proverCtxt.ExprGen.Not(startCorrect) );
          } else {
            return proverCtxt.ExprGen.Let(bindings, startCorrect );
          }
        }

        VCExpr LetVC(Block block,
                     Dictionary<int, Absy> label2absy,
                     Hashtable/*<Block, VCExprVar!>*/ blockVariables,
                     List<VCExprLetBinding> bindings,
                     ProverContext proverCtxt,
                     out int assertionCount)
        {
          Contract.Requires(label2absy != null);
          Contract.Requires(blockVariables != null);
          Contract.Requires(proverCtxt != null);
          Contract.Requires(cce.NonNullElements(bindings));
          Contract.Ensures(Contract.Result<VCExpr>() != null);

          assertionCount = 0;
          VCExpressionGenerator gen = proverCtxt.ExprGen;
          Contract.Assert(gen != null);
          VCExprVar v = (VCExprVar)blockVariables[block];
          if (v == null) {
            /*
             * For block A (= block), generate:
             *   LET_binding A_correct = wp(A_body, (/\ S \in Successors(A) :: S_correct))
             * with the side effect of adding the let bindings to "bindings" for any
             * successor not yet visited.
             */
            VCExpr SuccCorrect;
            GotoCmd gotocmd = block.TransferCmd as GotoCmd;
            if (gotocmd == null) {
                if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
                    SuccCorrect = VCExpressionGenerator.False;
                } else {
                    SuccCorrect = VCExpressionGenerator.True;
                }
            } else {
              Contract.Assert( gotocmd.labelTargets != null);
              List<VCExpr> SuccCorrectVars = new List<VCExpr>(gotocmd.labelTargets.Count);
              foreach (Block successor in gotocmd.labelTargets) {
                Contract.Assert(successor != null);
                int ac;
                VCExpr s = LetVC(successor, label2absy, blockVariables, bindings, proverCtxt, out ac);
                assertionCount += ac;
                SuccCorrectVars.Add(s);
              }
              SuccCorrect = gen.NAry(VCExpressionGenerator.AndOp, SuccCorrectVars);
            }

            VCContext context = new VCContext(label2absy, proverCtxt);
            //        m_Context = context;

            VCExpr vc = Wlp.Block(block, SuccCorrect, context);
            assertionCount += context.AssertionCount;
            v = gen.Variable(block.Label + "_correct", Microsoft.Boogie.Type.Bool);
            
            bindings.Add(gen.LetBinding(v, vc));
            blockVariables.Add(block, v);
          }
          return v;
        }

        
        #endregion 
                       
    }

}
