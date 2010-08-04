//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

/* 
    Todo:
       - Inject Pre- and Postcondition
*/

using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;
using System.IO;
using Microsoft.Boogie;
using Graphing;
using AI = Microsoft.AbstractInterpretationFramework;
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
        
    
        public bool CheckReachvar(Variable reachvar, out ProverInterface.Outcome outcome) {
          Contract.Requires(reachvar != null);
            VCExpr vc = m_Checker.TheoremProver.Context.BoogieExprTranslator.LookupVariable(reachvar);
          Contract.Assert(vc != null);
            // Todo: Check if vc is trivial true or false            
            outcome = ProverInterface.Outcome.Undetermined;
            Contract.Assert( m_ErrorHandler !=null);
            m_Checker.BeginCheck(reachvar.Name, vc, m_ErrorHandler);
            m_Checker.ProverDone.WaitOne();
            
            try {
              outcome = m_Checker.ReadOutcome();
            } catch (UnexpectedProverOutputException e)
            {
              if (CommandLineOptions.Clo.TraceVerify) { 
                Console.WriteLine("Prover is unable to check {0}! Reason:", reachvar.Name);
                Console.WriteLine(e.ToString());
              }
              return false;
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
        public Hashtable Label2Absy;
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
        private InclusionOrder m_Order;
        private Evc m_Evc;
        #endregion
        
        [NotDelayed]
        public DoomCheck (Implementation passive_impl, Checker check) {
          Contract.Requires(passive_impl != null);
          Contract.Requires(check != null);
            m_Check = check;
            if (!VC.DCGen.UseItAsDebugger ) {  
                m_Order = new InclusionOrder(passive_impl.Blocks[0]);
            } else {
                m_Order = new InclusionOrder(cce.NonNull(VC.DCGen.firstNonDebugBlock) );
            }
            Label2Absy = new Hashtable(); // This is only a dummy
            m_Evc = new Evc(check);
            Hashtable l2a = null;
            VCExpr vce = this.GenerateEVC(passive_impl, out l2a, check);
          Contract.Assert(vce != null);
            Contract.Assert( l2a!=null);
            Label2Absy = l2a;
//            vce = check.VCExprGen.Implies(vce, vce);
            m_Evc.Initialize(vce);
        }

        /* - Set b to the next block that needs to be checked.
           - Returns false and set b to null if all blocks are checked.           
           - Has to be alternated with CheckLabel; might crash otherwise
        */
        public bool GetNextBlock(out Block b) {
            return m_Order.GetNextBlock(out b);
        }
        
        /*  - Checking a label means to ask the prover if |= ( rvar=false -> vc ) holds.            
            - outcome is set to Outcome.Invalid if the Block denoted by reachvar is doomed.            
            - returns false if the theorem prover throws an exception, otherwise true.            
        */
        public bool CheckLabel(Variable reachvar, out ProverInterface.Outcome outcome) {
           Contract.Requires(reachvar != null);
            outcome = ProverInterface.Outcome.Undetermined;
            if (m_Evc.CheckReachvar(reachvar, out outcome) ) {
                if (!m_Order.SetCurrentResult(reachvar, outcome, m_ErrHandler)) {
                    outcome = ProverInterface.Outcome.Undetermined;
                }
                return true;
            } else {
                m_Order.SetCurrentResult(reachvar, ProverInterface.Outcome.Undetermined, m_ErrHandler);
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
        private bool _tmpUseFreshBVars;
       
        VCExpr GenerateEVC(Implementation impl, out Hashtable label2absy, Checker ch)
        {
          Contract.Requires(impl != null);
          Contract.Requires(ch != null);
          Contract.Ensures(Contract.Result<VCExpr>() != null);

			    TypecheckingContext tc = new TypecheckingContext(null);
			    impl.Typecheck(tc);
			    label2absy = new Hashtable/*<int, Absy!>*/();
			    VCExpr vc;
			    switch (CommandLineOptions.Clo.vcVariety) {
				    case CommandLineOptions.VCVariety.Doomed:

                        if (!VC.DCGen.UseItAsDebugger ) {
                            vc = LetVC(cce.NonNull(impl.Blocks[0]), label2absy, ch.TheoremProver.Context);
                        }
                        #region _TESTING_NEW_STUFF_
                        else  {
                        
                                                                        
                        CommandLineOptions.Clo.vcVariety = CommandLineOptions.VCVariety.Block;				        
				        Contract.Assert( VC.DCGen.firstDebugBlock != null);
				        VCExpr a = LetVC(VC.DCGen.firstDebugBlock, label2absy, ch.TheoremProver.Context);				        				        				        
                          Contract.Assert(a != null);
				        CommandLineOptions.Clo.vcVariety = CommandLineOptions.VCVariety.Doomed;			

                        				        
                        VCExpr b = LetVC(cce.NonNull(VC.DCGen.firstNonDebugBlock), label2absy, ch.TheoremProver.Context);

					    //_tmpUseFreshBVars=false;
					    //vc = ch.VCExprGen.Not(ch.VCExprGen.Implies( wp, ch.VCExprGen.Not(vc)));
					    
					    vc = ch.VCExprGen.Not(ch.VCExprGen.Implies(ch.VCExprGen.Not(a), ch.VCExprGen.Not(b)));
					    
					    
					    /*
                            ConsoleColor col = Console.ForegroundColor;
                            Console.ForegroundColor = ConsoleColor.Green; 					    
					        Console.WriteLine(vc.ToString());
                            Console.ForegroundColor = col;
                            Console.WriteLine(" ... was asked.");
                        */
                                                                 
					    }
					    #endregion
					    					    
					    break;
					    
				    default:
					    Contract.Assert(false);throw new cce.UnreachableException();  // unexpected enumeration value
			    }
			    return vc;
        }

        public VCExpr LetVC(Block startBlock,
                             Hashtable/*<int, Absy!>*/ label2absy,
                             ProverContext proverCtxt)
        {Contract.Requires(startBlock != null);
          Contract.Requires(label2absy != null);
          Contract.Requires(proverCtxt != null);
          Contract.Ensures(Contract.Result<VCExpr>() != null);

          Hashtable/*<Block, LetVariable!>*/ blockVariables = new Hashtable/*<Block, LetVariable!!>*/();
          List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
          VCExpr startCorrect = LetVC(startBlock, label2absy, blockVariables, bindings, proverCtxt);
          if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
            return proverCtxt.ExprGen.Let(bindings, proverCtxt.ExprGen.Not(startCorrect) );
          } else {
            return proverCtxt.ExprGen.Let(bindings, startCorrect );
          }
        }

        VCExpr LetVC(Block block,
                             Hashtable/*<int, Absy!>*/ label2absy,
                             Hashtable/*<Block, VCExprVar!>*/ blockVariables,
                             List<VCExprLetBinding> bindings,
                             ProverContext proverCtxt)
        {
      Contract.Requires(label2absy != null);
      Contract.Requires(blockVariables != null);
      Contract.Requires(proverCtxt != null);
      Contract.Requires(cce.NonNullElements(bindings));
          Contract.Ensures(Contract.Result<VCExpr>() != null);

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
              List<VCExpr> SuccCorrectVars = new List<VCExpr>(gotocmd.labelTargets.Length);
              foreach (Block successor in gotocmd.labelTargets) {
                Contract.Assert(successor != null);
                VCExpr s = LetVC(successor, label2absy, blockVariables, bindings, proverCtxt);
                SuccCorrectVars.Add(s);
              }
              SuccCorrect = gen.NAry(VCExpressionGenerator.AndOp, SuccCorrectVars);
            }

            VCContext context = new VCContext(label2absy, proverCtxt);
    //        m_Context = context;

            VCExpr vc = Wlp.Block(block, SuccCorrect, context);

            v = gen.Variable(block.Label + "_correct", Microsoft.Boogie.Type.Bool);
            
            bindings.Add(gen.LetBinding(v, vc));
            blockVariables.Add(block, v);
          }
          return v;
        }

        
        #endregion 

        
        #region Build Inclusion Order to minimize the number of checks    
        class InclusionOrder 
        {

            #region Attributes
            public List<List<Block/*!*/>/*!*/>/*!*/ DetectedBlock = new List<List<Block/*!*/>/*!*/>();
 
            
            InclusionTree RootNode = new InclusionTree(null);
            InclusionTree currentNode = null;
            [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(DetectedBlock!=null);
              Contract.Invariant(RootNode != null);
}

            #endregion
        
            [NotDelayed]
            public InclusionOrder(Block rootblock) {Contract.Requires(rootblock != null);
                /*
                    We now compute for each block the set of blocks that
                    are reached on every execution reaching this block (dominator).
                    We first compute it form the start block to the current
                    block and second from the Term block to the current one.
                    Finally we build the union.
                */
                Dictionary<Block,TraceNode> map2 = new Dictionary<Block,TraceNode>();
                Dictionary<Block,TraceNode> map = new Dictionary<Block,TraceNode>();
                
                Dictionary<Block, List<Block>> unavoidablemap = new Dictionary<Block, List<Block>>();

                Block exitblock = BreadthFirst(rootblock, map2);Contract.Assert(exitblock != null);
                BreadthFirstBwd(exitblock, map);

                foreach (KeyValuePair<Block, TraceNode> kvp in map) {
                  Contract.Assert(kvp.Key != null);Contract.Assert(kvp.Value != null);
                    List<Block/*!*/>/*!*/ blist = new List<Block/*!*/>();
                    foreach (TraceNode tn in kvp.Value.Unavoidables ) {
                        blist.Add(tn.block);
                    }
                    unavoidablemap.Add(kvp.Key, blist);
                }
                foreach (KeyValuePair<Block, List<Block>> kvp in unavoidablemap) {
                  Contract.Assert(kvp.Key != null);
                  Contract.Assert(cce.NonNullElements(kvp.Value));
                    TraceNode tn = null;
                    if (map2.TryGetValue(kvp.Key, out tn) ) {
                        Contract.Assert( tn!=null);
                        foreach (TraceNode t0 in tn.Unavoidables) {Contract.Assert(t0 != null);
                            if (!kvp.Value.Contains(t0.block))
                                kvp.Value.Add(t0.block);
                        }
                    } else {
                        //assert false;
                    }
                }

                foreach (KeyValuePair<Block, List<Block>> kvp in unavoidablemap) {
                  Contract.Assert(kvp.Key != null);
                  Contract.Assert(cce.NonNullElements(kvp.Value));
                    Insert2Tree(RootNode,kvp);
                }
                InitCurrentNode(RootNode);
                //printtree(RootNode, "",0);
            }
                                  
            void InitCurrentNode(InclusionTree n) {Contract.Requires(n != null);
                if (n.Children.Count>0) {
                    InitCurrentNode(n.Children[0]);
                } else {
                    currentNode = n;
                }
            }
            
            public bool GetNextBlock(out Block b) {
                if (currentNode!=null && currentNode.EquivBlock.Count>0) {
                    b = currentNode.EquivBlock[0];
                    return true;
                }                   
                b = null;
                return false;
            }
            
            
            /*
                Warning: this is a very slow implementation. There should be
                a map from Block to InclusionTree to prevent running through
                the tree over and over again.
            */
            private void MarkUndoomedFromCE(Block b, InclusionTree node)
            {Contract.Requires(b != null);Contract.Requires(node != null);
                if (node.EquivBlock.Contains(b) ) {
                    //Console.WriteLine("Block {0} does not need to be checked - appears in CE", b.Label);
                    node.HasBeenChecked = true;
                    node.IsDoomed = false;
                    MarkUndoomedParents(node);
                    return;
                } else
                {
                    foreach (InclusionTree c in node.Children) {
                      Contract.Assert(c != null);
                        MarkUndoomedFromCE(b, c);
                    }
                }
            }
            
            // Takes the outcome for the current reachvar and marks all blocks
            // the do not need any further checking because they share the same
            // desteny
            // returns false if an explicite assert false was found.
            // Warning: Still slow; we do not need to do this while constructing the error report!            
            public bool SetCurrentResult(Variable reachvar, ProverInterface.Outcome outcome, DoomErrorHandler cb) {Contract.Requires(reachvar != null);
                if (outcome!=ProverInterface.Outcome.Valid) { 
                    if (currentNode != null) {
                        currentNode.IsDoomed = false;
                        currentNode.HasBeenChecked = true;
                        MarkUndoomedParents(currentNode);
                        if (cb != null) {
                            //Console.WriteLine("CE contains: ");
                            foreach (Block b in cb.TraceNodes)
                            {Contract.Assert(b != null);
                                //Console.Write("{0}, ", b.Label);
                                MarkUndoomedFromCE(b, RootNode);
                            }
                            //Console.WriteLine();
                        } else {
                            Console.WriteLine("ErrorHandler is not valid! ------ (DoomCheck)");
                        }
                                                                       
                        currentNode = FindNextNode(currentNode);
                    }
                } else {
                    if (currentNode != null) {                            

                        // Check if there is an assert false in this node or in one of its parents
                        // if so do not report anything
//                        if (ECContainsAssertFalse(currentNode.EquivBlock)) {  
//                        
//                            ConsoleColor col = Console.ForegroundColor;
//                            Console.ForegroundColor = ConsoleColor.Blue;
//                            Console.WriteLine("Assert false or PossiblyUnreachable was detected, but ignored");
//                            Console.ForegroundColor = col;
//
//                            currentNode.HasBeenChecked = true;
//                            currentNode.IsDoomed = false;
//                            currentNode = currentNode.Parent;
//                            return false;
//                        }
                        
                        List<Block> traceblocks = new List<Block>();
                                                
                        TracedChildern(currentNode, traceblocks);
                        TracedParents(currentNode, traceblocks);
                        
//                        cb.OnWarning("Doomed program points found!");
                        if (cb != null) {
                            cb.OnDoom(reachvar, currentNode.EquivBlock, traceblocks);
                        }
                                                
                        if (currentNode.EquivBlock.Count>0) {
                            
                            foreach (InclusionTree n in currentNode.Children) {Contract.Assert(n != null);
                                if (DetectedBlock.Contains(n.EquivBlock) ) {
                                    DetectedBlock.Remove(n.EquivBlock);
                                }
                            }
                            
                            DetectedBlock.Add(currentNode.EquivBlock);

                        } else {
                            Console.WriteLine("An empty equivalence class has been detected");
                            Contract.Assert(false);throw new cce.UnreachableException();
                        }
                        
                        currentNode.IsDoomed = true;
                        currentNode.HasBeenChecked = true;
                        MarkDoomedChildren(currentNode);
                        currentNode = currentNode.Parent;
                        if (currentNode!=null) {
                          foreach (InclusionTree it in currentNode.Children) {
                            Contract.Assert(it != null);
                                if (!it.HasBeenChecked) {
                                    currentNode = DescendToDeepestUnchecked(it);
                                    break;
                                }
                            }
                        }
                    }                        
                }
                return true;
            }      
            
            private InclusionTree DescendToDeepestUnchecked(InclusionTree node) 
            {
              Contract.Requires(node != null);
              Contract.Ensures(Contract.Result<InclusionTree>() != null);

                foreach (InclusionTree it in node.Children) {Contract.Assert(it != null);
                    if (!it.HasBeenChecked) {
                        return DescendToDeepestUnchecked(it);
                    }
                }
                return node;
            }                
            
            private bool ECContainsAssertFalse(List<Block> equiv) {
              Contract.Requires(cce.NonNullElements(equiv));
                foreach (Block b in equiv) {Contract.Assert(b != null);
                    if (BlockContainsAssertFalse(b)) return true;
                }
                return false;
            }

            private bool BlockContainsAssertFalse(Block b) {Contract.Requires(b != null);
                foreach (Cmd c in b.Cmds) {Contract.Assert(c != null);
                    AssertCmd ac = c as AssertCmd;
                    if (ac!=null) {
                        if (IsFalse(ac.Expr) || QKeyValue.FindBoolAttribute(ac.Attributes, "PossiblyUnreachable") ) {
                            return true;
                        }
                    }
                }
                return false;
            }

            // check if e is true, false, !true, !false
            // if so return true and the value of the expression in val
            bool BooleanEval(Expr e, ref bool val)
            {
              Contract.Requires(e != null);
                LiteralExpr lit = e as LiteralExpr;
                NAryExpr call = e as NAryExpr;

                if (lit != null && lit.isBool) {
                  val = lit.asBool;
                  return true;
            } else if (call != null && 
                       call.Fun is UnaryOperator && 
                       ((UnaryOperator)call.Fun).Op == UnaryOperator.Opcode.Not &&
                       BooleanEval(cce.NonNull(call.Args[0]), ref val)) {
              val = !val;
              return true;
            } 
            // this is for the 0bv32 != 0bv32 generated by vcc
            else if (call != null && 
                       call.Fun is BinaryOperator && 
                       ((BinaryOperator)call.Fun).Op == BinaryOperator.Opcode.Neq &&
                       call.Args[0] is LiteralExpr &&
                       cce.NonNull(call.Args[0]).Equals(call.Args[1]))
            {
              val = false;
              return true;
            }

            return false;
            }

            bool IsFalse(Expr e)
            {Contract.Requires(e != null);
                bool val = false;
                return BooleanEval(e, ref val) && !val;
            }

            private void TracedChildern(InclusionTree node, List<Block/*!*/>/*!*/ blist) {
              Contract.Requires(node != null);
              Contract.Requires(cce.NonNullElements(blist));
                foreach (Block b in node.EquivBlock) {Contract.Assert(b != null);
                    if (!blist.Contains(b)) blist.Add(b);
                }
                foreach (InclusionTree n in node.Children) {
                  Contract.Assert(n != null);
                    TracedChildern(n, blist);
                }
            }
            
            private void TracedParents(InclusionTree node, List<Block> blist) {
              Contract.Requires(node != null);
              Contract.Requires(cce.NonNullElements(blist));
                foreach (Block b in node.EquivBlock) {Contract.Assert(b != null);
                    if (!blist.Contains(b)) blist.Add(b);
                }
                if (node.Parent!=null) {
                    TracedParents(node.Parent, blist);
                }
            }
                                    
            InclusionTree FindNextNode(InclusionTree n) {Contract.Requires(n != null);
                Contract.Assert( n!=n.Parent);
                InclusionTree next = n.Parent;
                if (next!=null) {
                  foreach (InclusionTree n0 in next.Children) {
                    Contract.Assert(n0 != null);
                        if (!n0.HasBeenChecked) {
                            return n0;
                        }
                    }
                    return FindNextNode(next);
                }                
                return next;
            }
            
            void MarkUndoomedParents(InclusionTree n) {Contract.Requires(n != null);
                if (n.Parent != null) {
                    n.Parent.HasBeenChecked = true;
                    n.Parent.IsDoomed = false;
                    MarkUndoomedParents(n.Parent);
                }
            }
            
            void MarkDoomedChildren(InclusionTree n) {Contract.Requires(n != null);
            foreach (InclusionTree t in n.Children) {
              Contract.Assert(t != null);
                    t.IsDoomed = true;
                    t.HasBeenChecked = true;
                    MarkDoomedChildren(t);
                }
            }
                                   
            bool Insert2Tree(InclusionTree node, KeyValuePair<Block, List<Block>> kvp) {
              Contract.Requires(node != null);
              Contract.Requires(kvp.Key != null);
              Contract.Requires(cce.NonNullElements(kvp.Value));
                if (IsSubset(node.PathBlocks, kvp.Value) ) {
                    if (IsSubset(kvp.Value, node.PathBlocks) ) {
                        // The set of unavoidable blocks is equal, so 
                        // we can put the block in the same node.
                        node.EquivBlock.Add(kvp.Key);
                        return true;
                    } else {
                        foreach (InclusionTree n in node.Children) {Contract.Assert(n != null);
                            if (Insert2Tree(n,kvp) ) {
                                return true;
                            }
                        }
                        // we have not been able to add the block to one of
                        // the children, so we have to create a new child.
                        InclusionTree it = new InclusionTree(node);
                        Contract.Assert(it != null);
                        it.EquivBlock.Add(kvp.Key);
                        it.PathBlocks.AddRange(kvp.Value);
                        node.Children.Add(it);
                        return true;
                    }
                    // If we reached this point, we have to add a new node since
                    // our current set of pathnodes is not a subset of anything else
                } else {
                    // seems, that we have reached a new leaf.
                }                
                return false;
            }            
            
            bool IsSubset(List<Block> sub, List<Block> super ) {Contract.Requires(sub!=null);Contract.Requires(cce.NonNullElements(super));
                foreach (Block b in sub) {
                  Contract.Assert(b != null);
                    if (!super.Contains(b) ) return false;
                }
                return true;
            }
            
            void printtree(InclusionTree n, string indent, int level) {Contract.Requires(n != null);
                Console.Write("{0}Level {1}: Blocks ", indent, level);
                foreach (Block b in n.EquivBlock) {Contract.Assert(b != null);
                    Console.Write("{0}, ", b.Label);
                }
                Console.WriteLine();

                foreach (InclusionTree t in n.Children) {
                  Contract.Assert(t != null);
                    printtree(t, indent+"  ", level+1);
                }
            }
            
            private class InclusionTree {
                public InclusionTree(InclusionTree p) {
                    Parent = p;
                    HasBeenChecked=false;
                    IsDoomed = false;
                }
                
                public bool HasBeenChecked;
                public bool IsDoomed;
                public InclusionTree Parent;
                public List<Block/*!*/>/*!*/ EquivBlock = new List<Block>();
                public List<Block/*!*/>/*!*/ PathBlocks = new List<Block>();
                public List<InclusionTree/*!*/>/*!*/ Children = new List<InclusionTree>();
              [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(Parent!=null);
                Contract.Invariant(cce.NonNullElements(EquivBlock));
                Contract.Invariant(cce.NonNullElements(PathBlocks));
                Contract.Invariant(cce.NonNullElements(Children));
}

            }
            
            #region Collect Unavoidable Blocks
            private Block BreadthFirst(Block start, Dictionary<Block, TraceNode> blockmap) {
              Contract.Requires(start != null);
              Contract.Requires(cce.NonNullElements(blockmap));
              Contract.Ensures(Contract.Result<Block>() != null);

                List<Block> JobList = new List<Block>();
                List<Block> DoneList = new List<Block>();
                Block exitblock=null;
                JobList.Add(start);
                Block currentBlock = JobList[0];
                // Travers the Graph Breadth First and collect all 
                // predecessors of each node that are reached on any
                // path to this node
                while (JobList.Count>0)
                {                    
                    currentBlock = JobList[0];
                    TraceNode tn = new TraceNode(currentBlock);
                  Contract.Assert(tn != null);
                    
                    if (currentBlock.Predecessors.Length>0 ) {                    
                        TraceNode t0 =null;
                        Block firstpred = currentBlock.Predecessors[0];
                        
                        Contract.Assert( firstpred!=null);
                        if (blockmap.TryGetValue(firstpred, out t0)) {
                            Contract.Assert( t0 !=null);
                            tn.Unavoidables.AddRange(t0.Unavoidables);
                        }
                    }   
                                         
                    foreach (Block b0 in currentBlock.Predecessors) {Contract.Assert(b0 != null);
                        TraceNode t = null;
                        if (blockmap.TryGetValue(b0, out t)) {
                            Contract.Assert( t!=null);
                            tn.Predecessors.Add(t);
                            IntersectUnavoidables(t,tn);
                            if (!t.Successors.Contains(tn)) t.Successors.Add(tn);
                            blockmap[b0]=t;
                        }
                    }
                    if (!tn.Unavoidables.Contains(tn)) {
                        tn.Unavoidables.Add(tn);
                    } else
                    {
                        Contract.Assert(false);throw new cce.UnreachableException();
                    }          
                    
                                        
                    blockmap.Add(currentBlock, tn);
                    
                    GotoCmd gc = currentBlock.TransferCmd as GotoCmd;
                    if (gc!=null) {
                        Contract.Assert( gc.labelTargets!=null);
                        foreach (Block b0 in gc.labelTargets) {Contract.Assert(b0 != null);
                            if (!JobList.Contains(b0) && !DoneList.Contains(b0)) {
                                
                                JobList.Add(b0);
                            }
                        }
                    } else {
                        exitblock=currentBlock;
                    }
                    DoneList.Add(currentBlock);
                    JobList.RemoveAt(0);
                }
                Contract.Assert( exitblock!=null);
                return exitblock;
            }
       
            // WARNING: It is only for testing reasons that
            // BreadthFirstBwd and BreadthFirst and separat functions
            // it should be implemented using one function later on.
            private void BreadthFirstBwd(Block start, Dictionary<Block, TraceNode> blockmap) {
              Contract.Requires(start != null);
              Contract.Requires(cce.NonNullElements(blockmap));

                List<Block> JobList = new List<Block>();
                List<Block> DoneList = new List<Block>();
                JobList.Add(start);
                Block currentBlock = JobList[0];
                // Travers the Graph Breadth First and collect all 
                // predecessors of each node that are reached on any
                // path to this node
                while (JobList.Count>0)
                {                    
                    currentBlock = JobList[0];
                    TraceNode tn = new TraceNode(currentBlock);Contract.Assert(tn != null);
                    
                    GotoCmd gc = currentBlock.TransferCmd as GotoCmd;
                    BlockSeq preds = null;
                    if (gc!=null) {
                        preds = gc.labelTargets;
                    }
                    
                    if (preds != null ) {
                    
                        TraceNode t0 =null;
                        Block firstpred = preds[0];
                        
                        Contract.Assert( firstpred!=null);
                        if (blockmap.TryGetValue(firstpred, out t0)) {
                            Contract.Assert( t0 !=null);
                            tn.Unavoidables.AddRange(t0.Unavoidables);
                        }
                      
                                         
                        foreach (Block b0 in preds) {Contract.Assert(b0 != null);
                            TraceNode t = null;
                            if (blockmap.TryGetValue(b0, out t)) {
                                Contract.Assert( t!=null);
                                tn.Successors.Add(t);
                                IntersectUnavoidables(t,tn);
                                if (!t.Predecessors.Contains(tn)) t.Predecessors.Add(tn);
                                blockmap[b0]=t;
                            }
                        }
                    } 
                    if (!tn.Unavoidables.Contains(tn)) {
                        tn.Unavoidables.Add(tn);
                    } else
                    {
                        Contract.Assert(false);throw new cce.UnreachableException();
                    }
                    blockmap.Add(currentBlock, tn);
                                        
                    if (currentBlock.Predecessors.Length>0) {
                      foreach (Block b0 in currentBlock.Predecessors) {
                        Contract.Assert(b0 != null);
                            if (!JobList.Contains(b0) && !DoneList.Contains(b0) ) 
                                JobList.Add(b0);
                        }
                    }
                    DoneList.Add(currentBlock);
                    JobList.RemoveAt(0);
                }
            }
                   
            private void IntersectUnavoidables(TraceNode parent, TraceNode child) {
              Contract.Requires(parent != null);
              Contract.Requires(child != null);
                List<TraceNode/*!*/>/*!*/ ret = new List<TraceNode>();
                List<TraceNode/*!*/>/*!*/ tmp = new List<TraceNode>();
                tmp.AddRange(parent.Unavoidables);
                tmp.AddRange(child.Unavoidables);
                
                foreach (TraceNode tn in tmp) {Contract.Assert(tn != null);
                    if (parent.Unavoidables.Contains(tn) && child.Unavoidables.Contains(tn) 
                        && !ret.Contains(tn) ) {
                        ret.Add(tn);
                    }
                }
                Contract.Assert( ret.Count <= parent.Unavoidables.Count && ret.Count <= child.Unavoidables.Count);
                child.Unavoidables = ret;
                
             }
            
            #region TraceNode Class  
            // We assume that the program is already loopfree, otherwise we will
            // not terminate      
            private class TraceNode  {
                public List<TraceNode/*!*/>/*!*/ Predecessors = new List<TraceNode>();
                public List<TraceNode/*!*/>/*!*/ Successors = new List<TraceNode>();
                public List<TraceNode/*!*/>/*!*/ Unavoidables = new List<TraceNode>();
                public Block/*!*/ block;

                [ContractInvariantMethod]
                void ObjectInvariant() {
                  Contract.Invariant(block != null);
                  Contract.Invariant(cce.NonNullElements(Predecessors));
                  Contract.Invariant(cce.NonNullElements(Successors));
                  Contract.Invariant(cce.NonNullElements(Unavoidables));
                }

                public TraceNode(Block b) {
                  Contract.Requires(b != null);
                    block=b;
                }
                
            }
            #endregion
            #endregion
        }
        #endregion
        
        
    }
}
