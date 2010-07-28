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
    internal class DoomErrorHandler : ProverInterface.ErrorHandler {

        protected Hashtable label2Absy;
        protected VerifierCallback callback;
        private List<Block> m_CurrentTrace = new List<Block>();
        public Variable m_Reachvar;
        public List<Block> m_DoomedBlocks, m_TraceBlocks;
        
      [ContractInvariantMethod]
void ObjectInvariant() 
{
    Contract.Invariant(label2Absy!=null);
        Contract.Invariant(callback != null);
        Contract.Invariant(cce.NonNullElements(m_CurrentTrace));
        Contract.Invariant(m_Reachvar != null);
        Contract.Invariant(m_DoomedBlocks != null);
        Contract.Invariant(m_TraceBlocks != null);
}

        
        public DoomErrorHandler(Hashtable label2Absy, VerifierCallback callback) {
          Contract.Requires(label2Absy != null);
          Contract.Requires(callback != null);
          this.label2Absy = label2Absy;
          this.callback = callback;
        }
        
        public override Absy Label2Absy(string label) {
          Contract.Requires(label != null);
          Contract.Ensures(Contract.Result<Absy>() != null);

          int id = int.Parse(label);
          return cce.NonNull((Absy) label2Absy[id]);
        }
        
        public override void OnProverWarning(string msg) {
          Contract.Requires(msg != null);
          this.callback.OnWarning(msg);
        }
   
        public void OnDoom(Variable reachvar, List<Block>/*!>!*/ doomedblocks, List<Block>/*!>!*/ traceblocks) {
      Contract.Requires(reachvar != null);
          Contract.Requires(cce.NonNullElements(doomedblocks));
          Contract.Requires(cce.NonNullElements(traceblocks));
            m_Reachvar = reachvar;
            m_DoomedBlocks = doomedblocks;
            m_TraceBlocks = traceblocks;            
        }
        
        
        
        public List<Block>/*!>!*/ TraceNodes 
        {
            get
            {
              Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));
              
                return m_CurrentTrace;
            }
        }
        
        public override void OnModel(IList<string>/*!>!*/ labels, ErrorModel errModel) {
          Contract.Requires(labels != null);
          
        m_CurrentTrace.Clear();
        //Console.Write("Used Blocks: ");
        List<Block> traceNodes = new List<Block>();
        List<AssertCmd> assertNodes = new List<AssertCmd>();
        foreach (string s in labels) {
          Contract.Assert(s != null);
          Absy node = Label2Absy(s);
          if (node is Block) {
            Block b = (Block)node;
            traceNodes.Add(b);
            //Console.Write("{0}, ", b.Label);
          } else {
            AssertCmd a = (AssertCmd)node;
            assertNodes.Add(a);            
          }
        }
        m_CurrentTrace.AddRange(traceNodes);
        //Console.WriteLine();
//        assert assertNodes.Count > 0;
//        assert traceNodes.Count == assertNodes.Count;
//
//        foreach (AssertCmd a in assertNodes) {
//          // find the corresponding Block (assertNodes.Count is likely to be 1, or small in any case, so just do a linear search here)
//          foreach (Block b in traceNodes) {
//            if (b.Cmds.Has(a)) {
//              BlockSeq trace = new BlockSeq();
//              trace.Add(b);
//              goto NEXT_ASSERT;
//            }
//          }
//          assert false;  // there was no block that contains the assert
//          NEXT_ASSERT: {}
//        }
      
        }
        
    }
    
}