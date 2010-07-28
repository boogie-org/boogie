using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;
using System.IO;
using Microsoft.Boogie;
using Graphing;
using AI = Microsoft.AbstractInterpretationFramework;
using Microsoft.Contracts;
using Microsoft.Basetypes;
using Microsoft.Boogie.VCExprAST;

namespace VC
{
    internal class DoomErrorHandler : ProverInterface.ErrorHandler {

        protected Hashtable! label2Absy;
        protected VerifierCallback! callback;
        
        public Variable m_Reachvar;
        public List<Block!> m_DoomedBlocks, m_TraceBlocks;
        
        
        public DoomErrorHandler(Hashtable! label2Absy, VerifierCallback! callback) {
          this.label2Absy = label2Absy;
          this.callback = callback;
        }
        
        public override Absy! Label2Absy(string! label) {
          int id = int.Parse(label);
          return (Absy!) label2Absy[id];
        }
        
        public override void OnProverWarning(string! msg) {
          this.callback.OnWarning(msg);
        }
   
        public void OnDoom(Variable! reachvar, List<Block!>! doomedblocks, List<Block!>! traceblocks) {
            m_Reachvar = reachvar;
            m_DoomedBlocks = doomedblocks;
            m_TraceBlocks = traceblocks;            
        }
        
        private List<Block!>! m_CurrentTrace = new List<Block!>();
        
        public List<Block!>! TraceNodes 
        {
            get
            {
                return m_CurrentTrace;
            }
        }
        
        public override void OnModel(IList<string!>! labels, ErrorModel errModel) {
        m_CurrentTrace.Clear();
        //Console.Write("Used Blocks: ");
        List<Block!> traceNodes = new List<Block!>();
        List<AssertCmd!> assertNodes = new List<AssertCmd!>();
        foreach (string! s in labels) {
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