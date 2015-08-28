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
    internal class DoomErrorHandler : ProverInterface.ErrorHandler
    {

        protected Dictionary<int, Absy> label2Absy;
        protected VerifierCallback callback;
        private List<Block> m_CurrentTrace = new List<Block>();

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(label2Absy != null);
            Contract.Invariant(callback != null);
            Contract.Invariant(cce.NonNullElements(m_CurrentTrace));
        }


        public DoomErrorHandler(Dictionary<int, Absy> label2Absy, VerifierCallback callback)
        {
            Contract.Requires(label2Absy != null);
            Contract.Requires(callback != null);
            this.label2Absy = label2Absy;
            this.callback = callback;
        }

        public override Absy Label2Absy(string label)
        {
            //Contract.Requires(label != null);
            Contract.Ensures(Contract.Result<Absy>() != null);

            int id = int.Parse(label);
            return cce.NonNull((Absy)label2Absy[id]);
        }

        public override void OnProverWarning(string msg)
        {
            //Contract.Requires(msg != null);
            this.callback.OnWarning(msg);
        }


        public List<Block>/*!>!*/ TraceNodes
        {
            get
            {
                Contract.Ensures(cce.NonNullElements(Contract.Result<List<Block>>()));

                return m_CurrentTrace;
            }
        }

        public override void OnModel(IList<string>/*!>!*/ labels, Model model, ProverInterface.Outcome proverOutcome)
        {
            // TODO: it would be better to check which reachability variables are actually set to one!
            List<Block> traceNodes = new List<Block>();
            List<AssertCmd> assertNodes = new List<AssertCmd>();            
            foreach (string s in labels)
            {
                Contract.Assert(s != null);
                Absy node = Label2Absy(s);
                if (node is Block)
                {
                    Block b = (Block)node;
                    traceNodes.Add(b);
                    //Console.Write("{0}, ", b.Label);
                }
            }
            m_CurrentTrace.AddRange(traceNodes);
        }

    }

}