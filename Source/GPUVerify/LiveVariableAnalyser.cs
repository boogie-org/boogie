using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;

namespace GPUVerify
{
    class LiveVariableAnalyser
    {
        private GPUVerifier verifier;

        // Maps procedure -> loop -> set of variables live at the loop head
        private Dictionary<string, Dictionary<string, HashSet<string>>> liveVariableInfo;

        public LiveVariableAnalyser(GPUVerifier verifier)
        {
            this.verifier = verifier;
            this.liveVariableInfo = new Dictionary<string, Dictionary<string, HashSet<string>>>();
        }

        internal void Analyse()
        {
            foreach (Declaration D in verifier.Program.TopLevelDeclarations)
            {
                if (D is Implementation)
                {
                    Implementation impl = D as Implementation;

                    liveVariableInfo[impl.Name] = new Dictionary<string, HashSet<string>>();

                    LiveVariableAnalysis.ComputeLiveVariables(impl);

                    Analyse(impl.StructuredStmts, impl);

                }
            }
        }

        private void Analyse(StmtList stmtList, Implementation impl)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                Analyse(bb, impl);
            }
        }

        private void Analyse(BigBlock bb, Implementation impl)
        {
            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;

                Debug.Assert(wc.Invariants.Count >= 1);

                string wcLabel = wc.Invariants[0].Attributes.Key;

                Debug.Assert (wcLabel.Contains("loophead_"));

                liveVariableInfo[impl.Name][wcLabel] = new HashSet<string>();

                Block wcStartBlock = GetBlockForWhile(wc, impl);

                Debug.Assert(wcStartBlock != null);

//                Debug.Assert(wcStartBlock.liveVarsBefore != null);

                if (wcStartBlock.liveVarsBefore == null)
                {
                    Console.WriteLine("live before is null for " + wcLabel);
                }
                else
                {
                    Console.WriteLine("live before is non-null for " + wcLabel);
                    foreach (Variable v in impl.LocVars)
                    {
                        if (wcStartBlock.IsLive(v))
                        {
                            liveVariableInfo[impl.Name][wcLabel].Add(v.Name);
                        }
                    }
                }

                Analyse(wc.Body, impl);
            }
            else if (bb.ec is IfCmd)
            {
                Analyse((bb.ec as IfCmd).thn, impl);
                if ((bb.ec as IfCmd).elseBlock != null)
                {
                    Analyse((bb.ec as IfCmd).elseBlock, impl);
                }
                Debug.Assert((bb.ec as IfCmd).elseIf == null);
            }

        }

        private Block GetBlockForWhile(WhileCmd wc, Implementation impl)
        {
            string whileLoopIdentifier =
                wc.Invariants[0].Attributes.Key;

            foreach (Block b in impl.Blocks)
            {
                if (b.Cmds.Length > 0 && b.Cmds[0] is AssertCmd)
                {
                    AssertCmd ass = b.Cmds[0] as AssertCmd;
                    if (ass.Attributes != null)
                    {
                        if (ass.Attributes.Key.Equals(whileLoopIdentifier))
                        {
                            return b;
                        }
                    }
                }
            }

            Debug.Assert(false);

            return null;
        }
    }
}
