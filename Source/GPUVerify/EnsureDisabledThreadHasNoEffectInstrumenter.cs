using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class EnsureDisabledThreadHasNoEffectInstrumenter
    {

        private GPUVerifier verifier;
        private Implementation Impl;

        public EnsureDisabledThreadHasNoEffectInstrumenter(GPUVerifier verifier, Implementation Impl)
        {
            this.verifier = verifier;
            this.Impl = Impl;
        }

        internal void instrument()
        {

            if (verifier.uniformityAnalyser.IsUniform(Impl.Name))
            {
                return;
            }

            foreach (IdentifierExpr iex in Impl.Proc.Modifies)
            {
                // For some reason, this does not work well with maps
                if (iex.Decl.TypedIdent.Type is MapType)
                {
                    continue;
                }

                Expr NoEffectExpr = Expr.Imp(
                        Expr.Not(new IdentifierExpr(iex.tok, new LocalVariable(iex.tok, new TypedIdent(iex.tok, "_P$" + 
                            GPUVerifier.GetThreadSuffix(iex.Name), Microsoft.Boogie.Type.Bool)))),
                        Expr.Eq(iex, new OldExpr(iex.tok, iex))
                    );

                Impl.Proc.Ensures.Add(new Ensures(false,
                    NoEffectExpr
                ));

                GPUVerifier.AddInvariantToAllLoops(NoEffectExpr, Impl.StructuredStmts);

            }

            AddEnablednessInvariantToAllLoops(Impl.StructuredStmts);
        }

        private void AddEnablednessInvariantToAllLoops(StmtList stmtList)
        {
            foreach (BigBlock bb in stmtList.BigBlocks)
            {
                AddEnablednessInvariantToAllLoops(bb);
            }
        }

        private void AddEnablednessInvariantToAllLoops(BigBlock bb)
        {
            if (bb.ec is WhileCmd)
            {
                WhileCmd wc = bb.ec as WhileCmd;
                Debug.Assert(wc.Guard is NAryExpr);
                Debug.Assert((wc.Guard as NAryExpr).Fun is BinaryOperator);
                Debug.Assert((wc.Guard as NAryExpr).Args[0] is IdentifierExpr);
                string LoopPredicate = ((wc.Guard as NAryExpr).Args[0] as IdentifierExpr).Name;
                LoopPredicate = GPUVerifier.StripThreadIdentifier(LoopPredicate);

                wc.Invariants.Add(
                    new AssertCmd(wc.tok,
                        Expr.Imp(
                            Expr.Not(new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, "_P$1", Microsoft.Boogie.Type.Bool)))),
                            Expr.Not(new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, LoopPredicate + "$1", Microsoft.Boogie.Type.Bool))))
                    )));

                wc.Invariants.Add(
                    new AssertCmd(wc.tok,
                        Expr.Imp(
                            Expr.Not(new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, "_P$2", Microsoft.Boogie.Type.Bool)))),
                            Expr.Not(new IdentifierExpr(wc.tok, new LocalVariable(wc.tok, new TypedIdent(wc.tok, LoopPredicate + "$2", Microsoft.Boogie.Type.Bool))))
                    )));

                AddEnablednessInvariantToAllLoops(wc.Body);
            }

        }
    
    }
}
