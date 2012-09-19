using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;

namespace GPUVerify {

  class AdversarialAbstraction {

    private GPUVerifier verifier;

    internal AdversarialAbstraction(GPUVerifier verifier) {
      this.verifier = verifier;
    }

    internal void Abstract() {
      List<Declaration> NewTopLevelDeclarations = new List<Declaration>();
      foreach (Declaration d in verifier.Program.TopLevelDeclarations) {
        if (d is Variable && verifier.KernelArrayInfo.Contains(d as Variable) &&
          verifier.ArrayModelledAdversarially(d as Variable)) {
          continue;
        }

        if (d is Implementation) {
          Abstract(d as Implementation);
        }

        if (d is Procedure) {
          Abstract(d as Procedure);
        }

        NewTopLevelDeclarations.Add(d);

      }

      verifier.Program.TopLevelDeclarations = NewTopLevelDeclarations;

      AbstractRequiresClauses(verifier.KernelProcedure);
    }


    private void AbstractRequiresClauses(Procedure proc) {
      RequiresSeq newRequires = new RequiresSeq();
      foreach (Requires r in proc.Requires) {
        var visitor = new AccessesAdversarialArrayVisitor(verifier);
        visitor.VisitRequires(r);
        if (!visitor.found) {
          newRequires.Add(r);
        }
      }
      proc.Requires = newRequires;
    }

    private void Abstract(Procedure proc) {
      AbstractModifiesSet(proc);
    }

    private void AbstractModifiesSet(Procedure proc) {
      IdentifierExprSeq NewModifies = new IdentifierExprSeq();
      foreach (IdentifierExpr e in proc.Modifies) {
        var visitor = new AccessesAdversarialArrayVisitor(verifier);
        visitor.VisitIdentifierExpr(e);
        if(!visitor.found) {
          NewModifies.Add(e);
        }
      }
      proc.Modifies = NewModifies;
    }

    private void Abstract(Implementation impl) {
      VariableSeq NewLocVars = new VariableSeq();

      foreach (Variable v in impl.LocVars) {
        Debug.Assert(!verifier.KernelArrayInfo.getGroupSharedArrays().Contains(v));
        NewLocVars.Add(v);
      }

      impl.LocVars = NewLocVars;

      if (CommandLineOptions.Unstructured)
        impl.Blocks = impl.Blocks.Select(Abstract).ToList();
      else
        impl.StructuredStmts = Abstract(impl.StructuredStmts);
    }


    private StmtList Abstract(StmtList stmtList) {
      Contract.Requires(stmtList != null);

      StmtList result = new StmtList(new List<BigBlock>(), stmtList.EndCurly);

      foreach (BigBlock bodyBlock in stmtList.BigBlocks) {
        result.BigBlocks.Add(Abstract(bodyBlock));
      }
      return result;
    }

    private CmdSeq Abstract(CmdSeq cs) {
      var result = new CmdSeq();

      foreach (Cmd c in cs) {
        if (c is AssignCmd) {
          AssignCmd assign = c as AssignCmd;

          var lhss = new List<AssignLhs>();
          var rhss = new List<Expr>();

          for (int i = 0; i != assign.Lhss.Count; i++) {
            AssignLhs lhs = assign.Lhss[i];
            Expr rhs = assign.Rhss[i];
            ReadCollector rc = new ReadCollector(verifier.KernelArrayInfo);
            rc.Visit(rhs);

            bool foundAdversarial = false;
            foreach (AccessRecord ar in rc.accesses) {
              if (verifier.ArrayModelledAdversarially(ar.v)) {
                foundAdversarial = true;
                break;
              }
            }

            if (foundAdversarial) {
              Debug.Assert(lhs is SimpleAssignLhs);
              result.Add(new HavocCmd(c.tok, new IdentifierExprSeq(new IdentifierExpr[] { (lhs as SimpleAssignLhs).AssignedVariable })));
              continue;
            }

            WriteCollector wc = new WriteCollector(verifier.KernelArrayInfo);
            wc.Visit(lhs);
            if (wc.GetAccess() != null && verifier.ArrayModelledAdversarially(wc.GetAccess().v)) {
              continue; // Just remove the write
            }

            lhss.Add(lhs);
            rhss.Add(rhs);
          }

          if (lhss.Count != 0) {
            result.Add(new AssignCmd(assign.tok, lhss, rhss));
          }
          continue;
        }
        result.Add(c);
      }

      return result;
    }

    private Block Abstract(Block b) {
      b.Cmds = Abstract(b.Cmds);
      return b;
    }

    private BigBlock Abstract(BigBlock bb) {
      BigBlock result = new BigBlock(bb.tok, bb.LabelName, new CmdSeq(), null, bb.tc);

      result.simpleCmds = Abstract(bb.simpleCmds);

      if (bb.ec is WhileCmd) {
        WhileCmd WhileCommand = bb.ec as WhileCmd;
        result.ec =
            new WhileCmd(WhileCommand.tok, WhileCommand.Guard, WhileCommand.Invariants, Abstract(WhileCommand.Body));
      }
      else if (bb.ec is IfCmd) {
        IfCmd IfCommand = bb.ec as IfCmd;
        Debug.Assert(IfCommand.elseIf == null);
        result.ec = new IfCmd(IfCommand.tok, IfCommand.Guard, Abstract(IfCommand.thn), IfCommand.elseIf, IfCommand.elseBlock != null ? Abstract(IfCommand.elseBlock) : null);
      }
      else {
        Debug.Assert(bb.ec == null || bb.ec is BreakCmd);
      }

      return result;

    }

    class AccessesAdversarialArrayVisitor : StandardVisitor {
      internal bool found;
      private GPUVerifier verifier;

      internal AccessesAdversarialArrayVisitor(GPUVerifier verifier) {
        this.found = false;
        this.verifier = verifier;
      }

      public override Variable VisitVariable(Variable v) {
        if (verifier.KernelArrayInfo.Contains(v)) {
          if (verifier.ArrayModelledAdversarially(v)) {
            found = true;
          }
        }
        return base.VisitVariable(v);
      }

    }
  
  }


}
