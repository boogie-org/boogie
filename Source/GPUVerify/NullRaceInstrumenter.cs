using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    class NullRaceInstrumenter : IRaceInstrumenter
    {

        public void AddRaceCheckingCandidateInvariants(Implementation impl, IRegion region)
        {
            
        }

        public void AddKernelPrecondition()
        {
            
        }

        public void AddRaceCheckingInstrumentation()
        {

        }

        public Microsoft.Boogie.BigBlock MakeResetReadWriteSetStatements(Variable v, Expr ResetCondition)
        {
            return new BigBlock(Token.NoToken, null, new CmdSeq(), null, null);
        }

        public void AddRaceCheckingCandidateRequires(Procedure Proc)
        {

        }

        public void AddRaceCheckingCandidateEnsures(Procedure Proc)
        {

        }

        public void AddRaceCheckingDeclarations()
        {

        }
        
        public void AddSourceLocationLoopInvariants(Implementation impl, IRegion region)
        {

        }

        public void DoHoudiniPointerAnalysis(Procedure Proc)
        {

        }

        public void AddStandardSourceVariablePreconditions()
        {

        }

        public void AddStandardSourceVariablePostconditions()
        {

        }
    }
}
