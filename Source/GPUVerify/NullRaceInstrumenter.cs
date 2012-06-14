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

        public bool AddRaceCheckingInstrumentation()
        {
            return true;
        }

        public Microsoft.Boogie.BigBlock MakeResetReadWriteSetsStatements(Variable v, int Thread)
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

    }
}
