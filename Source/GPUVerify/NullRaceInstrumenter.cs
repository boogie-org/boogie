using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    class NullRaceInstrumenter : IRaceInstrumenter
    {

        public void AddRaceCheckingCandidateInvariants(Implementation impl, Microsoft.Boogie.WhileCmd wc)
        {
            
        }

        public void AddKernelPrecondition()
        {
            
        }

        public bool AddRaceCheckingInstrumentation()
        {
            return true;
        }

        public Microsoft.Boogie.BigBlock MakeResetReadWriteSetsStatements(Microsoft.Boogie.IToken tok)
        {
            return new BigBlock(tok, "__ResetReadWriteSets", new CmdSeq(), null, null);
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
