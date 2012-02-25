using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    class NullRaceInstrumenter : IRaceInstrumenter
    {

        public void AddRaceCheckingCandidateInvariants(Microsoft.Boogie.WhileCmd wc)
        {
            
        }

        public void AddKernelPrecondition()
        {
            
        }

        public void CheckForRaces(IToken tok, BigBlock bb, Variable v, bool ReadWriteOnly)
        {
        }

        public bool AddRaceCheckingInstrumentation()
        {
            return true;
        }

        public Microsoft.Boogie.BigBlock MakeRaceCheckingStatements(Microsoft.Boogie.IToken tok)
        {
            return new BigBlock(tok, "__CheckForRaces", new CmdSeq(), null, null);
        }

        public void AddRaceCheckingCandidateRequires(Procedure Proc)
        {

        }

        public void AddRaceCheckingCandidateEnsures(Procedure Proc)
        {

        }
    
    }
}
