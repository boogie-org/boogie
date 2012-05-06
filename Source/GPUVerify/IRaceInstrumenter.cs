using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    interface IRaceInstrumenter
    {
        void AddRaceCheckingCandidateInvariants(Implementation impl, WhileCmd wc);
        void AddKernelPrecondition();

        // Summary:
        // Returns whether we should continue.
        // E.g. if race checking code could not be added because
        // the specified accesses to check were read/read or did not exist,
        // this will return false.
        bool AddRaceCheckingInstrumentation();

        void AddRaceCheckingDeclarations();

        BigBlock MakeResetReadWriteSetsStatements(IToken tok);

        void AddRaceCheckingCandidateRequires(Procedure Proc);

        void AddRaceCheckingCandidateEnsures(Procedure Proc);

    }
}
