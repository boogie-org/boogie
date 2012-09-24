using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    interface IRaceInstrumenter
    {
        void AddRaceCheckingCandidateInvariants(Implementation impl, IRegion region);
        void AddKernelPrecondition();

        void AddRaceCheckingInstrumentation();

        void AddRaceCheckingDeclarations();

        BigBlock MakeResetReadWriteSetStatements(Variable v, Expr ResetCondition);

        void AddRaceCheckingCandidateRequires(Procedure Proc);

        void AddRaceCheckingCandidateEnsures(Procedure Proc);

        void AddSourceLocationLoopInvariants(Implementation impl, IRegion region);

        void DoHoudiniPointerAnalysis(Procedure Proc);
        void AddStandardSourceVariablePreconditions();

        void AddStandardSourceVariablePostconditions();
    }
}
