using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    interface INonLocalState
    {

        ICollection<Variable> getGlobalVariables();

        ICollection<Variable> getGroupSharedVariables();

        ICollection<Variable> getAllNonLocalVariables();

        bool Contains(Variable v);

    }
}
