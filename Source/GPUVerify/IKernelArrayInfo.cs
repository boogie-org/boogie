using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    interface IKernelArrayInfo
    {

        ICollection<Variable> getGlobalArrays();

        ICollection<Variable> getGroupSharedArrays();

        ICollection<Variable> getPrivateArrays();

        ICollection<Variable> getAllNonLocalArrays();

        ICollection<Variable> getAllArrays();

        bool Contains(Variable v);

    }
}
