using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class KernelArrayInfoLists : IKernelArrayInfo
    {
        private List<Variable> GlobalVariables;
        private List<Variable> GroupSharedVariables;
        private List<Variable> PrivateVariables;

        public KernelArrayInfoLists()
        {
            GlobalVariables = new List<Variable>();
            GroupSharedVariables = new List<Variable>();
            PrivateVariables = new List<Variable>();
        }

        public ICollection<Variable> getGlobalArrays()
        {
            return GlobalVariables;
        }

        public ICollection<Variable> getGroupSharedArrays()
        {
            return GroupSharedVariables;
        }

        public ICollection<Variable> getAllNonLocalArrays()
        {
            List<Variable> all = new List<Variable>();
            all.AddRange(GlobalVariables);
            all.AddRange(GroupSharedVariables);
            return all;
        }

        public ICollection<Variable> getPrivateArrays()
        {
            return PrivateVariables;
        }

        public ICollection<Variable> getAllArrays()
        {
            List<Variable> all = new List<Variable>();
            all.AddRange(getAllNonLocalArrays());
            all.AddRange(PrivateVariables);
            return all;
        }

        public bool Contains(Variable v)
        {
            return getAllNonLocalArrays().Contains(v);
        }

    }
}
