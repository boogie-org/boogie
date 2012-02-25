using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;

namespace GPUVerify
{
    class NonLocalStateLists : INonLocalState
    {
        private List<Variable> GlobalVariables;
        private List<Variable> GroupSharedVariables;

        public NonLocalStateLists()
        {
            GlobalVariables = new List<Variable>();
            GroupSharedVariables = new List<Variable>();
        }

        public ICollection<Variable> getGlobalVariables()
        {
            return GlobalVariables;
        }

        public ICollection<Variable> getGroupSharedVariables()
        {
            return GroupSharedVariables;
        }

        public ICollection<Variable> getAllNonLocalVariables()
        {
            List<Variable> all = new List<Variable>();
            all.AddRange(GlobalVariables);
            all.AddRange(GroupSharedVariables);
            return all;
        }

        public bool Contains(Variable v)
        {
            return getAllNonLocalVariables().Contains(v);
        }

    }
}
