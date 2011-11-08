using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    abstract class AccessCollector : StandardVisitor
    {
        protected ICollection<Variable> GlobalVariables;
        protected ICollection<Variable> TileStaticVariables;

        public AccessCollector(ICollection<Variable> GlobalVariables, ICollection<Variable> TileStaticVariables)
        {
            this.GlobalVariables = GlobalVariables;
            this.TileStaticVariables = TileStaticVariables;
        }

        protected void MultiDimensionalMapError()
        {
            Console.WriteLine("*** Error - multidimensional maps not supported in kernels, use nested maps instead");
            Environment.Exit(1);
        }

    }
}
