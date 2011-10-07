using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    abstract class AccessCollector : StandardVisitor
    {
        protected List<Variable> GlobalVariables;
        protected List<Variable> TileStaticVariables;

        public AccessCollector(List<Variable> GlobalVariables, List<Variable> TileStaticVariables)
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
