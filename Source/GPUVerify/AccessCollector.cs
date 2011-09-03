using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify
{
    abstract class AccessCollector : StandardVisitor
    {
        protected GPUVerifier verifier;

        public AccessCollector(GPUVerifier verifier)
        {
            this.verifier = verifier;
        }

        protected void MultiDimensionalMapError()
        {
            Console.WriteLine("*** Error - multidimensional maps not supported in kernels, use nested maps instead");
            Environment.Exit(1);
        }

    }
}
