using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Boogie;

namespace GPUVerify
{
    class AccessRecord
    {
        public Variable v;
        public Expr IndexZ;
        public Expr IndexY;
        public Expr IndexX;

        public AccessRecord(Variable v, Expr IndexZ, Expr IndexY, Expr IndexX)
        {
            this.v = v;
            this.IndexZ = IndexZ;
            this.IndexY = IndexY;
            this.IndexX = IndexX;
        }


    }
}
