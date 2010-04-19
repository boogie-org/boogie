using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace BCTStmtTest
{
    class Program
    {
        private int i;

        void BCTAssignments(int j)
        {
            i = 7;
            int k;
            k = i + 20;
            i = k / j;
        }

        int BCTConditional(int k)
        {
            int i=0;
            if (k > 5) // ite
            {
                return 7;
            }
            else
            {
                i = k / 2;
            }

            if (i < k) //if without else
            {
                i = 2;
            }

            if (k > 5) // else if
            {
                return 7;
            }
            else if (k < 5)
            {
                i = k / 2;
            }
            else
            {
                return 100;
            }
            return 0;
        }

        static void Main(string[] args)
        {
            
        }
    }
}
