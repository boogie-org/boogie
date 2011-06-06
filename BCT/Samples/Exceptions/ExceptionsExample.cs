using System;
using System.Threading;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

/* Simple example of exception support needed by Poirot */

class PoirotMain
{

    public static void foo()
    {
        throw new Exception("Error");
    }

    public static void Main()
    {
        int x = 5;
        try
        {
            foo();
            x = 17;
        }
        catch (Exception e)
        {
            x = 34;
        }
        Contract.Assert(x == 35);
    }
}



