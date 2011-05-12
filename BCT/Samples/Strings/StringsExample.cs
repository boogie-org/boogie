using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

/* Example of string functionality needed by Poirot: concatenation and equality */
class StringsExample
{
    public static void Main()
    {
        string foo = "delicious";
        string bar = "cake";
        Contract.Assert(!foo.Equals(bar));
        string foo_bar = foo + bar;
        Contract.Assert(foo_bar.Equals("deliciouscake"));
        string delish = "delicious";
        Contract.Assert(foo.Equals(delish));
    }
}