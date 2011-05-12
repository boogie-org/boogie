using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

/* Simple example of generics/dictionary support needed by Poirot */
class GenericsExample
{
    public static void Main()
    {
        Dictionary<String, String> dict = new Dictionary<String, String>();
        dict["foo"] = "bar";
        Contract.Assert(dict.ContainsKey("foo"));
        Contract.Assert(dict.ContainsValue("bar"));
        Contract.Assert(dict["foo"] == "bar");
        dict.Remove("foo");
        Contract.Assert(dict["foo"] == "bar"); // should fail
    }
}