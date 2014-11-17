using NUnit.Framework;
using System;
using System.Diagnostics;

namespace Microsoft.Boogie
{
  namespace TestUtil
  {

    public class AssertionTextWriterTraceListener : TextWriterTraceListener {
      public AssertionTextWriterTraceListener(System.IO.Stream stream) : base(stream) { }

      public AssertionTextWriterTraceListener(System.IO.TextWriter writer) : base(writer) { }

      public override void Fail(string message) {
        base.Fail(message);
        Assert.Fail(message);
      }

      public override void Fail(string message, string detailMessage) {
        base.Fail(message, detailMessage);
        Assert.Fail(message + " : " + detailMessage);
      }
    }
  }
}

