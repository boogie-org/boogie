using System;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Boogie;

public class OutputCollector
{
  StringWriter[] outputs;

  int nextPrintableIndex = 0;

  public OutputCollector(Implementation[] implementations)
  {
    outputs = new StringWriter[implementations.Length];
  }

  public void WriteMoreOutput()
  {
    lock (outputs)
    {
      for (; nextPrintableIndex < outputs.Length && outputs[nextPrintableIndex] != null; nextPrintableIndex++)
      {
        Console.Write(outputs[nextPrintableIndex].ToString());
        outputs[nextPrintableIndex] = null;
        Console.Out.Flush();
      }
    }
  }

  public void Add(int index, StringWriter output)
  {
    Contract.Requires(0 <= index && index < outputs.Length);
    Contract.Requires(output != null);

    lock (this)
    {
      outputs[index] = output;
    }
  }
}