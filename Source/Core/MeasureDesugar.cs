using Microsoft.BaseTypes;

namespace Microsoft.Boogie
{
  public static class MeasureDesugar
  {
    public static Program Desugar(CoreOptions options, Program program)
    {
      // run the existing transformation
      MeasureChecker.Transform(program, options);

      if (options.TraceVerify)
      {
        options.OutputWriter.WriteLine("Printing inserted measure obligations:");

        var wr = new TokenTextWriter("<console>", options.OutputWriter, false, options);

        // print inserted asserts
        foreach (var impl in program.Implementations)
        {
          foreach (var block in impl.Blocks)
          {
            foreach (var cmd in block.Cmds)
            {
              if (cmd is AssertCmd ac &&
                  (ac.Description is MeasureDecreasesDescription ||
                   ac.Description is MeasureNonNegativeDescription))
              {
                ac.Emit(wr, 0);
                options.OutputWriter.WriteLine();
              }
            }
          }
        }

        // print inserted requires
        foreach (var proc in program.Procedures)
        {
          foreach (var req in proc.Requires)
          {
            if (req.Description is MeasureNonNegativeDescription)
            {
              req.Emit(wr, 0);
              options.OutputWriter.WriteLine();
            }
          }
        }
      }

      return program;
    }
  }
}