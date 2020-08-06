using NUnit.Framework;
using Microsoft.Boogie;

namespace TestUtil
{
  public class ProgramLoader
  {
    public static Program LoadProgramFrom(string programText, string fileName = "file.bpl")
    {
      Assert.That(programText, Is.Not.Null.And.Not.Empty);
      Assert.That(fileName, Is.Not.Null.And.Not.Empty);


      int errors = 0;
      Program p = null;
      errors = Parser.Parse(programText, fileName, out p, /*useBaseName=*/false);
      Assert.AreEqual(0, errors);
      Assert.IsNotNull(p);

      // Resolve
      errors = p.Resolve();
      Assert.AreEqual(0, errors);

      // Type check
      errors = p.Typecheck();
      Assert.AreEqual(0, errors);

      return p;
    }
  }
}