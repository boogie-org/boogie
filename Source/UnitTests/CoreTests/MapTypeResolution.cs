using System.Collections.Generic;
using System.IO;
using Microsoft.Boogie;
using NUnit.Framework;

namespace CoreTests
{
  [TestFixture()]
  public class MapTypeResolution : IErrorSink
  {
    private readonly List<string> errors = new();

    public void Error(IToken tok, string msg)
    {
      errors.Add(msg);
    }

    // The grammar has no map type without arguments, but a program built through the API can contain one.
    [Test()]
    public void MapTypeWithoutArguments()
    {
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      var type = new MapType(Token.NoToken, new List<TypeVariable>(), new List<Microsoft.Boogie.Type>(), BasicType.Int);
      var program = new Program();
      program.AddTopLevelDeclaration(new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "m", type)));

      program.Resolve(new ResolutionContext(this, options));

      Assert.AreEqual(new List<string> { "map type must have at least one argument" }, errors);
    }
  }
}
