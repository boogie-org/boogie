using NUnit.Framework;
using System;
using Microsoft.Boogie;

namespace TestUtil
{
	public class ProgramLoader
	{
		public static Program LoadProgramFrom(string programText, string fileName="file.bpl")
		{
			Assert.IsNotNullOrEmpty (programText);
			Assert.IsNotNullOrEmpty (fileName);


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

