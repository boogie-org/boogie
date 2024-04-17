using System;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests;

[TestFixture]
public class RandomSeedTest
{
  private const int randomSeed = 12312314;

  private const string program = @"
  const N: int;
  axiom 3 <= N;
  axiom N <= 3;

  procedure nEquals3()
  ensures true;
  {
  }";

  private static string GetProgramWithAttribute(int randomSeed)
  {
    return program.Replace("procedure", $"procedure {{:random_seed {randomSeed}}}");
  }
  
  [Test]
  public async Task AttributeAndCommandLineOptionProduceSameResult()
  {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.RandomSeed = randomSeed;
    var randomOptionsLogs = await GetProverLogs.GetProverLogForProgram(options, program);
    var randomAttributeLogs = await
      GetProverLogs.GetProverLogForProgram(CommandLineOptions.FromArguments(TextWriter.Null), GetProgramWithAttribute(randomSeed));
    Assert.AreEqual(randomOptionsLogs, randomAttributeLogs);
  }

  [Test]
  public async Task Z3RandomisationOptionsAreSet()
  {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.RandomSeed = randomSeed;
    var randomOptionsLogs = await GetProverLogs.GetProverLogForProgram(options, program);
    Assert.IsTrue(randomOptionsLogs.Contains("(set-option :smt.random_seed 12312314)"));
    Assert.IsTrue(randomOptionsLogs.Contains("(set-option :sat.random_seed 12312314)"));
  } 

  [Test]
  public async Task DeclarationOrderIsRandomised()
  {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.NormalizeDeclarationOrder = false;
    var noRandomLogs = await GetProverLogs.GetProverLogForProgram(options, program);
    options.RandomSeed = 10000;
    var randomOptionsLogs = await GetProverLogs.GetProverLogForProgram(options, program);
    var assertN3 = "(assert (<= N 3)";
    var randomN3Index = randomOptionsLogs.IndexOf(assertN3, StringComparison.Ordinal)!;
    var noRandomN3Index = noRandomLogs.IndexOf(assertN3, StringComparison.Ordinal)!;
    var assert3N = "(assert (<= 3 N)";
    var random3NIndex = randomOptionsLogs.IndexOf(assert3N, StringComparison.Ordinal)!;
    var noRandom3NIndex = noRandomLogs.IndexOf(assert3N, StringComparison.Ordinal)!;
    
    var noRandomOrder = noRandomN3Index.CompareTo(noRandom3NIndex);
    var randomOrder = randomN3Index.CompareTo(random3NIndex);
    Assert.AreNotEqual(noRandomOrder, randomOrder);
  }

  [Test]
  public async Task SomeVariablesAreRenamed()
  {
    var options = CommandLineOptions.FromArguments(TextWriter.Null);
    options.RandomSeed = randomSeed;
    options.NormalizeNames = true;
    var randomOptionsLogs = await GetProverLogs.GetProverLogForProgram(options, program);
    Assert.IsTrue(randomOptionsLogs.Contains("random506996257"));
  }
}
