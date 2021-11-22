using Microsoft.Boogie;
using NUnit.Framework;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class ProofIsolation
  {
    [Test()]
    public void TurnOffEmitDebugInformation()
    {
      var procedure = @"
procedure M(x: int) 
  requires x == 2; {
  assert (exists y:int :: x + y + x - y == 4);
  assert (forall y:int :: x + y + x - y == 4);
}";
      
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      ExecutionEngine.printer = new ConsolePrinter();
      
      var proverLog1 = GetProverLogForProgram(procedure);
      Assert.True(proverLog1.Contains("skolemid"));
      Assert.True(proverLog1.Contains("qid"));
      Assert.True(proverLog1.Contains(":boogie-vc-id"));
      
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      CommandLineOptions.Clo.EmitDebugInformation = false;
      ExecutionEngine.printer = new ConsolePrinter();
      
      var proverLog2 = GetProverLogForProgram(procedure);
      Assert.True(!proverLog2.Contains("skolemid"));
      Assert.True(!proverLog2.Contains("qid"));
      Assert.True(!proverLog2.Contains(":boogie-vc-id"));
    }

    [Test()]
    public void TestNameDiscarding()
    {
      var procedure1 = @"
type Wicket;
const w: Wicket;
function age(Wicket) returns (int);
axiom age(w) == 7;

var favorite: Wicket;
var alternative: Wicket;

type Barrel a;
type RGBColor;
const unique red: RGBColor;
const unique green: RGBColor;
const unique blue: RGBColor;

const m: [Barrel Wicket] Wicket;
const n: <a> [Barrel a] a;

type MySynonym a = int;
type ComplicatedInt = MySynonym (MySynonym bool);

procedure M(x: int, coloredBarrel: Barrel RGBColor)
  requires x == 2; 
  modifies favorite;
  ensures age(favorite) == 42; 
{
  var y: ComplicatedInt;
  favorite := alternative;
  assert y == 3;
}
";
      
      var procedure2 = @"
type Wicket2;
const w2 : Wicket2;
function age2(Wicket2) returns (int);
axiom age2(w2) == 7;

var favorite2: Wicket2;
var alternative2: Wicket2;

type Barrel2 a;
type RGBColor2;
const unique red2: RGBColor2;
const unique green2: RGBColor2;
const unique blue2: RGBColor2;

const m2: [Barrel2 Wicket2] Wicket2;
const n2: <a2> [Barrel2 a2] a2;

type MySynonym2 a2 = int;
type ComplicatedInt2 = MySynonym2 (MySynonym2 bool);

procedure M(x2: int, coloredBarrel: Barrel2 RGBColor2)
  requires x2 == 2; 
  modifies favorite2;
  ensures age2(favorite2) == 42; 
{
  var y2: ComplicatedInt2;
  favorite2 := alternative2;
  assert y2 == 3;
}
";
      
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      CommandLineOptions.Clo.DiscardNames = true;
      ExecutionEngine.printer = new ConsolePrinter();
      
      var proverLog1 = GetProverLogForProgram(procedure1);
      var proverLog2 = GetProverLogForProgram(procedure2);
      Assert.AreEqual(proverLog1, proverLog2);
    }

    [Test()]
    public void ControlFlowIsIsolated()
    {
      var procedure1 = @"
procedure M(x: int) 
  requires x == 2; {
  assert x + x == 4;
}";
      
      var procedure2 = @"
procedure N(x: int) 
  requires x == 3; {
  assert x * x == 9;
}";
      
      var procedure1And2 = $@"
{procedure1}
{procedure2}";
      
      var procedure2And1 = $@"
{procedure1}
{procedure2}";
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      ExecutionEngine.printer = new ConsolePrinter();
      
      var proverLog1 = GetProverLogForProgram(procedure1);
      CommandLineOptions.Clo.ProcsToCheck.Add("M");
      var proverLog2 = GetProverLogForProgram(procedure1And2);
      Assert.AreEqual(proverLog1, proverLog2);
      var proverLog3 = GetProverLogForProgram(procedure2And1);
      Assert.AreEqual(proverLog3, proverLog2);
    }
    
    [Test()]
    public void ConstantsFunctionsAxiomsAndTypesAreIsolated()
    {
      var procedure1 = @"
type Wicket;
const w: Wicket;
function age(Wicket) returns (int);
axiom age(w) == 7;

var favorite: Wicket;
var alternative: Wicket;

type Barrel a;
type RGBColor;
const unique red: RGBColor;
const unique green: RGBColor;
const unique blue: RGBColor;

const m: [Barrel Wicket] Wicket;
const n: <a> [Barrel a] a;

type MySynonym a = int;
type ComplicatedInt = MySynonym (MySynonym bool);

procedure M(x: int, coloredBarrel: Barrel RGBColor)
  requires x == 2; 
  modifies favorite;
  ensures age(favorite) == 42; 
{
  var y: ComplicatedInt;
  favorite := alternative;
  assert y == 3;
}
";
      
      var procedure2 = @"
type Wicket2;
const w2 : Wicket2;
function age2(Wicket2) returns (int);
axiom age2(w2) == 7;

var favorite2: Wicket2;
var alternative2: Wicket2;

type Barrel2 a;
type RGBColor2;
const unique red2: RGBColor2;
const unique green2: RGBColor2;
const unique blue2: RGBColor2;

const m2: [Barrel2 Wicket2] Wicket2;
const n2: <a> [Barrel2 a] a;

type MySynonym2 a = int;
type ComplicatedInt2 = MySynonym2 (MySynonym2 bool);

procedure M2(x: int, coloredBarrel: Barrel2 RGBColor2)
  requires x == 2; 
  modifies favorite2;
  ensures age2(favorite2) == 42; 
{
  var y: ComplicatedInt2;
  favorite2 := alternative2;
  assert y == 3;
}
";
      
      var procedure1And2 = $@"
{procedure1}
{procedure2}";
      
      var procedure2And1 = $@"
{procedure1}
{procedure2}";
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.PruneFunctionsAndAxioms = true;
      CommandLineOptions.Clo.Parse(new string[]{});
      ExecutionEngine.printer = new ConsolePrinter();
      
      var proverLog1 = GetProverLogForProgram(procedure1);
      CommandLineOptions.Clo.ProcsToCheck.Add("M");
      var proverLog2 = GetProverLogForProgram(procedure1And2);
      Assert.AreEqual(proverLog1, proverLog2);
      var proverLog3 = GetProverLogForProgram(procedure2And1);
      Assert.AreEqual(proverLog3, proverLog2);
    }

    private static string GetProverLogForProgram(string procedure)
    {
      var logs = GetProverLogsForProgram(procedure).ToList();
      Assert.AreEqual(1, logs.Count);
      return logs[0];
    }
    
    private static IEnumerable<string> GetProverLogsForProgram(string procedure1)
    {
      var defines = new List<string>() { "FILE_0" };

      // Parse error are printed to StdOut :/
      int errorCount = Parser.Parse(new StringReader(procedure1), "1", defines, out Program program1,
        CommandLineOptions.Clo.UseBaseNameForFileName);
      Assert.AreEqual(0, errorCount);
      string directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
      Directory.CreateDirectory(directory);
      var temp1 = directory + "/proverLog";
      CommandLineOptions.Clo.ProverLogFilePath = temp1;
      var success1 = ExecutionEngine.ProcessProgram(program1, "1");
      foreach (var proverFile in Directory.GetFiles(directory)) {
        yield return File.ReadAllText(proverFile);
      }
    }
  }  
}

