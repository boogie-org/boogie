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
    public void OrderIsNormalised()
    {
      var procedure1 = @"
type Person;
function height(Person) returns (int);
function age(Person) returns (int);
axiom (forall p: Person :: name(p) == ""Remy"" ==> height(p) == 180);
function name(Person) returns (string);
axiom (forall p: Person :: name(p) == ""Remy"" ==> age(p) == 32);
procedure M(p: Person) 
  requires name(p) == ""Remy"";
  ensures age(p) == 32; 
  ensures height(p) == 180; 
{
}";
      
      var procedure2 = @"
function name(Person) returns (string);
type Person;
axiom (forall p: Person :: name(p) == ""Remy"" ==> age(p) == 32);
axiom (forall p: Person :: name(p) == ""Remy"" ==> height(p) == 180);
function age(Person) returns (int);
function height(Person) returns (int);
procedure M(p: Person) 
  requires name(p) == ""Remy"";
  ensures age(p) == 32; 
  ensures height(p) == 180;
{
}";
      
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      CommandLineOptions.Clo.EmitSkolimIdAndQId = false;
      ExecutionEngine.printer = new ConsolePrinter();
    
      var proverLog1 = GetProverLogForProgram(procedure1);
      var proverLog2 = GetProverLogForProgram(procedure2);
      Assert.AreEqual(proverLog1, proverLog2);
    }
      
    [Test()]
    public void TurnOffEmitSkolimIdAndQId()
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
      
      CommandLineOptions.Install(new CommandLineOptions());
      CommandLineOptions.Clo.Parse(new string[]{});
      CommandLineOptions.Clo.EmitSkolimIdAndQId = false;
      ExecutionEngine.printer = new ConsolePrinter();
      var proverLog2 = GetProverLogForProgram(procedure);
      Assert.True(!proverLog2.Contains("skolemid"));
      Assert.True(!proverLog2.Contains("qid"));
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
      
      var proverLog1 = GetProverLogsForProgram(procedure1).ToList();
      CommandLineOptions.Clo.ProcsToCheck.Add("M");
      var proverLog2 = GetProverLogsForProgram(procedure1And2).ToList();
      Assert.AreEqual(proverLog1.Count, proverLog2.Count);
      Assert.AreEqual(proverLog1[0], proverLog2[0]);
      var proverLog3 = GetProverLogsForProgram(procedure2And1).ToList();
      Assert.AreEqual(proverLog3[0], proverLog2[0]);
    }
    
    [Test()]
    public void ConstantsFunctionsAxiomsAndTypesAreIsolated()
    {
      var procedure1 = @"
type Wicket;
const w : Wicket;
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
      
      var proverLog1 = GetProverLogsForProgram(procedure1).ToList();
      CommandLineOptions.Clo.ProcsToCheck.Add("M");
      var proverLog2 = GetProverLogsForProgram(procedure1And2).ToList();
      Assert.AreEqual(proverLog1.Count, 1);
      Assert.AreEqual(proverLog1.Count, proverLog2.Count);
      Assert.AreEqual(proverLog1[0], proverLog2[0]);
      var proverLog3 = GetProverLogsForProgram(procedure2And1).ToList();
      Assert.AreEqual(proverLog3[0], proverLog2[0]);
    }

    private static string GetProverLogForProgram(string procedure1)
    {
      var logs = GetProverLogsForProgram(procedure1).ToList();
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

