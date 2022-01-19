using Microsoft.Boogie;
using NUnit.Framework;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class SolverLogStabilityTest
  {
    [Test()]
    public void OrderIsNormalisedBasedOnContent()
    {
      var procedure1 = @"
type Person;
function A(Person) returns (int) uses {
  axiom (forall p: Person :: name(p) == ""Remy"" ==> A(p) == 32);
}
function B(Person) returns (int) uses {
  axiom (forall p: Person :: name(p) == ""Remy"" ==> B(p) == 180);
}
function name(Person) returns (string);
procedure M(p: Person) 
  requires name(p) == ""Remy"";
  ensures A(p) == 32; 
  ensures B(p) == 180; 
{
}";

      var procedure2 = @"
function name(Person) returns (string);
type Person;
function A(Person) returns (int) uses {
  axiom (forall p: Person :: name(p) == ""Remy"" ==> A(p) == 180);
}
function B(Person) returns (int) uses {
  axiom (forall p: Person :: name(p) == ""Remy"" ==> B(p) == 32);
}
procedure M(p: Person) 
  requires name(p) == ""Remy"";
  ensures B(p) == 32; 
  ensures A(p) == 180;
{
}";

      var options = CommandLineOptions.FromArguments();
      options.NormalizeNames = true;
      options.EmitDebugInformation = false;
      
      var proverLog1 = GetProverLogs.GetProverLogForProgram(options, procedure1);
      var proverLog2 = GetProverLogs.GetProverLogForProgram(options, procedure2);
      Assert.AreEqual(proverLog1, proverLog2);
      
      options.NormalizeDeclarationOrder = false;
      var proverLog3 = GetProverLogs.GetProverLogForProgram(options, procedure2);
      Assert.AreNotEqual(proverLog1, proverLog3);
    }
    
    [Test()]
    public void TurnOffEmitDebugInformation()
    {
      var procedure = @"
procedure M(x: int) 
  requires x == 2; {
  assert (exists y:int :: x + y + x - y == 4);
  assert (forall y:int :: x + y + x - y == 4);
}";
      
      var options = CommandLineOptions.FromArguments();
      
      var proverLog1 = GetProverLogs.GetProverLogForProgram(options, procedure);
      Assert.True(proverLog1.Contains("skolemid"));
      Assert.True(proverLog1.Contains("qid"));
      Assert.True(proverLog1.Contains(":boogie-vc-id"));
      
      options.EmitDebugInformation = false;
      
      var proverLog2 = GetProverLogs.GetProverLogForProgram(options, procedure);
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
      
      var options = CommandLineOptions.FromArguments();
      options.NormalizeNames = true;
      
      var proverLog1 = GetProverLogs.GetProverLogForProgram(options, procedure1);
      var proverLog2 = GetProverLogs.GetProverLogForProgram(options, procedure2);
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
      var options = CommandLineOptions.FromArguments();
      
      var proverLog1 = GetProverLogs.GetProverLogForProgram(options, procedure1);
      CommandLineOptions.Clo.ProcsToCheck.Add("M");
      var proverLog2 = GetProverLogs.GetProverLogForProgram(options, procedure1And2);
      Assert.AreEqual(proverLog1, proverLog2);
      var proverLog3 = GetProverLogs.GetProverLogForProgram(options, procedure2And1);
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
      var options = CommandLineOptions.FromArguments();
      options.Prune = true;
      
      var proverLog1 = GetProverLogs.GetProverLogForProgram(options, procedure1);
      CommandLineOptions.Clo.ProcsToCheck.Add("M");
      var proverLog2 = GetProverLogs.GetProverLogForProgram(options, procedure1And2);
      Assert.AreEqual(proverLog1, proverLog2);
      var proverLog3 = GetProverLogs.GetProverLogForProgram(options, procedure2And1);
      Assert.AreEqual(proverLog3, proverLog2);
    }
  }  
}

