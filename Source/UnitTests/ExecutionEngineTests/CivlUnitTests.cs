using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading.Tasks;
using Microsoft.Boogie;
using NUnit.Framework;
using TestUtil;
using VC;

namespace ExecutionEngineTests
{
  [TestFixture]
  public class CivlUnitTests
  {
    [TestCase("g := g + h; g := g + h;",
      "g == old(g) + 2 * old(h) && h == old(h)")]
    [TestCase("var t: int; t := nil; g := nil; h := t;",
      "g == nil && h == nil")]
    [TestCase("var t: int; havoc t; assume t >= old(g); g := t;",
      "g >= old(g) && h == old(h)")]
    [TestCase("var t, u: int; havoc t; u := t + t; assume u >= 0; g := u;",
      "(exists t: int :: g == t + t && g >= 0) && h == old(h)")]
    [TestCase("var t, u: int; havoc t; u := t + t; g := u + 1; assume u >= 0;",
      "(exists t: int :: g == t + t + 1 && t + t >= 0) && h == old(h)")]
    [TestCase("var {:pool \"A\"} t: int; havoc g; t := g + 1; g := t + t; g := g + 1;",
      "(exists a, t: int :: t == a + 1 && g == t + t + 1) && h == old(h)")]
    public async Task TransitionRelationPreservesEliminationSemantics(string commands, string expected)
    {
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      Assert.IsTrue(options.Parse(new[] { "/proverOpt:O:smt.mbqi=true" }));
      var program = ProgramLoader.LoadProgramFrom(options, $@"
var g, h: int;
const nil: int;
procedure p()
modifies g, h;
{{
  {commands}
}}");
      var typeChecker = new CivlTypeChecker(options, program);
      var frame = program.TopLevelDeclarations.OfType<GlobalVariable>().Cast<Variable>().ToHashSet();
      var relation = TransitionRelationComputation.Refinement(typeChecker, program.Implementations.Single(), frame);
      var checker = ProgramLoader.LoadProgramFrom(options, $@"
var g, h: int;
const nil: int;
procedure p()
modifies g, h;
{{
  havoc g, h;
  assert ({relation}) <==> ({expected});
}}");

      using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      var task = (await engine.GetVerificationTasks(checker)).Single();
      var result = await task.TryRun().ToTask();
      Assert.IsInstanceOf<Completed>(result);
      Assert.AreEqual(SolverOutcome.Valid, ((Completed)result).Result.Outcome, relation.ToString());
    }

    [TestCase("g, h := h, g; assert g > h;", "h > g")]
    [TestCase("g := g + h; g := g + h; assert g > 0;", "g + 2 * h > 0")]
    [TestCase("g := g + 1; havoc h; assert h > g;", "false")]
    [TestCase("g := g + 1; assert g > old(g);", "g + 1 > old(g)")]
    [TestCase("g := g + 1; assert old(g) == 0;", "old(g) == 0")]
    [TestCase("g, old_g := g + 1, old_g + 1; assert g + old(g) + old_g > 0;",
      "g + 1 + old(g) + old_g + 1 > 0")]
    public async Task WlpPreservesAssignmentSemantics(string commands, string expected)
    {
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      var program = ProgramLoader.LoadProgramFrom(options, $@"
var g, h, old_g: int;
procedure p()
modifies g, h, old_g;
{{
  g := g + 7;
  assert {expected};
  {commands}
}}");
      var impl = program.Implementations.Single();
      var block = impl.Blocks.Single();
      var prefix = block.Cmds[0];
      var expectedExpr = ((AssertCmd)block.Cmds[1]).Expr;
      block.Cmds.RemoveRange(0, 2);
      var gate = Microsoft.Boogie.Wlp.HoistAsserts(impl, options).Single();
      var resolutionContext = new ResolutionContext(null, options) { StateMode = ResolutionContext.State.Two };
      gate.Expr.Resolve(resolutionContext);
      Assert.AreEqual(0, resolutionContext.ErrorCount);
      block.Cmds = new List<Cmd> { prefix, new AssertCmd(Token.NoToken, Expr.Iff(gate.Expr, expectedExpr)) };
      impl.StructuredStmts = null;

      using var printed = new StringWriter();
      using (var writer = new TokenTextWriter(printed, options))
      {
        program.Emit(writer);
      }
      program = ProgramLoader.LoadProgramFrom(options, printed.ToString());

      using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      var task = (await engine.GetVerificationTasks(program)).Single();
      var result = await task.TryRun().ToTask();
      Assert.IsInstanceOf<Completed>(result);
      Assert.AreEqual(SolverOutcome.Valid, ((Completed)result).Result.Outcome);
    }

    [Test]
    public void WlpScopesPoolHintsIndependentlyAndFiltersHavocDependencies()
    {
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      var program = ProgramLoader.LoadProgramFrom(options, @"
procedure p(i: int)
{
  var t, u: int;
  t := i + 1;
  u := u + 1;
  assert {:add_to_pool ""A"", t, u, i} {:msg ""unchanged""} t > i;
}");
      var impl = program.Implementations.Single();
      var gate = Microsoft.Boogie.Wlp.HoistAsserts(impl, options).Single();
      var pool = gate.Attributes;
      Assert.AreEqual("add_to_pool", pool.Key);
      Assert.AreEqual(3, pool.Params.Count);
      Assert.IsInstanceOf<LetExpr>(pool.Params[1]);
      var hint = (Expr)pool.Params[1];
      var freeVariables = new GSet<object>();
      hint.ComputeFreeVariables(freeVariables);
      CollectionAssert.AreEquivalent(impl.InParams, freeVariables.OfType<Variable>());
      Assert.AreEqual(Type.Int, hint.Type);
      Assert.AreEqual("msg", pool.Next.Key);
      Assert.AreEqual("unchanged", pool.Next.Params.Single());
    }
  }
}
