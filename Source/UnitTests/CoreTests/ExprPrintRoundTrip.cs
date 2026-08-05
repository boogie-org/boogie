using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using NUnit.Framework;

namespace CoreTests
{
  /// <summary>
  /// The printer omits parentheses wherever the binding powers in BinaryOperator.Emit make them
  /// redundant. Getting that wrong is not a cosmetic bug: a printed program that re-parses to a
  /// different expression silently changes what gets verified.
  ///
  /// The printer is allowed to reassociate where that is sound -- "a + (b + c)" may print as
  /// "a + b + c" on int and real, and Test/test0/PrettyPrint.bpl pins that flattening down. So the
  /// property checked here is not structural identity but preservation of meaning: re-parsing the
  /// printed text must yield either the same AST or a provably equal regrouping.
  ///
  /// Rather than trust the fragileLeftContext/fragileRightContext table by inspection, these tests
  /// enumerate every same-precedence operator pair against every operand type. Any future edit that
  /// drops a parenthesis it should have kept -- on floats, or across "div"/"mod"/"/" -- fails here.
  ///
  /// Note what this deliberately does not check: a change that adds redundant parentheses is sound,
  /// so it passes. Output that is merely uglier than necessary is caught by the golden files
  /// (Test/test0/PrettyPrint.bpl and Test/test0/PrintAssoc.bpl), not here.
  /// </summary>
  [TestFixture]
  public class ExprPrintRoundTrip
  {
    /// <summary>
    /// Every arithmetic operator that typechecks at each type: "div" and "mod" are int-only, "/" is
    /// real- and float-only. All of these bind at one of the two precedence levels ("+"/"-" at 0x40,
    /// the rest at 0x50) that BinaryOperator.Emit can strip parentheses within.
    /// </summary>
    private static readonly (string Type, string[] Operators)[] TypedOperators = {
      ("int", new[] { "+", "-", "*", "div", "mod" }),
      ("real", new[] { "+", "-", "*", "/" }),
      ("float24e8", new[] { "+", "-", "*", "/" })
    };

    private static IEnumerable<TestCaseData> NestedCases()
    {
      foreach (var (type, ops) in TypedOperators)
      {
        foreach (var outer in ops)
        {
          foreach (var inner in ops)
          {
            // Only same-precedence pairs can lose parentheses, but feeding every pair through
            // costs nothing and guards the cross-precedence cases too.
            yield return new TestCaseData(type, outer, inner, true).SetName(
              $"RightNested_{type}_{Sanitize(outer)}_{Sanitize(inner)}");
            yield return new TestCaseData(type, outer, inner, false).SetName(
              $"LeftNested_{type}_{Sanitize(outer)}_{Sanitize(inner)}");
          }
        }
      }
    }

    private static string Sanitize(string op) =>
      op.Replace("+", "add").Replace("-", "sub").Replace("*", "mul").Replace("/", "rdiv");

    /// <summary>
    /// The only regroupings the printer may perform. On int and real, "+" is associative and absorbs
    /// a nested "-" ("a + (b - c)" = "(a + b) - c"), and "*" is associative. Everything else -- any
    /// float, and "div"/"mod"/"/" at any type -- must keep its parentheses, either because rounding
    /// makes the operator non-associative or because truncation and division by zero make the two
    /// groupings differ.
    /// </summary>
    private static bool MayReassociate(string type, string outer, string inner)
    {
      if (type != "int" && type != "real")
      {
        return false;
      }

      return outer switch
      {
        "+" => inner is "+" or "-",
        "*" => inner is "*",
        _ => false
      };
    }

    [TestCaseSource(nameof(NestedCases))]
    public void PrintedExpressionPreservesMeaning(string type, string outer, string inner, bool nestRight)
    {
      var body = nestRight ? $"a {outer} (b {inner} c)" : $"(a {inner} b) {outer} c";
      var original = ParseExprInProcedure(type, body);

      var printed = original.ToString();
      var reParsed = ParseExprInProcedure(type, printed);

      if (original.ContentHash == reParsed.ContentHash)
      {
        return;
      }

      // The AST changed, so the printer reassociated. That is only allowed for the left-associative
      // regroupings above; a right-nested operand at any other type or operator must have kept its
      // parentheses and so must have round-tripped exactly.
      Assert.IsTrue(nestRight && MayReassociate(type, outer, inner),
        $"printing \"{body}\" as \"{printed}\" changed the expression"
        + $" (re-parsed as \"{reParsed}\")");
    }

    /// <summary>
    /// /print emits the program before ResolveAndTypecheck runs, so on that path every Expr.Type is
    /// still null and Emit cannot tell an int from a float. Reassociating there would be unsound for
    /// exactly the float programs this guards, so with no type information the parentheses have to
    /// stay -- printing must round-trip structurally, not just semantically.
    /// </summary>
    [TestCaseSource(nameof(NestedCases))]
    public void PrintingBeforeTypecheckingKeepsParentheses(string type, string outer, string inner, bool nestRight)
    {
      var body = nestRight ? $"a {outer} (b {inner} c)" : $"(a {inner} b) {outer} c";
      var original = ParseExprInProcedure(type, body, typecheck: false);
      Assert.IsNull(original.Type, "expression was typechecked; this test must exercise the null-type path");

      var printed = original.ToString();
      var reParsed = ParseExprInProcedure(type, printed, typecheck: false);

      Assert.AreEqual(original.ContentHash, reParsed.ContentHash,
        $"before typechecking, printing \"{body}\" as \"{printed}\" changed the expression"
        + $" (re-parsed as \"{reParsed}\")");
    }

    /// <summary>
    /// Parses "expr" as the right-hand side of an assignment over three variables of the given type.
    /// Typechecking matters: BinaryOperator.Emit consults operand types, so a typechecked and an
    /// untypechecked expression exercise different paths. Pass typecheck: false to reach the latter,
    /// which is what /print does.
    /// </summary>
    private static Expr ParseExprInProcedure(string type, string expr, bool typecheck = true)
    {
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      var programText = $@"
        procedure main()
        {{
          var a, b, c, r: {type};
          r := {expr};
        }}";

      Program program;
      if (typecheck)
      {
        program = TestUtil.ProgramLoader.LoadProgramFrom(options, programText, "roundtrip.bpl");
      }
      else
      {
        // ProgramLoader always typechecks, so parse and resolve by hand. Resolution is needed for
        // the printer to see the operators at all, but it leaves every Expr.Type null.
        Assert.AreEqual(0, Parser.Parse(programText, "roundtrip.bpl", out program, useBaseName: false));
        Assert.AreEqual(0, program.Resolve(options));
      }

      var assign = program.Implementations
        .SelectMany(i => i.Blocks)
        .SelectMany(b => b.Cmds)
        .OfType<AssignCmd>()
        .Single();
      return assign.Rhss.Single();
    }
  }
}
