using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using NUnit.Framework;

namespace CoreTests
{
  /// <summary>
  /// BinaryOperator.Emit drops parentheses its binding powers make redundant. An error there is not
  /// cosmetic: a printed program that re-parses differently changes what gets verified.
  ///
  /// The check is preservation of meaning, not structural identity -- "a + (b + c)" may legitimately
  /// print as "a + b + c" on int and real, which Test/test0/PrettyPrint.bpl pins down. So rather than
  /// read the fragileLeftContext/fragileRightContext table, enumerate every same-precedence operator
  /// pair against every operand type and re-parse.
  ///
  /// Adding redundant parentheses is sound and so passes here; the golden files catch that instead.
  /// </summary>
  [TestFixture]
  public class ExprPrintRoundTrip
  {
    /// <summary>
    /// Operators that both typecheck at each type and return it, so the result can be assigned back
    /// and nested again. That excludes "div"/"mod" outside int, and "/" outside real and float (on
    /// ints it returns real). All bind at 0x40 ("+", "-") or 0x50 (the rest) -- the two levels Emit
    /// can drop parentheses within.
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
            // Only same-precedence pairs can lose parentheses; the rest are cheap extra coverage.
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
    /// The regroupings the printer may perform, stated independently of BinaryOperator.RegroupsWith
    /// so that a wrong rule there cannot make these tests agree with it.
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

      // The AST changed, so the printer reassociated. Only a right-nested operand can: printing is
      // left-associative, so "(a op b) op' c" never had parentheses to drop.
      Assert.IsTrue(nestRight && MayReassociate(type, outer, inner),
        $"printing \"{body}\" as \"{printed}\" changed the expression"
        + $" (re-parsed as \"{reParsed}\")");
    }

    /// <summary>
    /// /print runs before ResolveAndTypecheck, leaving every Expr.Type null, so Emit cannot tell an
    /// int from a float. It must therefore keep the parentheses: here the round-trip has to be
    /// structural, not just meaning-preserving.
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
    /// Parses "expr" as the right-hand side of an assignment over variables of the given type.
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
        // the printer to see the operators, but leaves every Expr.Type null.
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
