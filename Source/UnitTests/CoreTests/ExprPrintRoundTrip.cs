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
    /// Parses "expr" as the right-hand side of an assignment over three variables of the given type,
    /// and returns the resolved, typechecked expression. Typechecking matters: BinaryOperator.Emit
    /// consults operand types, so an untypechecked expression exercises a different path.
    /// </summary>
    private static Expr ParseExprInProcedure(string type, string expr)
    {
      var options = CommandLineOptions.FromArguments(TextWriter.Null);
      var program = TestUtil.ProgramLoader.LoadProgramFrom(options, $@"
        procedure main()
        {{
          var a, b, c, r: {type};
          r := {expr};
        }}", "roundtrip.bpl");

      var typeErrors = program.Typecheck(options);
      Assert.AreEqual(0, typeErrors, $"\"{expr}\" did not typecheck at type {type}");

      var assign = program.Implementations
        .SelectMany(i => i.Blocks)
        .SelectMany(b => b.Cmds)
        .OfType<AssignCmd>()
        .Single();
      return assign.Rhss.Single();
    }
  }
}
