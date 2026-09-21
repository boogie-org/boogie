using System.Linq;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
  /// <summary>
  /// The symbols Boogie declares for its own encoding when it hands a program to a solver. A
  /// `{:builtin ...}` function naming one of these would share it, so an axiom about the function would
  /// constrain the encoding; Function.Typecheck rejects that.
  ///
  /// Not to be confused with SMTLibNameUtils.reservedSmtWordsList, which exists so a colliding Boogie
  /// *identifier* can be renamed. Renaming is not available here: the point of the attribute is to name
  /// a symbol exactly.
  ///
  /// Harvested with `boogie PROGRAM.bpl -typeEncoding:p -proverLog:out.smt2` over a program that
  /// exercises the type encoding, then reading out.smt2's declarations. A symbol missing below is one a
  /// user can still capture, so re-harvest when the encoding changes. The names built from a type's own
  /// name are matched by shape instead of listed -- see IsBoxedTypeName.
  /// </summary>
  public static class EmittedSymbols
  {
    private static readonly string[] Names =
    {
      "ControlFlow", "Ctor", "tickleBool",
      "int_2_U", "U_2_int", "bool_2_U", "U_2_bool", "real_2_U", "U_2_real",
      "real_pow", "UOrdering2", "UOrdering3", "type",
    };

    // The map-type helpers and boxed type sorts have one member per arity or per type, and `q@` is the
    // prefix put on a renamed identifier.
    private static readonly string[] Prefixes = { "MapType", "T@", "q@" };

    public static bool Contains(string name)
    {
      return Names.Contains(name) || Prefixes.Any(name.StartsWith) || IsBoxedTypeName(name);
    }

    /// <summary>
    /// TypeErasure names the constructor of a boxed type after the type itself -- `NType`, plus one
    /// `NTypeInv&lt;i&gt;` per argument -- so which names those are depends on the program. Matching the shape
    /// rather than deriving the set keeps this answerable from one declaration, and costs nothing: no
    /// solver names a function this way.
    /// </summary>
    private static bool IsBoxedTypeName(string name)
    {
      return name.EndsWith("Type") || Regex.IsMatch(name, "TypeInv[0-9]+$");
    }
  }
}
