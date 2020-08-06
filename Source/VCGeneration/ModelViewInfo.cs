using System.Collections.Generic;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;
using Set = Microsoft.Boogie.GSet<object>;

namespace VC
{
  public class ModelViewInfo
  {
    public readonly List<Variable> AllVariables = new List<Variable>();
    public readonly List<Mapping> CapturePoints = new List<Mapping>();

    public static readonly Function MVState_FunctionDef = new Function(Token.NoToken, "$mv_state",
      new List<Variable>
      {
        new Formal(Token.NoToken, new TypedIdent(Token.NoToken, TypedIdent.NoName, Bpl.Type.Int), true),
        new Formal(Token.NoToken, new TypedIdent(Token.NoToken, TypedIdent.NoName, Bpl.Type.Int), true)
      },
      new Formal(Token.NoToken, new TypedIdent(Token.NoToken, TypedIdent.NoName, Bpl.Type.Bool), false));

    public static readonly Constant MVState_ConstantDef =
      new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "$mv_state_const", Bpl.Type.Int));

    public ModelViewInfo(Program program, Implementation impl)
    {
      Contract.Requires(program != null);
      Contract.Requires(impl != null);

      // global variables
      lock (program.TopLevelDeclarations)
      {
        foreach (var v in program.Variables)
        {
          if (!(v is Constant))
          {
            AllVariables.Add(v);
          }
        }
      }

      // implementation parameters
      foreach (Variable p in impl.InParams)
      {
        AllVariables.Add(p);
      }

      foreach (Variable p in impl.OutParams)
      {
        AllVariables.Add(p);
      }

      // implementation locals
      foreach (Variable v in impl.LocVars)
      {
        AllVariables.Add(v);
      }
    }

    public ModelViewInfo(CodeExpr codeExpr)
    {
      Contract.Requires(codeExpr != null);
      // TODO: also need all variables of enclosing scopes (the global variables of the program, the parameters
      // and perhaps locals of the implementation (if any), any enclosing code expressions).

      foreach (Variable v in codeExpr.LocVars)
      {
        AllVariables.Add(v);
      }
    }

    public class Mapping
    {
      public readonly string Description;
      public readonly Dictionary<Variable, Expr> IncarnationMap;

      public Mapping(string description, Dictionary<Variable, Expr> incarnationMap)
      {
        Description = description;
        IncarnationMap = incarnationMap;
      }
    }
  }
}