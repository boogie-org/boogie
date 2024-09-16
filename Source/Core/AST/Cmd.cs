using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Boogie;

/// <summary>
/// Could have also been called a statement.
///
/// Does not include commands that contain other commands,
/// for those, look at StructuredCmd
/// 
/// </summary>
[ContractClass(typeof(CmdContracts))]
public abstract class Cmd : Absy
{
  public List<int> Layers;
    
  public byte[] Checksum { get; internal set; }
  public byte[] SugaredCmdChecksum { get; internal set; }
  public bool IrrelevantForChecksumComputation { get; set; }

  public Cmd(IToken /*!*/ tok)
    : base(tok)
  {
    Contract.Assert(tok != null);
  }

  public abstract void Emit(TokenTextWriter /*!*/ stream, int level);

  /// <summary>
  /// Should only be called after resolution
  /// </summary>
  public IEnumerable<Variable> GetAssignedVariables() {
    List<IdentifierExpr> ids = new();
    AddAssignedIdentifiers(ids);
    return ids.Select(id => id.Decl);
  }
    
  public abstract void AddAssignedIdentifiers(List<IdentifierExpr> /*!*/ vars);

  protected void CheckAssignments(TypecheckingContext tc)
  {
    Contract.Requires(tc != null);
    var /*!*/ vars = GetAssignedVariables().ToList();
    foreach (Variable /*!*/ v in vars)
    {
      Contract.Assert(v != null);
      if (!v.IsMutable)
      {
        tc.Error(this, "command assigns to an immutable variable: {0}", v.Name);
      }
      else if (tc.CheckModifies && v is GlobalVariable)
      {
        if (!tc.Yields && !tc.InFrame(v))
        {
          tc.Error(this,
            "command assigns to a global variable that is not in the enclosing {0} modifies clause: {1}",
            tc.Proc is ActionDecl ? "action's" : "procedure's", v.Name);
        }
      }
    }
  }

  // Methods to simulate the old SimpleAssignCmd and MapAssignCmd
  public static AssignCmd SimpleAssign(IToken tok, IdentifierExpr lhs, Expr rhs)
  {
    Contract.Requires(rhs != null);
    Contract.Requires(lhs != null);
    Contract.Requires(tok != null);
    Contract.Ensures(Contract.Result<AssignCmd>() != null);
    List<AssignLhs /*!*/> /*!*/
      lhss = new List<AssignLhs /*!*/>();
    List<Expr /*!*/> /*!*/
      rhss = new List<Expr /*!*/>();

    lhss.Add(new SimpleAssignLhs(lhs.tok, lhs));
    rhss.Add(rhs);

    return new AssignCmd(tok, lhss, rhss);
  }

  public static AssignCmd /*!*/ MapAssign(IToken tok,
    IdentifierExpr /*!*/ map,
    List<Expr> /*!*/ indexes, Expr /*!*/ rhs)
  {
    Contract.Requires(tok != null);
    Contract.Requires(map != null);
    Contract.Requires(indexes != null);
    Contract.Requires(rhs != null);
    Contract.Ensures(Contract.Result<AssignCmd>() != null);
    List<AssignLhs /*!*/> /*!*/
      lhss = new List<AssignLhs /*!*/>();
    List<Expr /*!*/> /*!*/
      rhss = new List<Expr /*!*/>();
    List<Expr /*!*/> /*!*/
      indexesList = new List<Expr /*!*/>();


    foreach (Expr e in indexes)
    {
      indexesList.Add(cce.NonNull(e));
    }

    lhss.Add(new MapAssignLhs(map.tok,
      new SimpleAssignLhs(map.tok, map),
      indexesList));
    rhss.Add(rhs);

    return new AssignCmd(tok, lhss, rhss);
  }

  public static AssignCmd /*!*/ MapAssign(IToken tok,
    IdentifierExpr /*!*/ map,
    params Expr[] /*!*/ args)
  {
    Contract.Requires(tok != null);
    Contract.Requires(map != null);
    Contract.Requires(args != null);
    Contract.Requires(args.Length > 0); // at least the rhs
    Contract.Requires(Contract.ForAll(args, i => i != null));
    Contract.Ensures(Contract.Result<AssignCmd>() != null);

    List<AssignLhs /*!*/> /*!*/
      lhss = new List<AssignLhs /*!*/>();
    List<Expr /*!*/> /*!*/
      rhss = new List<Expr /*!*/>();
    List<Expr /*!*/> /*!*/
      indexesList = new List<Expr /*!*/>();

    for (int i = 0; i < args.Length - 1; ++i)
    {
      indexesList.Add(cce.NonNull(args[i]));
    }

    lhss.Add(new MapAssignLhs(map.tok,
      new SimpleAssignLhs(map.tok, map),
      indexesList));
    rhss.Add(cce.NonNull(args[^1]));

    return new AssignCmd(tok, lhss, rhss);
  }

  /// <summary>
  /// This is a helper routine for printing a linked list of attributes.  Each attribute
  /// is terminated by a space.
  /// </summary>
  public static void EmitAttributes(TokenTextWriter stream, QKeyValue attributes)
  {
    Contract.Requires(stream != null);

    if (stream.UseForComputingChecksums)
    {
      return;
    }

    for (QKeyValue kv = attributes; kv != null; kv = kv.Next)
    {
      kv.Emit(stream);
      stream.Write(" ");
    }
  }

  [Pure]
  public override string ToString() {
    Contract.Ensures(Contract.Result<string>() != null);
    System.IO.StringWriter buffer = new System.IO.StringWriter();
    using TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, false, false, PrintOptions.Default);
    this.Emit(stream, 0);

    return buffer.ToString();
  }
}