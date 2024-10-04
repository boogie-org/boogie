using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  [ContractClassFor(typeof(Cmd))]
  public abstract class CmdContracts : Cmd
  {
    public CmdContracts() : base(null)
    {
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      Contract.Requires(stream != null);
      throw new NotImplementedException();
    }

    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
      throw new NotSupportedException();
    }
  }

  public static class ChecksumHelper
  {
    public static void ComputeChecksums(CoreOptions options, Cmd cmd, Implementation impl, ISet<Variable> usedVariables,
      byte[] currentChecksum = null)
    {
      if (options.VerifySnapshots < 2)
      {
        return;
      }

      if (cmd.IrrelevantForChecksumComputation)
      {
        cmd.Checksum = currentChecksum;
        return;
      }

      if (cmd is AssumeCmd assumeCmd
          && QKeyValue.FindBoolAttribute(assumeCmd.Attributes, "assumption_variable_initialization"))
      {
        // Ignore assumption variable initializations.
        assumeCmd.Checksum = currentChecksum;
        return;
      }

      using (var strWr = new System.IO.StringWriter())
      using (var tokTxtWr = new TokenTextWriter("<no file>", strWr, false, false, options))
      {
        tokTxtWr.UseForComputingChecksums = true;
        if (cmd is HavocCmd havocCmd)
        {
          tokTxtWr.Write("havoc ");
          var relevantVars = havocCmd.Vars
            .Where(e => usedVariables.Contains(e.Decl) && !e.Decl.Name.StartsWith("a##cached##")).OrderBy(e => e.Name)
            .ToList();
          relevantVars.Emit(tokTxtWr, true);
          tokTxtWr.WriteLine(";");
        }
        else
        {
          cmd.Emit(tokTxtWr, 0);
        }

        var md5 = System.Security.Cryptography.MD5.Create();
        var str = strWr.ToString();
        if (str.Any())
        {
          var data = System.Text.Encoding.UTF8.GetBytes(str);
          var checksum = md5.ComputeHash(data);
          currentChecksum = currentChecksum != null ? CombineChecksums(currentChecksum, checksum) : checksum;
        }

        cmd.Checksum = currentChecksum;
      }

      if (cmd is AssertCmd { Checksum: not null } assertCmd)
      {
        if (assertCmd is AssertRequiresCmd assertRequiresCmd)
        {
          impl.AddAssertionChecksum(assertRequiresCmd.Checksum);
          impl.AddAssertionChecksum(assertRequiresCmd.Call.Checksum);
          assertRequiresCmd.SugaredCmdChecksum = assertRequiresCmd.Call.Checksum;
        }
        else
        {
          impl.AddAssertionChecksum(assertCmd.Checksum);
        }
      }

      if (cmd is SugaredCmd sugaredCmd)
      {
        // The checksum of a sugared command should not depend on the desugaring itself.
        if (sugaredCmd.GetDesugaring(options) is StateCmd stateCmd)
        {
          foreach (var c in stateCmd.Cmds)
          {
            ComputeChecksums(options, c, impl, usedVariables, currentChecksum);
            currentChecksum = c.Checksum;
            c.SugaredCmdChecksum ??= cmd.Checksum;
          }
        }
        else
        {
          ComputeChecksums(options, sugaredCmd.GetDesugaring(options), impl, usedVariables, currentChecksum);
        }
      }
    }

    public static byte[] CombineChecksums(byte[] first, byte[] second, bool unordered = false)
    {
      Contract.Requires(first != null && (second == null || first.Length == second.Length));

      var result = (byte[]) (first.Clone());
      for (int i = 0; second != null && i < second.Length; i++)
      {
        if (unordered)
        {
          result[i] += second[i];
        }
        else
        {
          result[i] = (byte) (result[i] * 31 ^ second[i]);
        }
      }

      return result;
    }
  }

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

    public void CheckAssignments(TypecheckingContext tc)
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
      rhss.Add(cce.NonNull(args[args.Length - 1]));

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
  
  public class CommentCmd : Cmd // just a convenience for debugging
  {
    public readonly string /*!*/
      Comment;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Comment != null);
    }

    public CommentCmd(string c)
      : base(Token.NoToken)
    {
      Contract.Requires(c != null);
      Comment = c;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      if (stream.UseForComputingChecksums)
      {
        return;
      }

      if (this.Comment.Contains("\n"))
      {
        stream.WriteLine(this, level, "/* {0} */", this.Comment);
      }
      else
      {
        stream.WriteLine(this, level, "// {0}", this.Comment);
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
    }
    
    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
    }

    public override void Typecheck(TypecheckingContext tc)
    {
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitCommentCmd(this);
    }
  }

  // class for parallel assignments, which subsumes both the old
  // SimpleAssignCmd and the old MapAssignCmd
  public class AssignCmd : Cmd, ICarriesAttributes
  {
    public QKeyValue Attributes { get; set; }

    private List<AssignLhs> _lhss;

    public IList<AssignLhs> Lhss
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IList<AssignLhs>>()));
        Contract.Ensures(Contract.Result<IList<AssignLhs>>().IsReadOnly);
        return this._lhss.AsReadOnly();
      }
      set
      {
        Contract.Requires(cce.NonNullElements(value));
        this._lhss = new List<AssignLhs>(value);
      }
    }

    internal void SetLhs(int index, AssignLhs lhs)
    {
      Contract.Requires(0 <= index && index < this.Lhss.Count);
      Contract.Requires(lhs != null);
      Contract.Ensures(this.Lhss[index] == lhs);
      this._lhss[index] = lhs;
    }

    private List<Expr> _rhss;

    public IList<Expr> Rhss
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IList<Expr>>()));
        Contract.Ensures(Contract.Result<IList<Expr>>().IsReadOnly);
        return this._rhss.AsReadOnly();
      }
      set
      {
        Contract.Requires(cce.NonNullElements(value));
        this._rhss = new List<Expr>(value);
      }
    }

    internal void SetRhs(int index, Expr rhs)
    {
      Contract.Requires(0 <= index && index < this.Rhss.Count);
      Contract.Requires(rhs != null);
      Contract.Ensures(this.Rhss[index] == rhs);
      this._rhss[index] = rhs;
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(cce.NonNullElements(this._lhss));
      Contract.Invariant(cce.NonNullElements(this._rhss));
    }

    public AssignCmd(IToken tok, IList<AssignLhs> lhss, IList<Expr> rhss, QKeyValue kv)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(cce.NonNullElements(lhss));
      this._lhss = new List<AssignLhs>(lhss);
      this._rhss = new List<Expr>(rhss);
      this.Attributes = kv;
    }

    public AssignCmd(IToken tok, IList<AssignLhs> lhss, IList<Expr> rhss)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(cce.NonNullElements(lhss));
      this._lhss = new List<AssignLhs>(lhss);
      this._rhss = new List<Expr>(rhss);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "");

      string /*!*/
        sep = "";
      foreach (AssignLhs /*!*/ l in Lhss)
      {
        Contract.Assert(l != null);
        stream.Write(sep);
        sep = ", ";
        l.Emit(stream);
      }

      stream.Write(" := ");

      sep = "";
      foreach (Expr /*!*/ e in Rhss)
      {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }

      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc)
    {
      (this as ICarriesAttributes).ResolveAttributes(rc);
      if (Lhss.Count != Rhss.Count)
      {
        rc.Error(this,
          "number of left-hand sides does not match number of right-hand sides");
      }

      foreach (AssignLhs /*!*/ e in Lhss)
      {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }

      foreach (Expr /*!*/ e in Rhss)
      {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }

      // check for double occurrences of assigned variables
      // (could be optimised)
      for (int i = 0; i < Lhss.Count; ++i)
      {
        for (int j = i + 1; j < Lhss.Count; ++j)
        {
          if (cce.NonNull(Lhss[i].DeepAssignedVariable).Equals(
            Lhss[j].DeepAssignedVariable))
          {
            rc.Error(Lhss[j],
              "variable {0} is assigned more than once in parallel assignment",
              Lhss[j].DeepAssignedVariable);
          }
        }
      }

      for (int i = 0; i < Lhss.Count; i++)
      {
        var lhs = Lhss[i] as SimpleAssignLhs;
        if (lhs == null)
        {
          continue;
        }
        var decl = lhs.AssignedVariable.Decl;
        if (lhs.AssignedVariable.Decl != null && QKeyValue.FindBoolAttribute(decl.Attributes, "assumption"))
        {
          var rhs = Rhss[i] as NAryExpr;
          if (rhs == null
              || !(rhs.Fun is BinaryOperator)
              || ((BinaryOperator)rhs.Fun).Op != BinaryOperator.Opcode.And
              || !(rhs.Args[0] is IdentifierExpr)
              || ((IdentifierExpr)rhs.Args[0]).Decl != decl)
          {
            rc.Error(tok,
              string.Format(
                "RHS of assignment to assumption variable {0} must match expression \"{0} && <boolean expression>\"",
                decl.Name));
          }
          else if (rc.HasVariableBeenAssigned(decl.Name))
          {
            rc.Error(tok, "assumption variable may not be assigned to more than once");
          }
          else
          {
            rc.MarkVariableAsAssigned(decl.Name);
          }
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      int errorCount = tc.ErrorCount;

      (this as ICarriesAttributes).TypecheckAttributes(tc);

      var expectedLayerRanges = new List<LayerRange>();
      if (tc.Proc is YieldProcedureDecl)
      {
        foreach (var e in Lhss.Where(e => e.DeepAssignedVariable is GlobalVariable))
        {
          tc.Error(e, $"global variable directly modified in a yield procedure: {e.DeepAssignedVariable.Name}");
        }
        expectedLayerRanges = Lhss.Select(e => e.DeepAssignedVariable.LayerRange).ToList();
      }

      foreach (AssignLhs /*!*/ e in Lhss)
      {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }

      for (int i = 0; i < Rhss.Count; i++)
      {
        var e = Rhss[i];
        Contract.Assert(e != null);
        tc.GlobalAccessOnlyInOld = tc.Proc is YieldProcedureDecl;
        tc.ExpectedLayerRange = tc.Proc is YieldProcedureDecl ? expectedLayerRanges[i] : null;
        e.Typecheck(tc);
        tc.GlobalAccessOnlyInOld = false;
        tc.ExpectedLayerRange = null;
      }

      if (tc.ErrorCount > errorCount)
      {
        // there has already been an error when typechecking the lhs or rhs
        return;
      }

      this.CheckAssignments(tc);

      for (int i = 0; i < Lhss.Count; ++i)
      {
        Type ltype = Lhss[i].Type;
        Type rtype = Rhss[i].Type;
        if (!ltype.Unify(rtype))
        {
          tc.Error(Lhss[i], "mismatched types in assignment command (cannot assign {0} to {1})", rtype, ltype);
        }
      }
    }

    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
      foreach (AssignLhs /*!*/ l in Lhss)
      {
        vars.Add(l.DeepAssignedIdentifier);
      }
    }

    // transform away the syntactic sugar of map assignments and
    // determine an equivalent assignment in which all rhs are simple
    // variables
    public AssignCmd /*!*/ AsSimpleAssignCmd
    {
      get
      {
        Contract.Ensures(Contract.Result<AssignCmd>() != null);

        List<AssignLhs /*!*/> /*!*/
          newLhss = new List<AssignLhs /*!*/>();
        List<Expr /*!*/> /*!*/
          newRhss = new List<Expr /*!*/>();

        for (int i = 0; i < Lhss.Count; ++i)
        {
          Lhss[i].AsSimpleAssignment(Rhss[i], out var newLhs, out var newRhs);
          newLhss.Add(new SimpleAssignLhs(Token.NoToken, newLhs));
          newRhss.Add(newRhs);
        }

        return new AssignCmd(Token.NoToken, newLhss, newRhss, Attributes);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitAssignCmd(this);
    }
  }

  // There are two different kinds of left-hand sides in assignments:
  // simple variables (identifiers), or locations of a map
  [ContractClass(typeof(AssignLhsContracts))]
  public abstract class AssignLhs : Absy
  {
    // The type of the lhs is determined during typechecking
    public abstract Type Type { get; }

    // Determine the variable that is actually assigned in this lhs
    public abstract IdentifierExpr /*!*/ DeepAssignedIdentifier { get; }
    public abstract Variable DeepAssignedVariable { get; }

    public AssignLhs(IToken /*!*/ tok)
      : base(tok)
    {
      Contract.Requires(tok != null);
    }

    public abstract void Emit(TokenTextWriter /*!*/ stream);

    public abstract Expr /*!*/ AsExpr { get; }

    // transform away the syntactic sugar of map assignments and
    // determine an equivalent simple assignment
    internal abstract void AsSimpleAssignment(Expr /*!*/ rhs,
      out IdentifierExpr /*!*/ simpleLhs,
      out Expr /*!*/ simpleRhs);
  }

  [ContractClassFor(typeof(AssignLhs))]
  public abstract class AssignLhsContracts : AssignLhs
  {
    public AssignLhsContracts() : base(null)
    {
    }

    public override IdentifierExpr DeepAssignedIdentifier
    {
      get
      {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
        throw new NotImplementedException();
      }
    }

    public override Expr AsExpr
    {
      get
      {
        Contract.Ensures(Contract.Result<Expr>() != null);
        throw new NotImplementedException();
      }
    }

    internal override void AsSimpleAssignment(Expr rhs, out IdentifierExpr simpleLhs, out Expr simpleRhs)
    {
      Contract.Requires(rhs != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleLhs) != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleRhs) != null);

      throw new NotImplementedException();
    }
  }

  public class SimpleAssignLhs : AssignLhs
  {
    public IdentifierExpr /*!*/
      AssignedVariable;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(AssignedVariable != null);
    }


    public override Type Type => AssignedVariable.Type.Expanded;

    public override IdentifierExpr /*!*/ DeepAssignedIdentifier
    {
      get
      {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);
        return AssignedVariable;
      }
    }

    public override Variable DeepAssignedVariable
    {
      get { return AssignedVariable.Decl; }
    }

    public SimpleAssignLhs(IToken tok, IdentifierExpr assignedVariable)
      : base(tok)
    {
      Contract.Requires(assignedVariable != null);
      Contract.Requires(tok != null);
      AssignedVariable = assignedVariable;
    }

    public override void Resolve(ResolutionContext rc)
    {
      AssignedVariable.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      AssignedVariable.Typecheck(tc);
    }

    public override void Emit(TokenTextWriter stream)
    {
      AssignedVariable.Emit(stream);
    }

    public override Expr /*!*/ AsExpr
    {
      get
      {
        Contract.Ensures(Contract.Result<Expr>() != null);

        return AssignedVariable;
      }
    }

    internal override void AsSimpleAssignment(Expr rhs,
      out IdentifierExpr /*!*/ simpleLhs,
      out Expr /*!*/ simpleRhs)
    {
      simpleLhs = AssignedVariable;
      simpleRhs = rhs;
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitSimpleAssignLhs(this);
    }
  }

  // A map-assignment-lhs (m[t1, t2, ...] := ...) is quite similar to
  // a map select expression, but it is cleaner to keep those two
  // things separate
  public class MapAssignLhs : AssignLhs
  {
    public AssignLhs /*!*/
      Map;

    public List<Expr /*!*/> /*!*/
      Indexes;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Map != null);
      Contract.Invariant(cce.NonNullElements(Indexes));
    }


    // The instantiation of type parameters of the map that is
    // determined during type checking.
    public TypeParamInstantiation TypeParameters = null;

    private Type TypeAttr = null;

    public override Type Type
    {
      get
      {
        if (TypeAttr == null)
        {
          TypeAttr = ((MapType)TypeProxy.FollowProxy(Map.Type.Expanded)).Result.Substitute(
            TypeParameters.FormalTypeParams.ToDictionary(x => x, x => TypeParameters[x]));
        }
        return TypeAttr;
      }
    }

    public override IdentifierExpr /*!*/ DeepAssignedIdentifier
    {
      get
      {
        Contract.Ensures(Contract.Result<IdentifierExpr>() != null);

        return Map.DeepAssignedIdentifier;
      }
    }

    public override Variable DeepAssignedVariable
    {
      get { return Map.DeepAssignedVariable; }
    }

    public MapAssignLhs(IToken tok, AssignLhs map, List<Expr /*!*/> /*!*/ indexes)
      : base(tok)
    {
      Contract.Requires(map != null);
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(indexes));

      Map = map;
      Indexes = indexes;
    }

    public override void Resolve(ResolutionContext rc)
    {
      Map.Resolve(rc);
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        e.Resolve(rc);
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      Map.Typecheck(tc);
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        e.Typecheck(tc);
      }

      // we use the same typechecking code as in MapSelect
      List<Expr> /*!*/
        selectArgs = new List<Expr>();
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        selectArgs.Add(e);
      }

      TypeAttr =
        MapSelect.Typecheck(cce.NonNull(Map.Type), Map,
          selectArgs, out var tpInsts, tc, tok, "map assignment");
      TypeParameters = tpInsts;
    }

    public override void Emit(TokenTextWriter stream)
    {
      Map.Emit(stream);
      stream.Write("[");
      string /*!*/
        sep = "";
      foreach (Expr /*!*/ e in Indexes)
      {
        Contract.Assert(e != null);
        stream.Write(sep);
        sep = ", ";
        e.Emit(stream);
      }

      stream.Write("]");
    }

    public override Expr /*!*/ AsExpr
    {
      get
      {
        Contract.Ensures(Contract.Result<Expr>() != null);

        NAryExpr /*!*/
          res = Expr.Select(Map.AsExpr, Indexes);
        Contract.Assert(res != null);
        res.TypeParameters = this.TypeParameters;
        res.Type = this.Type;
        return res;
      }
    }

    internal override void AsSimpleAssignment(Expr rhs,
      out IdentifierExpr /*!*/ simpleLhs,
      out Expr /*!*/ simpleRhs)
    {
      //Contract.Requires(rhs != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleLhs) != null);
      Contract.Ensures(Contract.ValueAtReturn(out simpleRhs) != null);

      NAryExpr /*!*/
        newRhs = Expr.Store(Map.AsExpr, Indexes, rhs);
      Contract.Assert(newRhs != null);
      newRhs.TypeParameters = this.TypeParameters;
      newRhs.Type = Map.Type;
      Map.AsSimpleAssignment(newRhs, out simpleLhs, out simpleRhs);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitMapAssignLhs(this);
    }
  }

  public class FieldAssignLhs : AssignLhs
  {
    public AssignLhs Datatype;

    public FieldAccess FieldAccess;

    public TypeParamInstantiation TypeParameters = null;

    private Type TypeAttr = null;

    public override Type Type
    {
      get
      {
        if (TypeAttr == null)
        {
          TypeAttr = FieldAccess.Type((CtorType)TypeProxy.FollowProxy(Datatype.Type.Expanded));
        }
        return TypeAttr;
      }
    }

    public override IdentifierExpr DeepAssignedIdentifier => Datatype.DeepAssignedIdentifier;

    public override Variable DeepAssignedVariable => Datatype.DeepAssignedVariable;

    public FieldAssignLhs(IToken tok, AssignLhs datatype, FieldAccess fieldAccess)
      : base(tok)
    {
      Datatype = datatype;
      this.FieldAccess = fieldAccess;
    }

    public override void Resolve(ResolutionContext rc)
    {
      Datatype.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      var errorCount = tc.ErrorCount;
      Datatype.Typecheck(tc);
      TypeParameters = SimpleTypeParamInstantiation.EMPTY;
      if (tc.ErrorCount == errorCount)
      {
        TypeAttr = FieldAccess.Typecheck(Datatype.Type, tc, out TypeParameters);
      }
    }

    public override void Emit(TokenTextWriter stream)
    {
      Datatype.Emit(stream);
      stream.Write("->{0}", FieldAccess.FieldName);
    }

    public override Expr AsExpr
    {
      get
      {
        var res = FieldAccess.Select(tok, Datatype.AsExpr);
        Contract.Assert(res != null);
        res.TypeParameters = this.TypeParameters;
        res.Type = this.Type;
        return res;
      }
    }

    internal override void AsSimpleAssignment(Expr rhs,
      out IdentifierExpr simpleLhs,
      out Expr simpleRhs)
    {
      var newRhs = FieldAccess.Update(tok, Datatype.AsExpr, rhs);
      Contract.Assert(newRhs != null);
      newRhs.TypeParameters = this.TypeParameters;
      newRhs.Type = Datatype.Type;
      Datatype.AsSimpleAssignment(newRhs, out simpleLhs, out simpleRhs);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitFieldAssignLhs(this);
    }
  }

  /// <summary>
  /// UnpackCmd used for unpacking a constructed value into its components.
  /// </summary>
  public class UnpackCmd : SugaredCmd, ICarriesAttributes
  {
    private NAryExpr lhs;
    private Expr rhs;
    private QKeyValue kv;

    public UnpackCmd(IToken tok, NAryExpr lhs, Expr rhs, QKeyValue kv)
    : base(tok)
    {
      this.lhs = lhs;
      this.rhs = rhs;
      this.kv = kv;
    }

    public QKeyValue Attributes
    {
      get { return kv; }
      set { kv = value; }
    }

    public override void Resolve(ResolutionContext rc)
    {
      lhs.Resolve(rc);
      rhs.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);

      LayerRange expectedLayerRange = null;
      if (tc.Proc is YieldProcedureDecl)
      {
        UnpackedLhs.Select(ie => ie.Decl).ForEach(v =>
        {
          if (v is GlobalVariable)
          {
            tc.Error(v, $"global variable directly modified in a yield procedure: {v.Name}");
          }
        });
        expectedLayerRange = LayerRange.Union(UnpackedLhs.Select(ie => ie.Decl.LayerRange).ToList());
      }

      lhs.Typecheck(tc);
      
      tc.GlobalAccessOnlyInOld = tc.Proc is YieldProcedureDecl;
      tc.ExpectedLayerRange = expectedLayerRange;
      rhs.Typecheck(tc);
      tc.GlobalAccessOnlyInOld = false;
      tc.ExpectedLayerRange = null;
      
      this.CheckAssignments(tc);
      Type ltype = lhs.Type;
      Type rtype = rhs.Type;
      if (ltype == null || rtype == null)
      {
        return;
      }
      if (!ltype.Unify(rtype))
      {
        tc.Error(tok, "mismatched types in assignment command (cannot assign {0} to {1})", rtype, ltype);
        return;
      }
      var f = (FunctionCall)lhs.Fun;
      if (!(f.Func is DatatypeConstructor))
      {
        tc.Error(tok, "left side of unpack command must be a constructor application");
      }
      var assignedVars = new HashSet<Variable>();
      UnpackedLhs.ForEach(ie =>
      {
        if (assignedVars.Contains(ie.Decl))
        {
          tc.Error(tok, $"variable {ie.Decl} is assigned more than once in unpack command");
        }
        else
        {
          assignedVars.Add(ie.Decl);
        }
      });
    }

    public DatatypeConstructor Constructor => (DatatypeConstructor)((FunctionCall)lhs.Fun).Func;

    public NAryExpr Lhs
    {
      get
      {
        return lhs;
      }
      set
      {
        lhs = value;
      }
    }

    public Expr Rhs
    {
      get
      {
        return rhs;
      }
      set
      {
        rhs = value;
      }
    }

    public IEnumerable<IdentifierExpr> UnpackedLhs => lhs.Args.Cast<IdentifierExpr>();

    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
      lhs.Args.Cast<IdentifierExpr>().ForEach(vars.Add);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "");
      lhs.Emit(stream);
      stream.Write(" := ");
      rhs.Emit(stream);
      stream.WriteLine(";");
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitUnpackCmd(this);
    }

    protected override Cmd ComputeDesugaring(PrintOptions options)
    {
      var cmds = new List<Cmd>();
      // assert that unpacked value has the correct constructor
      var assertCmd = new AssertCmd(tok,
        new NAryExpr(tok, new IsConstructor(tok, Constructor.datatypeTypeCtorDecl, Constructor.index),
          new List<Expr> { rhs })) { Description = new FailureOnlyDescription("the precondition for unpack could not be proved") };
      cmds.Add(assertCmd);
      // read fields into lhs variables from localRhs
      var assignLhss = lhs.Args.Select(arg => new SimpleAssignLhs(tok, (IdentifierExpr)arg)).ToList<AssignLhs>();
      var assignRhss = Enumerable.Range(0, Constructor.InParams.Count).Select(i =>
      {
        var fieldName = Constructor.InParams[i].Name;
        var fieldAccess = new FieldAccess(tok, fieldName, Constructor.datatypeTypeCtorDecl,
          new List<DatatypeAccessor> { new DatatypeAccessor(Constructor.index, i) });
        return new NAryExpr(tok, fieldAccess, new List<Expr> { rhs });
      }).ToList<Expr>();
      cmds.Add(new AssignCmd(tok, assignLhss, assignRhss));
      return new StateCmd(tok, new List<Variable>(), cmds);
    }
  }

  /// <summary>
  /// A StateCmd is like an imperative-let binding around a sequence of commands.
  /// There is no user syntax for a StateCmd.  Instead, a StateCmd is only used
  /// temporarily during the desugaring phase inside the VC generator.
  /// </summary>
  public class StateCmd : Cmd
  {
    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._locals != null);
      Contract.Invariant(this._cmds != null);
    }

    private List<Variable> _locals;

    public /*readonly, except for the StandardVisitor*/ List<Variable> /*!*/ Locals
    {
      get
      {
        Contract.Ensures(Contract.Result<List<Variable>>() != null);
        return this._locals;
      }
      internal set
      {
        Contract.Requires(value != null);
        this._locals = value;
      }
    }

    private List<Cmd> _cmds;

    public /*readonly, except for the StandardVisitor*/ List<Cmd> /*!*/ Cmds
    {
      get
      {
        Contract.Ensures(Contract.Result<List<Cmd>>() != null);
        return this._cmds;
      }
      set
      {
        Contract.Requires(value != null);
        this._cmds = value;
      }
    }

    public StateCmd(IToken tok, List<Variable> /*!*/ locals, List<Cmd> /*!*/ cmds)
      : base(tok)
    {
      Contract.Requires(locals != null);
      Contract.Requires(cmds != null);
      Contract.Requires(tok != null);
      this._locals = locals;
      this._cmds = cmds;
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      rc.PushVarContext();
      foreach (Variable /*!*/ v in Locals)
      {
        Contract.Assert(v != null);
        rc.AddVariable(v);
      }

      foreach (Cmd /*!*/ cmd in Cmds)
      {
        Contract.Assert(cmd != null);
        cmd.Resolve(rc);
      }

      rc.PopVarContext();
    }

    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
      var vs = new List<IdentifierExpr>();
      foreach (Cmd cmd in Cmds)
      {
        Contract.Assert(cmd != null);
        cmd.AddAssignedIdentifiers(vs);
      }

      var localsSet = new HashSet<Variable>(this.Locals);
      foreach (var v in vs)
      {
        Debug.Assert(v.Decl != null);
        if (!localsSet.Contains(v.Decl))
        {
          vars.Add(v);
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (Cmd /*!*/ cmd in Cmds)
      {
        Contract.Assert(cmd != null);
        cmd.Typecheck(tc);
      }
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.WriteLine(this, level, "{");
      foreach (Variable /*!*/ v in Locals)
      {
        Contract.Assert(v != null);
        v.Emit(stream, level + 1);
      }

      foreach (Cmd /*!*/ c in Cmds)
      {
        Contract.Assert(c != null);
        c.Emit(stream, level + 1);
      }

      stream.WriteLine(level, "}");
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitStateCmd(this);
    }
  }

  [ContractClass(typeof(SugaredCmdContracts))]
  public abstract class SugaredCmd : Cmd
  {
    private Cmd desugaring; // null until desugared

    public SugaredCmd(IToken tok)
      : base(tok)
    {
      Contract.Requires(tok != null);
    }

    public Cmd GetDesugaring(PrintOptions options)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);

      if (desugaring == null) {
        desugaring = ComputeDesugaring(options);
      }

      return desugaring;
    }

    public void ResetDesugaring()
    {
      desugaring = null;
    }
    
    /// <summary>
    /// This method invokes "visitor.Visit" on the desugaring, and then updates the
    /// desugaring to the result thereof.  The method's intended use is for subclasses
    /// of StandardVisitor that need to also visit the desugaring.  Note, since the
    /// "desugaring" field is updated, this is not an appropriate method to be called
    /// by a ReadOnlyVisitor; such visitors should instead just call
    /// visitor.Visit(sugaredCmd.Desugaring).
    /// </summary>
    public void VisitDesugaring(StandardVisitor visitor)
    {
      Contract.Requires(visitor != null && !(visitor is ReadOnlyVisitor));
      if (desugaring != null)
      {
        desugaring = (Cmd) visitor.Visit(desugaring);
      }
    }

    protected abstract Cmd /*!*/ ComputeDesugaring(PrintOptions options);

    public void ExtendDesugaring(CoreOptions options, IEnumerable<Cmd> before, IEnumerable<Cmd> beforePreconditionCheck,
      IEnumerable<Cmd> after)
    {
      var desug = GetDesugaring(options);
      var stCmd = desug as StateCmd;
      if (stCmd != null)
      {
        stCmd.Cmds.InsertRange(0, before);
        var idx = stCmd.Cmds.FindIndex(c => c is AssertCmd || c is HavocCmd || c is AssumeCmd);
        if (idx < 0)
        {
          idx = 0;
        }

        stCmd.Cmds.InsertRange(idx, beforePreconditionCheck);
        stCmd.Cmds.AddRange(after);
      }
      else if (desug != null)
      {
        var cmds = new List<Cmd>(before);
        cmds.Add(desug);
        cmds.AddRange(after);
        desugaring = new StateCmd(Token.NoToken, new List<Variable>(), cmds);
      }
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      if (stream.Options.PrintDesugarings && !stream.UseForComputingChecksums)
      {
        stream.WriteLine(this, level, "/*** desugaring:");
        GetDesugaring(stream.Options).Emit(stream, level);
        stream.WriteLine(level, "**** end desugaring */");
      }
    }
  }

  [ContractClassFor(typeof(SugaredCmd))]
  public abstract class SugaredCmdContracts : SugaredCmd
  {
    public SugaredCmdContracts() : base(null)
    {
    }

    protected override Cmd ComputeDesugaring(PrintOptions options)
    {
      Contract.Ensures(Contract.Result<Cmd>() != null);

      throw new NotImplementedException();
    }
  }

  public abstract class CallCommonality : SugaredCmd, ICarriesAttributes
  {
    public QKeyValue Attributes { get; set; }

    private bool isFree = false;

    public bool IsFree
    {
      get { return isFree; }
      set { isFree = value; }
    }

    private bool isAsync = false;

    public bool IsAsync
    {
      get { return isAsync; }
      set { isAsync = value; }
    }

    protected CallCommonality(IToken tok, QKeyValue kv)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Attributes = kv;
    }

    protected enum TempVarKind
    {
      Formal,
      Old,
      Bound
    }

    // We have to give the type explicitly, because the type of the formal "likeThisOne" can contain type variables
    protected Variable CreateTemporaryVariable(List<Variable> tempVars, Variable likeThisOne, Type ty, TempVarKind kind,
      ref int uniqueId)
    {
      Contract.Requires(ty != null);
      Contract.Requires(likeThisOne != null);
      Contract.Requires(tempVars != null);
      Contract.Ensures(Contract.Result<Variable>() != null);
      string /*!*/
        tempNamePrefix;
      switch (kind)
      {
        case TempVarKind.Formal:
          tempNamePrefix = "formal@";
          break;
        case TempVarKind.Old:
          tempNamePrefix = "old@";
          break;
        case TempVarKind.Bound:
          tempNamePrefix = "forall@";
          break;
        default:
        {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        } // unexpected kind
      }

      TypedIdent ti = likeThisOne.TypedIdent;
      int id = uniqueId++;
      TypedIdent newTi = new TypedIdent(ti.tok, "call" + id + tempNamePrefix + ti.Name, ty);
      Variable v;
      if (kind == TempVarKind.Bound)
      {
        v = new BoundVariable(likeThisOne.tok, newTi);
      }
      else
      {
        v = new LocalVariable(likeThisOne.tok, newTi);
        tempVars.Add(v);
      }
      return v;
    }
  }

  public class ParCallCmd : CallCommonality
  {
    public List<CallCmd> CallCmds;

    public ParCallCmd(IToken tok, List<CallCmd> callCmds)
      : base(tok, null)
    {
      this.CallCmds = callCmds;
    }

    public ParCallCmd(IToken tok, List<CallCmd> callCmds, QKeyValue kv)
      : base(tok, kv)
    {
      this.CallCmds = callCmds;
    }

    protected override Cmd ComputeDesugaring(PrintOptions options)
    {
      throw new NotImplementedException();
    }

    public ProofObligationDescription Description { get; set; } = new PreconditionDescription();

    public override void Resolve(ResolutionContext rc)
    {
      (this as ICarriesAttributes).ResolveAttributes(rc);
      foreach (CallCmd callCmd in CallCmds)
      {
        callCmd.Resolve(rc);
      }

      HashSet<Variable> parallelCallLhss = new HashSet<Variable>();
      Dictionary<Variable, List<CallCmd>> inputVariables = new Dictionary<Variable, List<CallCmd>>();
      CallCmds.ForEach(c =>
      {
        foreach (var v in VariableCollector.Collect(c.Ins))
        {
          if (!inputVariables.ContainsKey(v))
          {
            inputVariables[v] = new List<CallCmd>();
          }

          inputVariables[v].Add(c);
        }
      });
      foreach (CallCmd callCmd in CallCmds)
      {
        foreach (IdentifierExpr ie in callCmd.Outs)
        {
          if (parallelCallLhss.Contains(ie.Decl))
          {
            rc.Error(this, "left-hand side of parallel call command contains variable twice: {0}", ie.Name);
          }
          else if (inputVariables.ContainsKey(ie.Decl) &&
                   (inputVariables[ie.Decl].Count > 1 || inputVariables[ie.Decl][0] != callCmd))
          {
            rc.Error(this,
              "left-hand side of parallel call command contains variable accessed on the right-hand side of a different arm: {0}",
              ie.Name);
          }
          else
          {
            parallelCallLhss.Add(ie.Decl);
          }
        }
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);
      if (tc.CheckModifies)
      {
        if (!tc.Yields)
        {
          tc.Error(this, "calling procedure of a parallel call must yield");
        }

        foreach (CallCmd callCmd in CallCmds)
        {
          if (callCmd.Proc is YieldProcedureDecl || callCmd.Proc is YieldInvariantDecl)
          {
            continue;
          }
          tc.Error(callCmd, "target procedure of a parallel call must yield");
        }
      }
      foreach (CallCmd callCmd in CallCmds)
      {
        callCmd.Typecheck(tc);
      }

      var markedCallCount = CallCmds.Count(CivlAttributes.IsCallMarked);
      if (markedCallCount > 0)
      {
        if (markedCallCount > 1)
        {
          tc.Error(this, "at most one arm of a parallel call may be annotated with :mark");
        }
        var callerDecl = (YieldProcedureDecl)tc.Proc;
        CallCmds.ForEach(callCmd =>
        {
          if (!CivlAttributes.IsCallMarked(callCmd) && callCmd.Proc is YieldProcedureDecl calleeDecl &&
              callerDecl.Layer == calleeDecl.Layer)
          {
            callCmd.Outs.Where(ie => callerDecl.VisibleFormals.Contains(ie.Decl)).ForEach(ie =>
              {
                tc.Error(ie, $"unmarked call modifies visible output variable of the caller: {ie.Decl}");
              });
          }
        });
      }
    }

    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
      foreach (CallCmd callCmd in CallCmds)
      {
        callCmd.AddAssignedIdentifiers(vars);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitParCallCmd(this);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "");
      stream.Write("par ");
      EmitAttributes(stream, Attributes);
      string sep = "";
      bool first = true;
      foreach (var callCmd in CallCmds)
      {
        if (!first)
        {
          stream.Write(" | ");
        }

        first = false;
        if (callCmd.Outs.Count > 0)
        {
          foreach (Expr arg in callCmd.Outs)
          {
            stream.Write(sep);
            sep = ", ";
            if (arg == null)
            {
              stream.Write("*");
            }
            else
            {
              arg.Emit(stream);
            }
          }

          stream.Write(" := ");
        }

        stream.Write(TokenTextWriter.SanitizeIdentifier(callCmd.callee));
        stream.Write("(");
        sep = "";
        foreach (Expr arg in callCmd.Ins)
        {
          stream.Write(sep);
          sep = ", ";
          if (arg == null)
          {
            stream.Write("*");
          }
          else
          {
            arg.Emit(stream);
          }
        }

        stream.Write(")");
      }

      stream.WriteLine(";");
      base.Emit(stream, level);
    }
  }

  public abstract class PredicateCmd : Cmd, ICarriesAttributes
  {
    public QKeyValue Attributes { get; set; }

    public /*readonly--except in StandardVisitor*/ Expr /*!*/
      Expr;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Expr != null);
    }

    
    public PredicateCmd(IToken /*!*/ tok, Expr /*!*/ expr)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
    }

    public PredicateCmd(IToken /*!*/ tok, Expr /*!*/ expr, QKeyValue kv)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
      Attributes = kv;
    }

    public override void Resolve(ResolutionContext rc)
    {
      Expr.Resolve(rc);
      (this as ICarriesAttributes).ResolveAttributes(rc);
      Layers = (this as ICarriesAttributes).FindLayers();
      if (rc.Proc is YieldProcedureDecl yieldProcedureDecl && this is AssertCmd && !this.HasAttribute(CivlAttributes.YIELDS))
      {
        if (Layers.Count == 0)
        {
          rc.Error(this, "expected layers");
        }
        else if (Layers[^1] > yieldProcedureDecl.Layer)
        {
          rc.Error(this, $"each layer must not be more than {yieldProcedureDecl.Layer}");
        }
      }
      var id = QKeyValue.FindStringAttribute(Attributes, "id");
      if (id != null)
      {
        rc.AddStatementId(tok, id);
      }
    }

    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
    }
  }

  public abstract class MiningStrategy
  {
    // abstract class to bind all types of enhanced error data types together
  }

  public class ListOfMiningStrategies : MiningStrategy
  {
    private List<MiningStrategy> /*!*/
      _msList;

    public List<MiningStrategy> /*!*/ msList
    {
      get
      {
        Contract.Ensures(Contract.Result<List<MiningStrategy>>() != null);
        return this._msList;
      }
      set
      {
        Contract.Requires(value != null);
        this._msList = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._msList != null);
    }

    public ListOfMiningStrategies(List<MiningStrategy> l)
    {
      Contract.Requires(l != null);
      this._msList = l;
    }
  }

  public class EEDTemplate : MiningStrategy
  {
    private string /*!*/
      _reason;

    public string /*!*/ reason
    {
      get
      {
        Contract.Ensures(Contract.Result<string>() != null);
        return this._reason;
      }
      set
      {
        Contract.Requires(value != null);
        this._reason = value;
      }
    }

    private List<Expr /*!*/> /*!*/
      exprList;

    public IEnumerable<Expr> Expressions
    {
      get
      {
        Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expr>>()));
        return this.exprList.AsReadOnly();
      }
      set
      {
        Contract.Requires(cce.NonNullElements(value));
        this.exprList = new List<Expr>(value);
      }
    }


    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._reason != null);
      Contract.Invariant(cce.NonNullElements(this.exprList));
    }

    public EEDTemplate(string reason, List<Expr /*!*/> /*!*/ exprList)
    {
      Contract.Requires(reason != null);
      Contract.Requires(cce.NonNullElements(exprList));
      this._reason = reason;
      this.exprList = exprList;
    }
  }

  public class AssertCmd : PredicateCmd
  {
    public Expr OrigExpr;
    public Dictionary<Variable, Expr> IncarnationMap;

    Expr verifiedUnder;

    public Expr VerifiedUnder
    {
      get
      {
        if (verifiedUnder != null)
        {
          return verifiedUnder;
        }
        verifiedUnder = QKeyValue.FindExprAttribute(Attributes, "verified_under");
        return verifiedUnder;
      }
    }

    public void MarkAsVerifiedUnder(Expr expr)
    {
      Attributes = new QKeyValue(tok, "verified_under", new List<object> {expr}, Attributes);
      verifiedUnder = expr;
    }

    public ProofObligationDescription Description { get; set; }

    public string ErrorMessage
    {
      get { return QKeyValue.FindStringAttribute(Attributes, "msg"); }
    }

    private MiningStrategy errorDataEnhanced;

    public MiningStrategy ErrorDataEnhanced
    {
      get { return errorDataEnhanced; }
      set { errorDataEnhanced = value; }
    }

    public AssertCmd(IToken tok, Expr expr, ProofObligationDescription description, QKeyValue kv = null)
      : base(tok, expr, kv)
    {
      errorDataEnhanced = GenerateBoundVarMiningStrategy(expr);
      Description = description;
    }

    public AssertCmd(IToken tok, Expr expr, QKeyValue kv = null)
      : this(tok, expr, new AssertionDescription(), kv) { }

    public override void Emit(TokenTextWriter stream, int level)
    {
      stream.Write(this, level, "assert ");
      EmitAttributes(stream, Attributes);
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);
      tc.ExpectedLayerRange = Layers?.Count > 0 ? new LayerRange(Layers[0], Layers[^1]) : null;
      Expr.Typecheck(tc);
      tc.ExpectedLayerRange = null;
      Contract.Assert(Expr.Type != null); // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool))
      {
        tc.Error(this, "an asserted expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public static MiningStrategy GenerateBoundVarMiningStrategy(Expr expr)
    {
      Contract.Requires(expr != null);
      List<MiningStrategy> l = new List<MiningStrategy>();
      if (expr != null)
      {
        l = GenerateBoundVarListForMining(expr, l);
      }

      return new ListOfMiningStrategies(l);
    }

    public static List<MiningStrategy> GenerateBoundVarListForMining(Expr expr, List<MiningStrategy> l)
    {
      Contract.Requires(l != null);
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<List<MiningStrategy>>() != null);

      // go through the origExpr and identify all bound variables in the AST.
      if (expr is LiteralExpr || expr is IdentifierExpr)
      {
        //end recursion
      }
      else if (expr is NAryExpr)
      {
        NAryExpr e = (NAryExpr) expr;
        foreach (Expr arg in e.Args)
        {
          Contract.Assert(arg != null);
          l = GenerateBoundVarListForMining(arg, l);
        }
      }
      else if (expr is OldExpr)
      {
        OldExpr e = (OldExpr) expr;
        l = GenerateBoundVarListForMining(e.Expr, l);
      }
      else if (expr is QuantifierExpr)
      {
        QuantifierExpr qe = (QuantifierExpr) expr;
        List<Variable> vs = qe.Dummies;
        foreach (Variable /*!*/ x in vs)
        {
          Contract.Assert(x != null);
          string name = x.Name;
          if (name.StartsWith("^"))
          {
            name = name.Substring(1);
            List<Expr> exprList = new List<Expr>();
            exprList.Add(new IdentifierExpr(Token.NoToken, x.ToString(), x.TypedIdent.Type));
            MiningStrategy eed = new EEDTemplate("The bound variable " + name + " has the value {0}.", exprList);
            l.Add(eed);
          }
        }

        l = GenerateBoundVarListForMining(qe.Body, l);
      }

      return l;
    }


    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitAssertCmd(this);
    }
  }

  // An AssertCmd that is a loop invariant check before the loop iteration starts
  public class LoopInitAssertCmd : AssertCmd
  {
    public readonly AssertCmd originalAssert;

    public LoopInitAssertCmd(IToken /*!*/ tok, Expr /*!*/ expr, AssertCmd original)
      : base(tok, expr, new InvariantEstablishedDescription())
    {
      this.originalAssert = original;
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
  }

  // An AssertCmd that is a loop invariant check to maintain the invariant after iteration
  public class LoopInvMaintainedAssertCmd : AssertCmd
  {
    public readonly AssertCmd originalAssert;

    public LoopInvMaintainedAssertCmd(IToken /*!*/ tok, Expr /*!*/ expr, AssertCmd original)
      : base(tok, expr, new InvariantMaintainedDescription())
    {
      this.originalAssert = original;
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }
  }

  /// <summary>
  /// An AssertCmd that is introduced in translation from the requires on a call.
  /// </summary>
  public class AssertRequiresCmd : AssertCmd
  {
    public CallCmd /*!*/ Call;

    public Requires /*!*/ Requires;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Call != null);
      Contract.Invariant(Requires != null);
    }


    public AssertRequiresCmd(CallCmd /*!*/ call, Requires /*!*/ requires)
      : base(call.tok, requires.Condition, requires.Description)
    {
      Contract.Requires(call != null);
      Contract.Requires(requires != null);
      this.Call = call;
      this.Requires = requires;
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssertRequiresCmd(this);
    }
  }

  /// <summary>
  /// An AssertCmd that is introduced in translation from an ensures
  /// declaration.
  /// </summary>
  public class AssertEnsuresCmd : AssertCmd
  {
    public Ensures /*!*/
      Ensures;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Ensures != null);
    }

    public AssertEnsuresCmd(Ensures /*!*/ ens)
      : base(ens.tok, ens.Condition, ens.Description)
    {
      Contract.Requires(ens != null);
      this.Ensures = ens;
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitAssertEnsuresCmd(this);
    }
  }

  public class AssumeCmd : PredicateCmd
  {
    public AssumeCmd(IToken /*!*/ tok, Expr /*!*/ expr)
      : base(tok, expr)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }

    public AssumeCmd(IToken /*!*/ tok, Expr /*!*/ expr, QKeyValue kv)
      : base(tok, expr, kv)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "assume ");
      EmitAttributes(stream, Attributes);
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc)
    {
      (this as ICarriesAttributes).ResolveAttributes(rc);
      base.Resolve(rc);
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      (this as ICarriesAttributes).TypecheckAttributes(tc);
      tc.ExpectedLayerRange = tc.Proc is YieldProcedureDecl decl ? new LayerRange(0, decl.Layer) : null;
      tc.GlobalAccessOnlyInOld = tc.Proc is YieldProcedureDecl;
      Expr.Typecheck(tc);
      tc.ExpectedLayerRange = null;
      tc.GlobalAccessOnlyInOld = false;
      Contract.Assert(Expr.Type != null); // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool))
      {
        tc.Error(this, "an assumed expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      return visitor.VisitAssumeCmd(this);
    }
  }

  public class ReturnExprCmd : ReturnCmd
  {
    public Expr /*!*/ Expr;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Expr != null);
    }

    public ReturnExprCmd(IToken /*!*/ tok, Expr /*!*/ expr)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Expr = expr;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "return ");
      this.Expr.Emit(stream);
      stream.WriteLine(";");
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      Expr.Typecheck(tc);
      Contract.Assert(Expr.Type != null); // follows from Expr.Typecheck postcondition
      if (!Expr.Type.Unify(Type.Bool))
      {
        tc.Error(this, "a return expression must be of type bool (got: {0})", Expr.Type);
      }
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      Expr.Resolve(rc);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitReturnExprCmd(this);
    }
  }

  public class HavocCmd : Cmd
  {
    private List<IdentifierExpr> /*!*/ _vars;

    public List<IdentifierExpr> /*!*/ Vars
    {
      get
      {
        Contract.Ensures(Contract.Result<List<IdentifierExpr>>() != null);
        return this._vars;
      }
      set
      {
        Contract.Requires(value != null);
        this._vars = value;
      }
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(this._vars != null);
    }

    public HavocCmd(IToken /*!*/ tok, List<IdentifierExpr> /*!*/ vars)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(vars != null);
      this._vars = vars;
    }

    public override void Emit(TokenTextWriter stream, int level)
    {
      //Contract.Requires(stream != null);
      stream.Write(this, level, "havoc ");
      Vars.Emit(stream, true);
      stream.WriteLine(";");
    }

    public override void Resolve(ResolutionContext rc)
    {
      //Contract.Requires(rc != null);
      foreach (IdentifierExpr /*!*/ ide in Vars)
      {
        Contract.Assert(ide != null);
        ide.Resolve(rc);
      }
    }

    public override void AddAssignedIdentifiers(List<IdentifierExpr> vars) {
      foreach (IdentifierExpr /*!*/ e in this.Vars)
      {
        Contract.Assert(e != null);
        vars.Add(e);
      }
    }

    public override void Typecheck(TypecheckingContext tc)
    {
      //Contract.Requires(tc != null);
      foreach (IdentifierExpr ie in Vars)
      {
        ie.Typecheck(tc);
      }

      this.CheckAssignments(tc);
    }

    public override Absy StdDispatch(StandardVisitor visitor)
    {
      //Contract.Requires(visitor != null);
      Contract.Ensures(Contract.Result<Absy>() != null);
      return visitor.VisitHavocCmd(this);
    }
  }
}
