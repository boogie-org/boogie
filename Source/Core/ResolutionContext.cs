//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Boogie {
  using System.Collections;
  using System.Collections.Generic;
  using System;
  using System.Linq;
  using System.Diagnostics.Contracts;

  [ContractClass(typeof(IErrorSinkContracts))]
  public interface IErrorSink {
    void Error(IToken/*!*/ tok, string/*!*/ msg);
  }
  [ContractClassFor(typeof(IErrorSink))]
  public abstract class IErrorSinkContracts : IErrorSink {
    #region IErrorSink Members
    public void Error(IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      throw new NotImplementedException();
    }
    #endregion
  }

  public class CheckingContext {
    // ------------------------------  Error counting  ------------------------------

    IErrorSink errorSink;
    int errors;

    public CheckingContext(IErrorSink errorSink) {
      this.errorSink = errorSink;
      this.errors = 0;
    }

    public int ErrorCount {
      get {
        return errors;
      }
      set {
        errors = value;
      }
    }

    public void Error(Absy subject, string msg, params object[] args) {
      Contract.Requires(args != null);
      Contract.Requires(msg != null);
      Contract.Requires(subject != null);
      Error(subject.tok, msg, args);
    }

    public virtual void Error(IToken tok, string msg) {
      Contract.Requires(msg != null);
      Contract.Requires(tok != null);
      errors++;
      if (errorSink == null) {
        ConsoleColor col = Console.ForegroundColor;
        Console.ForegroundColor = ConsoleColor.Red;
        Console.WriteLine("{0}({1},{2}): Error: {3}",
            tok.filename, tok.line, tok.col - 1,
            msg);
        Console.ForegroundColor = col;
      } else {
        errorSink.Error(tok, msg);
      }
    }

    private string Format(string msg, params object[] args) {
      Contract.Requires(msg != null);
      Contract.Ensures(Contract.Result<string>() != null);
      if (System.Type.GetType("Mono.Runtime") != null) {  // MONO
        // something in mono seems to be broken so that calling
        // NamedDeclarations.ToString (and similar ToString methods)
        // causes a stack overflow. We therefore convert those to
        // strings by hand
        object[] fixedArgs = new object[cce.NonNull(args).Length];
        for (int i = 0; i < args.Length; ++i) {
          if (args[i] is NamedDeclaration) {
            fixedArgs[i] = cce.NonNull((NamedDeclaration)args[i]).Name;
          } else if (args[i] is Type) {
            System.IO.StringWriter buffer = new System.IO.StringWriter();
            using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, /*setTokens=*/ false, /*pretty=*/ false)) {
              cce.NonNull((Type)args[i]).Emit(stream);
            }
            fixedArgs[i] = buffer.ToString();
          } else if (args[i] is Expr) {
            System.IO.StringWriter buffer = new System.IO.StringWriter();
            using (TokenTextWriter stream = new TokenTextWriter("<buffer>", buffer, /*setTokens=*/ false, /*pretty=*/ false)) {
              cce.NonNull((Expr/*!*/)args[i]).Emit(stream, 0, false);
            }
            fixedArgs[i] = buffer.ToString();
          } else {
            fixedArgs[i] = args[i];
          }
        }
        args = fixedArgs;
      }
      return string.Format(msg, args);
    }

    public void Error(IToken tok, string msg, params object[] args) {
      Contract.Requires(msg != null);
      Contract.Requires(tok != null);
      Error(tok, Format(msg, args));
    }

    public void Warning(Absy subject, string msg, params object[] args) {
      Contract.Requires(args != null);
      Contract.Requires(msg != null);
      Contract.Requires(subject != null);
      Warning(subject.tok, msg, args);
    }

    public virtual void Warning(IToken tok, string msg) {
      Contract.Requires(msg != null);
      Contract.Requires(tok != null);
      // warnings are currently always written to the console
      ConsoleColor col = Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.DarkYellow;
      Console.WriteLine("{0}({1},{2}): Warning: {3}",
                        tok.filename, tok.line, tok.col - 1,
                        msg);
      Console.ForegroundColor = col;
    }

    public void Warning(IToken tok, string msg, params object[] args) {
      Contract.Requires(msg != null);
      Contract.Requires(tok != null);
      Warning(tok, Format(msg, args));
    }
  }

  public class ResolutionContext : CheckingContext {
    public ResolutionContext(IErrorSink errorSink)
      : base(errorSink) {
    }

    // ------------------------------  Boogie 2 Types  -------------------------

    // user-defined types, which can be either TypeCtorDecl or TypeSynonymDecl
    Hashtable /*string->NamedDeclaration*//*!*/ types = new Hashtable /*string->NamedDeclaration*/ ();
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(types != null);
      Contract.Invariant(cce.NonNullElements(typeBinders));
      Contract.Invariant(varContext != null);
      Contract.Invariant(funcdures != null);
    }


    /// <summary>
    /// Checks if name coincides with the name of a bitvector type.  If so, reports an error and
    /// returns true; otherwise, returns false.
    /// </summary>
    private bool CheckBvNameClashes(Absy absy, string name) {
      Contract.Requires(name != null);
      Contract.Requires(absy != null);
      if (name.StartsWith("bv") && name.Length > 2) {
        for (int i = 2; i < name.Length; ++i)
          if (!char.IsDigit(name[i]))
            return false;
        Error(absy, "type name: {0} is registered for bitvectors", name);
        return true;
      }
      return false;
    }

    public void AddType(NamedDeclaration td) {
      Contract.Requires(td != null);
      Contract.Requires((td is TypeCtorDecl) || (td is TypeSynonymDecl));
      Contract.Requires(td.Name != null);

      string name = td.Name;
      if (CheckBvNameClashes(td, name))
        return;  // error has already been reported

      var previous = (NamedDeclaration)types[name];
      if (previous == null) {
        types.Add(name, td);
      } else {
        var r = (NamedDeclaration)SelectNonExtern(td, previous);
        if (r == null) {
          Error(td, "more than one declaration of type name: {0}", name);
        } else {
          types[name] = r;
        }
      }
    }

    /// <summary>
    /// Returns the declaration of the named type, or null if
    /// no such type is declared. Also return null if the type
    /// declared with the given name is not a constructor but a
    /// type synonym
    /// </summary>
    /// <param name="name"></param>
    /// <returns></returns>
    public TypeCtorDecl LookUpType(string name) {
      Contract.Requires(name != null);
      return types[name] as TypeCtorDecl;
    }

    public TypeSynonymDecl LookUpTypeSynonym(string name) {
      Contract.Requires(name != null);
      return types[name] as TypeSynonymDecl;
    }

    // ------------------------------  Boogie 2 Type Binders  ------------------------------

    List<TypeVariable/*!*/>/*!*/ typeBinders = new List<TypeVariable/*!*/>(5);

    public void AddTypeBinder(TypeVariable td) {
      Contract.Requires(td != null);
      if (CheckBvNameClashes(td, td.Name)) {
        return;
      }
      if (types.ContainsKey(td.Name)) {
        Error(td, "name is already reserved for type constructor: {0}", td.Name);
        return;
      }
      for (int i = 0; i < typeBinders.Count; i++) {
        if (typeBinders[i].Name == td.Name) {
          Error(td, "more than one declaration of type variable: {0}", td.Name);
          return;
        }
      }
      typeBinders.Add(td);
    }

    public int TypeBinderState {
      get {
        return typeBinders.Count;
      }
      set {
        typeBinders.RemoveRange(value, typeBinders.Count - value);
      }
    }

    /// <summary>
    /// Returns the declaration of the named type binder, or null if
    /// no such binder is declared.
    /// </summary>
    public TypeVariable LookUpTypeBinder(string name) {
      Contract.Requires(name != null);
      for (int i = typeBinders.Count; 0 <= --i; ) {
        TypeVariable/*!*/ td = typeBinders[i];
        Contract.Assert(td != null);
        if (td.Name == name) {
          return td;
        }
      }
      return null;  // not present
    }

    // ------------------------------  Variables  ------------------------------

    class VarContextNode {
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(VarSymbols != null);
      }

      public readonly Hashtable /*string->Variable*//*!*/ VarSymbols = new Hashtable /*string->Variable*/();
      public /*maybe null*/ VarContextNode ParentContext;
      public readonly bool Opaque;
      readonly ISet<string> assignedAssumptionVariables = new HashSet<string>();

      public bool HasVariableBeenAssigned(string name)
      {
        Contract.Requires(name != null);

        if (assignedAssumptionVariables.Contains(name))
        {
          return true;
        }
        else if (ParentContext != null)
        {
          return ParentContext.HasVariableBeenAssigned(name);
        }
        else
        {
          return false;
        }
      }

      public bool MarkVariableAsAssigned(string name)
      {
        Contract.Requires(name != null);

        if (VarSymbols.Contains(name))
        {
          if (assignedAssumptionVariables.Contains(name))
          {
            return false;
          }
          assignedAssumptionVariables.Add(name);
          return true;
        }
        else if (ParentContext != null)
        {
          return ParentContext.MarkVariableAsAssigned(name);
        }
        else
        {
          return false;
        }
      }

      public VarContextNode(/*maybe null*/ VarContextNode parentContext, bool opaque) {
        ParentContext = parentContext;
        Opaque = opaque;
      }
    }

    // symbolic constants, global variables, local variables, formals, expression-bound variables
    VarContextNode/*!*/ varContext = new VarContextNode(null, false);

    /// <summary>
    /// Adds a variable context.
    /// </summary>
    public void PushVarContext() {
      varContext = new VarContextNode(varContext, false);
    }

    /// <summary>
    /// Adds an opaque variable context, that is, one that blocks all previously pushed contexts.
    /// </summary>
    public void PushOpaqueVarContext() {
      varContext = new VarContextNode(varContext, true);
    }

    /// <summary>
    /// Requires there to be more than one variable context.
    /// </summary>
    public void PopVarContext() {
      Contract.Assert(varContext.ParentContext != null);
      varContext = varContext.ParentContext;
    }

    public readonly ISet<string> StatementIds = new HashSet<string>();

    public void AddStatementId(IToken tok, string name)
    {
      if (StatementIds.Contains(name))
      {
        Error(tok, "more than one statement with same id: " + name);
        return;
      }
      StatementIds.Add(name);
    }

    public void AddVariable(Variable var, bool global) {
      Contract.Requires(var != null);
      var previous = FindVariable(cce.NonNull(var.Name), !global);
      if (previous == null) {
        varContext.VarSymbols.Add(var.Name, var);
      } else {
        var r = (Variable)SelectNonExtern(var, previous);
        if (r == null) {
          Error(var, "more than one declaration of variable name: {0}", var.Name);
        } else {
          varContext.VarSymbols[var.Name] = r;
        }
      }
    }

    /// <summary>
    /// Returns the declaration of the named variable, or null if
    /// no such variable is declared.
    /// </summary>
    /// <param name="name"></param>
    /// <returns></returns>
    public Variable LookUpVariable(string name) {
      Contract.Requires(name != null);
      return FindVariable(name, false);
    }

    Variable FindVariable(string name, bool ignoreTopLevelVars) {
      Contract.Requires(name != null);
      VarContextNode c = varContext;
      bool lookOnlyForConstants = false;
      do {
        if (ignoreTopLevelVars && c.ParentContext == null) {
          // this is the top level and we're asked to ignore the top level; hence, we're done
          break;
        }

        Variable var = (Variable)c.VarSymbols[name];
        if (var != null && (!lookOnlyForConstants || var is Constant)) {
          return var;
        }
        // not at this level

        if (c.Opaque) {
          // from here on, only constants can be looked up
          lookOnlyForConstants = true;
        }
        c = c.ParentContext;
      } while (c != null);

      // not present in the relevant levels
      return null;
    }

    public bool HasVariableBeenAssigned(string name)
    {
      Contract.Requires(name != null);

      return varContext.HasVariableBeenAssigned(name);
    }

    public void MarkVariableAsAssigned(string name)
    {
      Contract.Requires(name != null);

      var success = varContext.MarkVariableAsAssigned(name);
      Contract.Assume(success);
    }

    Hashtable axioms = new Hashtable();

    public void AddAxiom(Axiom axiom) {
      string axiomName = QKeyValue.FindStringAttribute(axiom.Attributes, "name");
      if (axiomName == null)
        return;
      var previous = (Axiom)axioms[axiomName];
      if (previous == null) {
        axioms.Add(axiomName, axiom);
      }
      else {
        var r = (Axiom)SelectNonExtern(axiom, previous);
        if (r == null) {
          Error(axiom, "more than one declaration of axiom name: {0}", axiomName);
        }
        else {
          axioms[axiomName] = r;
        }
      }
    }

    // ------------------------------  Functions/Procedures  ------------------------------

    // uninterpreted function symbols, procedures
    Hashtable /*string->DeclWithFormals*//*!*/ funcdures = new Hashtable /*string->DeclWithFormals*/ ();

    public void AddProcedure(DeclWithFormals proc) {
      Contract.Requires(proc != null);
      Contract.Requires(proc.Name != null);

      string name = proc.Name;
      var previous = (DeclWithFormals)funcdures[name];
      if (previous == null) {
        funcdures.Add(name, proc);
      } else {
        var r = (DeclWithFormals)SelectNonExtern(proc, previous);
        if (r == null) {
          Error(proc, "more than one declaration of function/procedure name: {0}", name);
        } else {
          funcdures[name] = r;
        }
      }
    }

    /// <summary>
    /// If both "a" and "b" have an ":extern" attribute, returns either one.
    /// If one of "a" and "b" has an ":extern" attribute, returns that one.
    /// If neither of "a" and "b" has an ":extern" attribute, returns null.
    /// If a non-value value is returned, this method also adds the ":ignore"
    /// attribute to the declaration NOT returned.
    /// </summary>
    Declaration SelectNonExtern(Declaration a, Declaration b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Declaration>() == null || Contract.Result<Declaration>() == a || Contract.Result<Declaration>() == b);

      Declaration ignore, keep;
      if (QKeyValue.FindBoolAttribute(a.Attributes, "extern")) {
        ignore = a;
        keep = b;
      } else if (QKeyValue.FindBoolAttribute(b.Attributes, "extern")) {
        ignore = b;
        keep = a;
      } else {
        return null;
      }
      // prepend :ignore attribute
      ignore.Attributes = new QKeyValue(ignore.tok, "ignore", new List<object/*!*/>(), ignore.Attributes);
      return keep;
    }

    /// <summary>
    /// Returns the declaration of the named function/procedure, or null if
    /// no such function or procedure is declared.
    /// </summary>
    /// <param name="name"></param>
    /// <returns></returns>
    public DeclWithFormals LookUpProcedure(string name) {
      Contract.Requires(name != null);
      return (DeclWithFormals)funcdures[name];
    }

    // ------------------------------  Blocks  ------------------------------

    class ProcedureContext {
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Blocks != null);
      }

      public readonly Hashtable/*!*/ /*string->Block!*/ Blocks;
      public readonly ProcedureContext Next;
      public ProcedureContext(ProcedureContext next) {
        Blocks = new Hashtable /*string->Block!*/ ();
        Next = next;
      }
    }
    /*maybe null*/
    ProcedureContext procedureContext;  // stack of procedure contexts
    public bool HasProcedureContext {
      get {
        return procedureContext != null;
      }
    }

    /// <summary>
    /// Pushes a new procedure context.
    /// </summary>
    public void PushProcedureContext() {
      Contract.Ensures(HasProcedureContext);
      procedureContext = new ProcedureContext(procedureContext);
    }

    /// <summary>
    /// Requires there to be a procedure context.  Pops it.
    /// </summary>
    public void PopProcedureContext() {
      Contract.Requires(HasProcedureContext);
      Contract.Assert(procedureContext != null);  // follows from precondition
      procedureContext = procedureContext.Next;
    }

    /// <summary>
    /// Requires there to be a procedure context.
    /// </summary>
    /// <param name="block"></param>
    public void AddBlock(Block block) {
      Contract.Requires(block != null);
      Contract.Requires(HasProcedureContext);
      Contract.Assert(procedureContext != null);  // follows from precondition
      Hashtable/*!*/ /*string->Block!*/ blocks = procedureContext.Blocks;
      Contract.Assert(blocks != null);
      if (blocks[block.Label] != null) {
        Error(block, "more than one declaration of block name: {0}", block.Label);
      } else {
        blocks.Add(block.Label, block);
      }
    }

    /// <summary>
    /// Requires there to be a procedure context.
    /// Returns the declaration of the named block, or null if
    /// no such block is declared.
    /// </summary>
    /// <param name="name"></param>
    /// <returns></returns>
    public Block LookUpBlock(string name) {
      Contract.Requires(name != null);
      Contract.Requires(HasProcedureContext);
      Contract.Assert(procedureContext != null);  // follows from precondition
      Hashtable/*!*/ /*string->Block!*/ blocks = procedureContext.Blocks;
      Contract.Assert(blocks != null);
      return (Block)blocks[name];
    }

    // ------------------------------  Flags  ------------------------------

    public enum State {
      StateLess,
      Single,
      Two
    }
    State stateMode = State.Single;

    /// <summary>
    /// To increase our confidence in that the caller knows what it's doing, we only allow
    /// the state mode to be changed in and out of the State.Single mode.
    /// </summary>
    public State StateMode {
      get {
        return stateMode;
      }
      set {
        Contract.Assert(value != stateMode);
        Contract.Assert(stateMode == State.Single || value == State.Single);
        cce.BeginExpose(this);
        {
          stateMode = value;
        }
        cce.EndExpose();
      }
    }

    bool triggerMode = false;

    /// <summary>
    /// Setting TriggerMode is allowed only if the setting has the effect of toggling the
    /// boolean.  That is, TriggerMode can be set to true only if it previously was false,
    /// and TriggerMode can be set to false only if it previously was true.
    /// </summary>
    public bool TriggerMode {
      get {
        return triggerMode;
      }
      set {
        Contract.Assert(triggerMode != value);
        cce.BeginExpose(this);
        {
          triggerMode = value;
        }
        cce.EndExpose();
      }
    }
  }

  public class TypecheckingContext : CheckingContext {
    public List<IdentifierExpr> Frame;  // used in checking the assignment targets of implementation bodies
    public bool Yields;

    public TypecheckingContext(IErrorSink errorSink)
      : base(errorSink) {
    }

    public bool InFrame(Variable v) {
      Contract.Requires(v != null);
      Contract.Requires(Frame != null);
      return Frame.Any(f => f.Decl == v);
    }
  }
}
