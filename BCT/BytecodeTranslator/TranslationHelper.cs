//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;


namespace BytecodeTranslator {

  public class MethodParameter {
    
    /// <summary>
    /// All parameters of the method get an associated in parameter
    /// in the Boogie procedure except for out parameters.
    /// </summary>
    public Bpl.Formal/*?*/ inParameterCopy;
    
    /// <summary>
    /// A local variable when the underlyingParameter is an in parameter
    /// and a formal (out) parameter when the underlyingParameter is
    /// a ref or out parameter.
    /// </summary>
    public Bpl.Variable outParameterCopy;

    public IParameterDefinition underlyingParameter;

    public MethodParameter(IParameterDefinition parameterDefinition) {

      this.underlyingParameter = parameterDefinition;

      Bpl.Type ptype = TranslationHelper.CciTypeToBoogie(parameterDefinition.Type);

      var parameterToken = parameterDefinition.Token();
      var typeToken = parameterDefinition.Type.Token();
      var parameterName = parameterDefinition.Name.Value;

      if (!parameterDefinition.IsOut) {
        this.inParameterCopy = new Bpl.Formal(parameterToken, new Bpl.TypedIdent(typeToken, parameterName + "$in", ptype), true);
      }
      if (parameterDefinition.IsByReference || parameterDefinition.IsOut) {
        this.outParameterCopy = new Bpl.Formal(parameterToken, new Bpl.TypedIdent(typeToken, parameterName + "$out", ptype), false);
      } else {
        this.outParameterCopy = new Bpl.LocalVariable(parameterToken, new Bpl.TypedIdent(typeToken, parameterName, ptype));
      }
      
    }

    public override string ToString() {
      return this.underlyingParameter.Name.Value;
    }
  }

    /// <summary>
    /// Class containing several static helper functions to convert
    /// from Cci to Boogie
    /// </summary>
  static class TranslationHelper {

    public static Bpl.AssignCmd BuildAssignCmd(Bpl.IdentifierExpr lhs, Bpl.Expr rhs)
    {
      List<Bpl.AssignLhs> lhss = new List<Bpl.AssignLhs>();
      lhss.Add(new Bpl.SimpleAssignLhs(lhs.tok, lhs));
      List<Bpl.Expr> rhss = new List<Bpl.Expr>();
      rhss.Add(rhs);
      return new Bpl.AssignCmd(lhs.tok, lhss, rhss);
    }

    public static Bpl.IToken Token(this IObjectWithLocations objectWithLocations) {
      //TODO: use objectWithLocations.Locations!
      Bpl.IToken tok = Bpl.Token.NoToken;
      return tok;
    }

    internal static int tmpVarCounter = 0;
    public static string GenerateTempVarName() {
      return "$tmp" + (tmpVarCounter++).ToString();
    }

    public static string CreateUniqueMethodName(IMethodReference method) {
      var containingTypeName = TypeHelper.GetTypeName(method.ContainingType, NameFormattingOptions.None);
      if (containingTypeName == "Poirot.Poirot")
      {
          string name = method.Name.Value;
          if (name == "BeginAtomic")
              return "corral_atomic_begin";
          else if (name == "EndAtomic")
              return "corral_atomic_end";
          else if (name == "CurrentThreadId")
              return "corral_getThreadID";
          else if (name == "Nondet")
              return "poirot_nondet";
      }
      var s = MemberHelper.GetMethodSignature(method, NameFormattingOptions.DocumentationId);
      s = s.Substring(2);
      s = s.TrimEnd(')');
      s = TurnStringIntoValidIdentifier(s);
      return s;
    }

    public static string TurnStringIntoValidIdentifier(string s) {
      s = s.Replace('(', '$');
      s = s.Replace(')', '$');
      s = s.Replace(',', '$');
      s = s.Replace("[]", "array");
      s = s.Replace('<', '$');
      s = s.Replace('>', '$');
      s = s.Replace(':', '$');
      s = s.Replace(' ', '$');
      s = s.Replace('{', '$');
      s = s.Replace('}', '$');
      s = s.Replace('-', '$');
      s = s.Replace(' ', '$');
      s = s.Replace('\t', '$');
      s = s.Replace('\n', '$');
      s = s.Replace('/', '$');
      s = s.Replace('\\', '$');
      s = s.Replace('=', '$');
      s = s.Replace('@', '$');
      return s;
    }

    #region Temp Stuff that must be replaced as soon as there is real code to deal with this

    public static Bpl.Type CciTypeToBoogie(ITypeReference type) {
      if (TypeHelper.TypesAreEquivalent(type, type.PlatformType.SystemBoolean))
        return Bpl.Type.Bool;
      else if (TypeHelper.IsPrimitiveInteger(type))
        return Bpl.Type.Int;
      else
        return Bpl.Type.Int; // BUG! This is where we need to return "ref" for a reference type
    }

    public static Bpl.Variable TempThisVar() {
      return new Bpl.GlobalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "this", Bpl.Type.Int));
    }

    public static Bpl.Variable TempArrayContentsVar()
    {
        return new Bpl.GlobalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "$ArrayContents", Bpl.Type.Int));
    }
    public static Bpl.Variable TempArrayLengthVar()
    {
        return new Bpl.GlobalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "$ArrayLength", Bpl.Type.Int));
    }
    #endregion

  }
}
