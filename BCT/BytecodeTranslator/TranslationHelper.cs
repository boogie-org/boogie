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

    public MethodParameter(IParameterDefinition parameterDefinition, Bpl.Type ptype) {
      this.underlyingParameter = parameterDefinition;

      var parameterToken = parameterDefinition.Token();
      var typeToken = parameterDefinition.Type.Token();
      var parameterName = parameterDefinition.Name.Value;

      this.inParameterCopy = new Bpl.Formal(parameterToken, new Bpl.TypedIdent(typeToken, parameterName + "$in", ptype), true);
      if (parameterDefinition.IsByReference) {
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
      var s = MemberHelper.GetMethodSignature(method, NameFormattingOptions.DocumentationId);
      s = s.Substring(2);
      s = s.TrimEnd(')');
      s = TurnStringIntoValidIdentifier(s);
      return s;
    }

    public static string TurnStringIntoValidIdentifier(string s) {
      s = s.Replace("[0:,0:]", "2DArray"); // TODO: Do this programmatically to handle arbitrary arity
      s = s.Replace("[0:,0:,0:]", "3DArray");
      s = s.Replace("[0:,0:,0:,0:]", "4DArray");
      s = s.Replace("[0:,0:,0:,0:,0:]", "5DArray");
      s = s.Replace('!', '$');
      s = s.Replace('*', '$');
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
      s = s.Replace(';', '$');
      s = s.Replace('%', '$');
      s = s.Replace('&', '$');
      return s;
    }

    public static bool IsStruct(ITypeReference typ) {
      return typ.IsValueType && !typ.IsEnum && typ.TypeCode == PrimitiveTypeCode.NotPrimitive;
    }

    #region Temp Stuff that must be replaced as soon as there is real code to deal with this

    public static Bpl.Variable TempThisVar() {
      return new Bpl.GlobalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "this", Bpl.Type.Int));
    }

    #endregion

  }
}
