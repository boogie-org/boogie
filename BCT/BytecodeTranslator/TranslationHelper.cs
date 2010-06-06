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
    /// <summary>
    /// Class containing several static helper functions to convert
    /// from Cci to Boogie Methodology
    /// </summary>
  class TranslationHelper {

    public static Bpl.IToken CciLocationToBoogieToken(IEnumerable<ILocation> locations) {
      Bpl.IToken tok = Bpl.Token.NoToken;
      return tok;
    }

    public static Bpl.IToken CciLocationToBoogieToken(ILocation location) {
      Bpl.IToken tok = Bpl.Token.NoToken;
      return tok;
    }

    private static int tmpVarCounter = 0;
    public static string GenerateTempVarName() {
      return "$tmp" + (tmpVarCounter++).ToString();
    }

    public static string CreateUniqueMethodName(IMethodDefinition method) {
      return method.ContainingType.ToString() + "." + method.Name.Value + "$" + method.Type.ResolvedType.ToString();
    }

    #region Temp Stuff that must be replaced as soon as there is real code to deal with this

    public static Bpl.Type CciTypeToBoogie(ITypeReference type) {
      return Bpl.Type.Int;
    }

    public static Bpl.Variable TempHeapVar() {
      return new Bpl.GlobalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "$Heap", Bpl.Type.Int)); 
    }

    public static Bpl.Variable TempThisVar() {
      return new Bpl.GlobalVariable(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, "this", Bpl.Type.Int));
    }

    #endregion

  }
}
