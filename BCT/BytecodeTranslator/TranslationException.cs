//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace BytecodeTranslator {
  public enum ExceptionType {
    UnresolvedMethod,
    UnresolvedType,
  };

  public class TranslationException : Exception {
    
    public TranslationException(string reason) : base(reason) {
    }

    public TranslationException(ExceptionType eType, string message)
      : base(eType.ToString() + ": " + message) {
    }

  }
}
