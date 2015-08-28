//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.AbstractInterpretationFramework {
  using System;
  using System.Diagnostics;
  using System.Diagnostics.Contracts;

  public class Logger {
    private string/*!*/ dbgmsgContext;
    private static int contextWidth = 0;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(dbgmsgContext != null);
      Contract.Invariant(dbgmsgIndent != null);
    }


    public bool Enabled = false;

    public Logger(string/*!*/ contextMsg) {
      Contract.Requires(contextMsg != null);
      this.dbgmsgContext = "[" + contextMsg + "] ";
      contextWidth = Math.Max(contextWidth, contextMsg.Length + 3);
      // base();
    }

    private static System.Text.StringBuilder/*!*/ dbgmsgIndent = new System.Text.StringBuilder();

    public void DbgMsgIndent() {
      dbgmsgIndent.Append(' ', 2);
    }
    public void DbgMsgUnindent() {
      if (dbgmsgIndent.Length >= 2)
        dbgmsgIndent.Remove(0, 2);
    }

    [ConditionalAttribute("DEBUG")]
    public void DbgMsg(string msg) {
      if (Enabled)
        Debug.WriteLine(dbgmsgContext.PadRight(contextWidth) + dbgmsgIndent + msg);
    }
    [ConditionalAttribute("DEBUG")]
    public void DbgMsgNoLine(string msg) {
      if (Enabled)
        Debug.Write(dbgmsgContext.PadRight(contextWidth) + dbgmsgIndent + msg);
    }
    [ConditionalAttribute("DEBUG")]
    public void DbgMsgPlain(string msg) {
      if (Enabled)
        Debug.Write(msg);
    }
  }
}
