//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Xml;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
namespace Microsoft.Boogie {

  public class XmlSink {
    string/*!*/ filename;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(filename != null);
    }

    [Rep]
    XmlWriter wr;
    public bool IsOpen {
      get {
        return wr != null;
      }
    }

    public XmlSink(string filename) {
      Contract.Requires(filename != null);
      this.filename = filename;
    }

    /// <summary>
    /// Returns null on success, in which case the caller should eventually invoke Close.
    /// Returns an error string on failure.
    /// </summary>
    public string Open() {
      //modifies this.*;
      Contract.Ensures(IsOpen);
      if (wr != null) {
        Close();
      }
      cce.BeginExpose(this);
      {
        XmlWriterSettings settings = new XmlWriterSettings();
        settings.Indent = true;
        wr = XmlWriter.Create(filename, settings);
        wr.WriteStartDocument();
        wr.WriteStartElement("boogie");
        wr.WriteAttributeString("version", CommandLineOptions.Clo.VersionNumber);
        wr.WriteAttributeString("commandLine", Environment.CommandLine);
      }
      cce.EndExpose();
      return null;  // success
    }

    public void Close() {
      //modifies this.*;
      if (wr != null) {
        cce.BeginExpose(this);
        {
          wr.WriteEndDocument();
          wr.Close();
          wr = null;
        }
        cce.EndExpose();
      }
    }

    const string DateTimeFormatString = "u";

    public void WriteStartMethod(string methodName, DateTime startTime) {
      Contract.Requires(methodName != null);
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("method");
        wr.WriteAttributeString("name", methodName);
        wr.WriteAttributeString("startTime", startTime.ToString(DateTimeFormatString));
      }
      cce.EndExpose();
    }

    public void WriteEndMethod(string outcome, DateTime endTime, TimeSpan elapsed) {
      Contract.Requires(outcome != null);
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("conclusion");
        wr.WriteAttributeString("endTime", endTime.ToString(DateTimeFormatString));
        wr.WriteAttributeString("duration", elapsed.TotalSeconds.ToString());
        wr.WriteAttributeString("outcome", outcome);

        wr.WriteEndElement();  // outcome
        wr.WriteEndElement();  // method
      }
      cce.EndExpose();
    }

    public void WriteError(string message, IToken errorToken, IToken relatedToken, List<Block> trace) {
      Contract.Requires(errorToken != null);
      Contract.Requires(message != null);
      Contract.Requires(IsOpen && (trace == null || cce.Owner.Different(this, trace)));
      //modifies this.*, errorToken.*, relatedToken.*, trace.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("error");
        wr.WriteAttributeString("message", message);
        WriteTokenAttributes(errorToken);
        if (relatedToken != null) {
          wr.WriteStartElement("related");
          WriteTokenAttributes(relatedToken);
          wr.WriteEndElement();
        }
        if (trace != null) {
          wr.WriteStartElement("trace");
          {
            foreach (object bo in trace) {
              cce.LoopInvariant(wr != null);
              Contract.Assume(bo is Block);
              Block b = (Block)bo;
              wr.WriteStartElement("traceNode");
              {
                WriteTokenAttributes(b.tok);
                wr.WriteAttributeString("label", b.Label);
              }
              wr.WriteEndElement();
            }
            wr.WriteEndElement();
          }
        }
        wr.WriteEndElement();
      }
      cce.EndExpose();
    }

#if CCI
    public void WriteError(string message, Cci.Node offendingNode, List<Block> trace) {
      Contract.Requires(offendingNode != null);
      Contract.Requires(message != null);
      Contract.Requires(IsOpen && cce.Owner.Different(this, offendingNode));
      Contract.Requires(trace == null || cce.Owner.Different(this, trace));
      //modifies this.*, offendingNode.*, trace.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("error");
        wr.WriteAttributeString("message", message);
        WriteTokenAttributes(offendingNode);
        if (trace != null) {
          wr.WriteStartElement("trace");
          {
            foreach (object bo in trace) {
              cce.LoopInvariant(wr != null);
              Contract.Assume(bo is Block);
              Block b = (Block)bo;
              wr.WriteStartElement("traceNode");
              {
                this.WriteTokenAttributes(b.tok);
                wr.WriteAttributeString("label", b.Label);
              }
              wr.WriteEndElement();
            }
            wr.WriteEndElement();
          }
        }
        wr.WriteEndElement();
      }
      cce.EndExpose();
    }
#endif

    [Inside]
    private void WriteTokenAttributes(IToken tok) {
      Contract.Requires(wr != null && cce.IsPeerConsistent(wr));
      //modifies this.0, wr.*;
      if (tok != null && tok.filename != null) {
        wr.WriteAttributeString("file", tok.filename);
        wr.WriteAttributeString("line", tok.line.ToString());
        wr.WriteAttributeString("column", tok.col.ToString());
      }
    }

#if CCI
    [Inside]
    private void WriteTokenAttributes(Cci.Node node) {
      Contract.Requires(node != null);
      Contract.Requires(wr != null && cce.IsPeerConsistent(wr));
      //modifies this.0, wr.*;
      Contract.Assert(wr != null);
      if (node.SourceContext.Document != null) {
        wr.WriteAttributeString("file", node.SourceContext.Document.Name);
        wr.WriteAttributeString("line", node.SourceContext.StartLine.ToString());
        wr.WriteAttributeString("column", node.SourceContext.StartColumn.ToString());
      }
    }
#endif

    public void WriteStartInference(string inferenceName) {
      Contract.Requires(inferenceName != null);
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("inference");
        wr.WriteAttributeString("name", inferenceName);
      }
      cce.EndExpose();
    }

    public void WriteEndInference() {
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteEndElement();  // inference
      }
      cce.EndExpose();
    }

    public void WriteContractParaAssignment(string varName, string val) {
      Contract.Requires(varName != null);
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("assignment");
        wr.WriteAttributeString("name", varName);
        wr.WriteAttributeString("value", val);
        wr.WriteEndElement();
      }
      cce.EndExpose();
    }

    public void WriteStartFile(string filename) {
      Contract.Requires(filename != null);
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("file");
        wr.WriteAttributeString("name", filename);
      }
      cce.EndExpose();
    }

    public void WriteEndFile() {
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteEndElement();
      }
      cce.EndExpose();
    }

    public void WriteFileFragment(string fragment) {
      Contract.Requires(fragment != null);
      Contract.Requires(IsOpen);
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      cce.BeginExpose(this);
      {
        wr.WriteStartElement("fileFragment");
        wr.WriteAttributeString("name", fragment);
        wr.WriteEndElement();
      }
      cce.EndExpose();
    }
  }

  public class XmlFileScope : IDisposable {
    [Peer]
    [SpecPublic]
    XmlSink sink;

    [Captured]
    public XmlFileScope(XmlSink sink, string filename) {
      Contract.Requires(filename != null);
      Contract.Requires(sink == null || sink.IsOpen);
      //modifies sink.*;
      if (sink != null) {
        sink.WriteStartFile(filename);  // invoke this method while "sink" is still peer consistent
        cce.Owner.AssignSame(this, sink);
        this.sink = sink;
      }
    }

    public void Dispose() {
      if (sink != null) {
        Contract.Assume(sink.IsOpen);
        sink.WriteEndFile();
      }
    }
  }
}