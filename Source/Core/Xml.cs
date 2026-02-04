using System;
using System.Xml;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  public class XmlSink
  {
    string filename;
    private CoreOptions options;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(filename != null);
    }

    [Rep] XmlWriter wr;

    public bool IsOpen
    {
      get { return wr != null; }
    }

    public XmlSink(CoreOptions options, string filename)
    {
      
      this.filename = filename;
      this.options = options;
    }

    /// <summary>
    /// Returns null on success, in which case the caller should eventually invoke Close.
    /// Returns an error string on failure.
    /// </summary>
    public string Open()
    {
      //modifies this.*;
      Contract.Ensures(IsOpen);
      if (wr != null)
      {
        Close();
      }

      Cce.BeginExpose(this);
      XmlWriterSettings settings = new XmlWriterSettings();
      settings.Indent = true;
      wr = XmlWriter.Create(filename, settings);
      wr.WriteStartDocument();
      wr.WriteStartElement("boogie");
      wr.WriteAttributeString("version", options.VersionNumber);
      wr.WriteAttributeString("commandLine", Environment.CommandLine);
      Cce.EndExpose();
      return null; // success
    }

    public void Close()
    {
      //modifies this.*;
      if (wr != null)
      {
        Cce.BeginExpose(this);
        {
          wr.WriteEndDocument();
          wr.Close();
          wr = null;
        }
        Cce.EndExpose();
      }
    }

    const string DateTimeFormatString = "u";

    public void WriteStartMethod(string methodName, DateTime startTime)
    {
      
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      wr.WriteStartElement("method");
      wr.WriteAttributeString("name", methodName);
      wr.WriteAttributeString("startTime", startTime.ToString(DateTimeFormatString));
      Cce.EndExpose();
    }

    public void WriteEndMethod(string outcome, DateTime endTime, TimeSpan elapsed, int? resourceCount)
    {
      
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteStartElement("conclusion");
        wr.WriteAttributeString("endTime", endTime.ToString(DateTimeFormatString));
        wr.WriteAttributeString("duration", elapsed.TotalSeconds.ToString());
        if (resourceCount is not null)
        {
          wr.WriteAttributeString("resourceCount", resourceCount.ToString());
        }

        wr.WriteAttributeString("outcome", outcome);

        wr.WriteEndElement(); // outcome
        wr.WriteEndElement(); // method
      }
      Cce.EndExpose();
    }

    public void WriteSplit(int splitNum, int iteration, IEnumerable<AssertCmd> asserts, DateTime startTime,
                           string outcome, TimeSpan elapsed, int? resourceCount)
    {
      
      
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);

      Cce.BeginExpose(this);
      {
        wr.WriteStartElement("assertionBatch");
        wr.WriteAttributeString("number", splitNum.ToString());
        wr.WriteAttributeString("iteration", iteration.ToString());
        wr.WriteAttributeString("startTime", startTime.ToString(DateTimeFormatString));

        foreach(var assert in asserts)
        {
          var token = assert.tok;
          wr.WriteStartElement("assertion");
          wr.WriteAttributeString("file", token.filename);
          wr.WriteAttributeString("line", token.line.ToString());
          wr.WriteAttributeString("column", token.col.ToString());
          wr.WriteEndElement(); // assertion
        }

        wr.WriteStartElement("conclusion");
        wr.WriteAttributeString("duration", elapsed.TotalSeconds.ToString());
        wr.WriteAttributeString("outcome", outcome);
        if (resourceCount is not null)
        {
          wr.WriteAttributeString("resourceCount", resourceCount.ToString());
        }
        wr.WriteEndElement(); // conclusion

        wr.WriteEndElement(); // assertionBatch
      }
      Cce.EndExpose();
    }
    
    public void WriteError(string message, IToken errorToken, IToken relatedToken, List<Block> trace)
    {
      
      
      
      //modifies this.*, errorToken.*, relatedToken.*, trace.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteStartElement("error");
        wr.WriteAttributeString("message", message);
        WriteTokenAttributes(errorToken);
        if (relatedToken != null)
        {
          wr.WriteStartElement("related");
          WriteTokenAttributes(relatedToken);
          wr.WriteEndElement();
        }

        if (trace != null)
        {
          wr.WriteStartElement("trace");
          {
            foreach (object bo in trace)
            {
              Cce.LoopInvariant(wr != null);
              Contract.Assume(bo is Block);
              Block b = (Block) bo;
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
      Cce.EndExpose();
    }

#if CCI
    public void WriteError(string message, Cci.Node offendingNode, List<Block> trace) {
      
      
      
      
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
    private void WriteTokenAttributes(IToken tok)
    {
      
      //modifies this.0, wr.*;
      if (tok != null && tok.filename != null)
      {
        wr.WriteAttributeString("file", tok.filename);
        wr.WriteAttributeString("line", tok.line.ToString());
        wr.WriteAttributeString("column", tok.col.ToString());
      }
    }

#if CCI
    [Inside]
    private void WriteTokenAttributes(Cci.Node node) {
      
      
      //modifies this.0, wr.*;
      Contract.Assert(wr != null);
      if (node.SourceContext.Document != null) {
        wr.WriteAttributeString("file", node.SourceContext.Document.Name);
        wr.WriteAttributeString("line", node.SourceContext.StartLine.ToString());
        wr.WriteAttributeString("column", node.SourceContext.StartColumn.ToString());
      }
    }
#endif

    public void WriteStartInference(string inferenceName)
    {
      
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteStartElement("inference");
        wr.WriteAttributeString("name", inferenceName);
      }
      Cce.EndExpose();
    }

    public void WriteEndInference()
    {
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteEndElement(); // inference
      }
      Cce.EndExpose();
    }

    public void WriteContractParaAssignment(string varName, string val)
    {
      
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteStartElement("assignment");
        wr.WriteAttributeString("name", varName);
        wr.WriteAttributeString("value", val);
        wr.WriteEndElement();
      }
      Cce.EndExpose();
    }

    public void WriteStartFile(string filename)
    {
      
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteStartElement("file");
        wr.WriteAttributeString("name", filename);
      }
      Cce.EndExpose();
    }

    public void WriteEndFile()
    {
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteEndElement();
      }
      Cce.EndExpose();
    }

    public void WriteFileFragment(string fragment)
    {
      
      
      //modifies this.*;
      Contract.Ensures(IsOpen);
      Contract.Assert(wr != null);
      Cce.BeginExpose(this);
      {
        wr.WriteStartElement("fileFragment");
        wr.WriteAttributeString("name", fragment);
        wr.WriteEndElement();
      }
      Cce.EndExpose();
    }
  }

  public class XmlFileScope : IDisposable
  {
    [Peer] [SpecPublic] XmlSink sink;

    [Captured]
    public XmlFileScope(XmlSink sink, string filename)
    {
      
      
      //modifies sink.*;
      if (sink != null)
      {
        sink.WriteStartFile(filename); // invoke this method while "sink" is still peer consistent
        Cce.Owner.AssignSame(this, sink);
        this.sink = sink;
      }
    }

    public void Dispose()
    {
      if (sink != null)
      {
        Contract.Assume(sink.IsOpen);
        sink.WriteEndFile();
      }
    }
  }
}
