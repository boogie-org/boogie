using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Boogie;


public delegate void ErrorReporterDelegate(ErrorInformation errInfo);

public enum ErrorKind
{
  Assertion,
  Precondition,
  Postcondition,
  InvariantEntry,
  InvariantMaintainance
}

public class ErrorInformation
{
  public readonly IToken Tok;
  public string Msg;
  public string Category { get; set; }
  public readonly List<AuxErrorInfo> Aux = new List<AuxErrorInfo>();
  public string OriginalRequestId { get; set; }
  public string RequestId { get; set; }
  public ErrorKind Kind { get; set; }
  public string ImplementationName { get; set; }
  public TextWriter Out = new StringWriter();
  public TextWriter ModelWriter = new StringWriter();

  public string FullMsg
  {
    get
    {
      return Category != null ? string.Format("{0}: {1}", Category, Msg) : Msg;
    }
  }

  public struct AuxErrorInfo
  {
    public readonly IToken Tok;
    public readonly string Msg;
    public readonly string Category;

    public string FullMsg
    {
      get { return Category != null ? string.Format("{0}: {1}", Category, Msg) : Msg; }
    }

    public AuxErrorInfo(IToken tok, string msg, string category = null)
    {
      Tok = tok;
      Msg = CleanUp(msg);
      Category = category;
    }
  }

  protected ErrorInformation(IToken tok, string msg)
  {
    Contract.Requires(tok != null);
    Contract.Requires(1 <= tok.line && 1 <= tok.col);
    Contract.Requires(msg != null);

    Tok = tok;
    Msg = CleanUp(msg);
  }

  internal static ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId = null,
    string originalRequestId = null, string category = null)
  {
    var result = new ErrorInformation(tok, msg);
    result.RequestId = requestId;
    result.OriginalRequestId = originalRequestId;
    result.Category = category;
    return result;
  }

  public virtual void AddAuxInfo(IToken tok, string msg, string category = null)
  {
    Contract.Requires(tok != null);
    Contract.Requires(1 <= tok.line && 1 <= tok.col);
    Contract.Requires(msg != null);
    Aux.Add(new AuxErrorInfo(tok, msg, category));
  }

  protected static string CleanUp(string msg)
  {
    if (msg.ToLower().StartsWith("error: "))
    {
      return msg.Substring(7);
    }
    else
    {
      return msg;
    }
  }
}

public class ErrorInformationFactory
{
  public virtual ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId = null,
    string originalRequestId = null, string category = null)
  {
    Contract.Requires(1 <= tok.line && 1 <= tok.col);
    Contract.Requires(msg != null);

    return ErrorInformation.CreateErrorInformation(tok, msg, requestId, originalRequestId, category);
  }
}