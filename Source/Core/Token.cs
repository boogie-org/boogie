using System.Text;
using System.Collections.Generic;
using System.IO;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie
{
  [Immutable]
  public interface IToken
  {
    int kind { get; set; } // token kind
    string filename { get; set; } // token file
    int pos { get; set; } // token position in the source text (starting at 0)
    int col { get; set; } // token column (starting at 0)
    int line { get; set; } // token line (starting at 1)
    string /*!*/ val { get; set; } // token value

    bool IsValid { get; }
  }

  [Immutable]
  public class Token : IToken
  {
    public int _kind; // token kind
    string _filename; // token file
    public int _pos; // token position in the source text (starting at 0)
    public int _col; // token column (starting at 1)
    public int _line; // token line (starting at 1)

    public string /*!*/
      _val; // token value

    public Token next; // ML 2005-03-11 Tokens are kept in linked list

    public static readonly IToken /*!*/
      NoToken = new Token();

    public Token()
    {
      this._val = "anything so that it is nonnull";
    }

    public Token(int linenum, int colnum)
      : base()
    {
      this._line = linenum;
      this._col = colnum;
      this._val = "anything so that it is nonnull";
    }

    public int kind
    {
      get { return this._kind; }
      set { this._kind = value; }
    }

    public string filename
    {
      get { return this._filename; }
      set { this._filename = value; }
    }

    public int pos
    {
      get { return this._pos; }
      set { this._pos = value; }
    }

    public int col
    {
      get { return this._col; }
      set { this._col = value; }
    }

    public int line
    {
      get { return this._line; }
      set { this._line = value; }
    }

    public string /*!*/ val
    {
      get { return this._val; }
      set { this._val = value; }
    }

    public bool IsValid
    {
      get { return this._filename != null; }
    }
  }
}