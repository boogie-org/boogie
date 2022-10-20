using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace SMTLib;

public class SExprParser
{
  private int linePos;
  private string currLine;
  private readonly AsyncQueue<string> sexpLines = new();

  public event Action<string> ErrorHandler;

  public void AddLine(string line)
  {
    sexpLines.Enqueue(line);
  }

  Task<string> ReadLine()
  {
    return sexpLines.Dequeue(CancellationToken.None);
  }
  
  async Task<char> SkipWs()
  {
    while (true)
    {
      if (currLine == null)
      {
        currLine = await ReadLine();
        if (currLine == null)
        {
          return '\0';
        }
      }


      while (linePos < currLine.Length && char.IsWhiteSpace(currLine[linePos]))
      {
        linePos++;
      }

      if (linePos < currLine.Length && currLine[linePos] != ';')
      {
        return currLine[linePos];
      }
      else
      {
        currLine = null;
        linePos = 0;
      }
    }
  }

  void Shift()
  {
    linePos++;
  }

  async Task<string> ParseId()
  {
    var sb = new StringBuilder();

    var begin = await SkipWs();

    var quoted = begin == '"' || begin == '|';
    if (quoted)
    {
      Shift();
    }

    while (true)
    {
      if (linePos >= currLine.Length)
      {
        if (quoted)
        {
          do
          {
            sb.Append("\n");
            currLine = await ReadLine();
          } while (currLine == "");
          if (currLine == null)
          {
            break;
          }

          linePos = 0;
        }
        else
        {
          break;
        }
      }

      var c = currLine[linePos++];
      if (quoted && c == begin)
      {
        break;
      }

      if (!quoted && (char.IsWhiteSpace(c) || c == '(' || c == ')'))
      {
        linePos--;
        break;
      }

      if (quoted && c == '\\' && linePos < currLine.Length && currLine[linePos] == '"')
      {
        sb.Append('"');
        linePos++;
        continue;
      }

      sb.Append(c);
    }

    return sb.ToString();
  }

  void ParseError(string msg)
  {
    ErrorHandler?.Invoke(msg);
  }

  public async IAsyncEnumerable<SExpr> ParseSExprs(bool top)
  {
    while (true)
    {
      var c = await SkipWs();
      if (c == '\0')
      {
        break;
      }

      if (c == ')')
      {
        if (top)
        {
          ParseError("stray ')'");
        }

        break;
      }

      string id;

      if (c == '(')
      {
        Shift();
        c = await SkipWs();
        if (c == '\0')
        {
          ParseError("expecting something after '('");
          break;
        }
        else if (c == '(')
        {
          id = "";
        }
        else
        {
          id = await ParseId();
        }

        var args = await ParseSExprs(false).ToListAsync();

        c = await SkipWs();
        if (c == ')')
        {
          Shift();
        }
        else
        {
          ParseError("unclosed '(" + id + "'");
        }

        yield return new SExpr(id, args);
      }
      else
      {
        id = await ParseId();
        yield return new SExpr(id);
      }

      if (top)
      {
        break;
      }
    }
  }
}