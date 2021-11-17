using System;
using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
  internal abstract class ModelParser
  {
    protected Model currModel;
    int lineNo;
    internal List<Model> resModels = new();
    internal System.IO.TextReader rd;
    string lastLine = "";
    protected static Regex seps = new Regex("( |(?=\")|(?<=\"))");
    protected static Regex bitVec = new Regex(@"\(_ BitVec (\d+)\)");
    protected static Regex bv = new Regex(@"\(_ bv(\d+) (\d+)\)");
    protected static Regex fpType = new Regex(@"\(_ FloatingPoint (\d+) (\d+)\)");

    protected void NewModel()
    {
      lastLine = "";
      currModel = new Model();
      resModels.Add(currModel);
    }

    protected Exception BadModelException(string msg)
    {
      return new ArgumentException($"Invalid model: {msg}, at line {lineNo} ({lastLine})");
    }

    protected string ReadLine()
    {
      var l = rd.ReadLine();
      if (l != null)
      {
        lineNo++;
        lastLine = l;
      }

      return l;
    }

    Model.Element GetElt(string name)
    {
      Model.Element ret = currModel.TryMkElement(name);
      if (ret == null)
      {
        throw BadModelException("invalid element name " + name);
      }

      return ret;
    }

    protected Model.Element GetElt(object o)
    {
      if (o is string s)
      {
        return GetElt(s);
      }

      List<object> os = (List<object>) o;
      if (!(os[0] is string))
      {
        os.Insert(0, "_"); // KLM: fix crash on ((as const (Array Int Int)) 0)
      }

      List<Model.Element> args = new List<Model.Element>();
      for (int i = 1; i < os.Count; i++)
      {
        args.Add(GetElt(os[i]));
      }

      return new Model.DatatypeValue(currModel, (string) os[0], args);
    }

    protected int CountOpenParentheses(string s, int n)
    {
      int f = n;
      foreach (char c in s)
      {
        if (c == '(')
        {
          f++;
        }
        else if (c == ')')
        {
          f--;
        }
      }

      if (f < 0)
      {
        throw BadModelException("mismatched parentheses in datatype term");
      }

      return f;
    }

    internal abstract void Run();
  }
}
