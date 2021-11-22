using System;
using System.Collections.Generic;

namespace Microsoft.Boogie
{
  class ParserZ3 : ModelParser
  {
    private readonly Func<string, string> nameMapper;

    public ParserZ3(Func<string,string> nameMapper)
    {
      this.nameMapper = nameMapper;
    }

    List<object> GetFunctionTokens(string newLine)
    {
      if (newLine == null)
      {
        return null;
      }

      newLine = bitVec.Replace(newLine, "bv${1}");
      newLine = bv.Replace(newLine, "bv${1}[${2}]");
      newLine = fpType.Replace(newLine, "float${2}e${1}");
      string line = newLine;
      
      int openParenCounter = CountOpenParentheses(newLine, 0);
      if (!newLine.Contains("}"))
      {
        while (openParenCounter > 0)
        {
          newLine = ReadLine();
          if (newLine == null)
          {
            return null;
          }

          line += newLine;
          openParenCounter = CountOpenParentheses(newLine, openParenCounter);
        }
      }

      line = line.Replace("(", " ( ");
      line = line.Replace(")", " ) ");
      var tuple = seps.Split(line);

      List<object> newTuple = new List<object>();
      var wordStack = new Stack<Tuple<string, List<object>>>();
      foreach (var elem in tuple) {
        if (elem == "" || elem == " ")
        {
          continue;
        }

        if (elem == "(" || elem == "\"" && (wordStack.Count == 0 || wordStack.Peek().Item1 != "\""))
        {
          var ls = Tuple.Create(elem, new List<object>());
          wordStack.Push(ls);
        }
        else if (elem == ")")
        {
          var tup = wordStack.Pop();
          if (tup.Item1 != "(")
          {
            throw BadModelException("unmatched parentheses");
          }

          var ls = tup.Item2;
          if (wordStack.Count > 0)
          {
            wordStack.Peek().Item2.Add(ls);
          }
          else
          {
            newTuple.Add(ls);
          }
        }
        else if (elem == "\"")
        {
          var words = "\"" + String.Join(" ", wordStack.Pop().Item2) + "\"";
          if (wordStack.Count > 0)
          {
            wordStack.Peek().Item2.Add(String.Join(" ", words));
          }
          else
          {
            newTuple.Add(words);
          }
        }
        else if (wordStack.Count > 0)
        {
          wordStack.Peek().Item2.Add(DisplayName(elem));
        }
        else
        {
          newTuple.Add(DisplayName(elem));
        }
      }

      return newTuple;
    }

    private string DisplayName(string elem)
    {
      var displayName = nameMapper(elem);
      displayName = bitVec.Replace(displayName, "bv${1}");
      displayName = bv.Replace(displayName, "bv${1}[${2}]");
      displayName = fpType.Replace(displayName, "float${2}e${1}");
      return displayName;
    }

    internal override void Run()
    {
      while (true)
      {
        var line = ReadLine();
        if (line == null)
        {
          break; // end of model, everything fine
        }

        if (line == "Counterexample:" || line == "Error model: " || line == "*** MODEL")
        {
          NewModel();
          continue;
        }

        if (line.EndsWith(": Invalid.") || line.EndsWith(": Valid.") || line.StartsWith("labels:"))
        {
          continue;
        }

        if (line == "END_OF_MODEL" || line == "." || line == "*** END_MODEL")
        {
          continue;
        }

        var words = GetFunctionTokens(line);
        if (words.Count == 0)
        {
          continue;
        }

        var lastWord = words[^1];

        if (currModel == null)
        {
          throw BadModelException("model begin marker not found");
        }

        var stateMarker = "*** STATE ";
        if (line.StartsWith(stateMarker))
        {
          var name = line.Substring(stateMarker.Length);
          var cs = name == "<initial>" ? currModel.InitialState : currModel.MkState(name);

          while (true)
          {
            var stateLine = ReadLine();
            if (stateLine == "*** END_STATE")
            {
              break;
            }

            var tuple = GetFunctionTokens(stateLine);
            if (tuple == null)
            {
              throw BadModelException("EOF in state table");
            }

            if (tuple.Count == 0)
            {
              continue;
            }

            if (tuple.Count == 3 && tuple[0] is string && tuple[1] is string && (string) tuple[1] == "->")
            {
              cs.AddBinding((string) tuple[0], GetElt(tuple[2]));
            }
            else if (tuple.Count == 2 && tuple[1] is string && ((string)tuple[1]) == "->")
            {
              // This line says that words[0] has no value in the model.
              // Ignore this line.
            }
            else
            {
              throw BadModelException("invalid state tuple definition");
            }
          }

          continue;
        }

        if (words.Count == 3 && words[1] is string && ((string) words[1]) == "->")
        {
          var funName = (string) words[0];
          
          Model.Func fn;

          if (lastWord is "{")
          {
            fn = currModel.MkFunc(funName, null);
            while (true)
            {
              var tuple = GetFunctionTokens(ReadLine());
              if (tuple == null)
              {
                throw BadModelException("EOF in function table");
              }

              if (tuple.Count == 0)
              {
                continue;
              }

              string tuple0 = tuple[0] as string;
              if (tuple.Count == 1)
              {
                if (tuple0 == "}")
                {
                  break;
                }

                if (fn.Else != null) {
                  throw BadModelException("multiple else cases");
                }
                fn.Else = GetElt(tuple[0]);
                continue;
              }

              string tuplePenultimate = tuple[^2] as string;
              if (tuple.Count == 2 || tuplePenultimate != "->")
              {
                throw BadModelException("invalid function tuple definition");
              }

              var resultName = tuple[^1];

              if (tuple0 == "else")
              {
                if (fn.Else != null) {
                  throw BadModelException("multiple else cases");
                }
                if (resultName is not "#unspecified")
                {
                  fn.Else = GetElt(resultName);
                }
                continue;
              }

              fn.Arity = tuple.Count - 2;
              var args = new Model.Element[(int) fn.Arity]; 
              for (int i = 0; i < fn.Arity; ++i)
              {
                args[i] = GetElt(tuple[i]);
              }

              fn.AddApp(GetElt(resultName), args);
            }
          }
          else
          {
            fn = currModel.MkFunc(funName, 0);
            fn.SetConstant(GetElt(lastWord));
          }
        }
        else if (words.Count == 2 && words[1] is string && ((string)words[1]) == "->")
        {
          // This line says that words[0] has no value in the model.
          // Ignore this line.
        }
        else
        {
          throw BadModelException("unidentified line");
        }
      }
    }
  }
}