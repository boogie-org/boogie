using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  public enum NameSeqSuffix
  {
    None,
    WhenNonZero,
    Always
  }

  public abstract class LanguageModel : ILanguageSpecificModel
  {
    protected Dictionary<string, int> baseNameUse = new Dictionary<string, int>();
    protected Dictionary<Model.Element, string> canonicalName = new Dictionary<Model.Element, string>();
    protected Dictionary<string, Model.Element> invCanonicalName = new Dictionary<string, Model.Element>();
    protected Dictionary<Model.Element, string> localValue = new Dictionary<Model.Element, string>();
    protected Dictionary<string, SourceLocation> sourceLocations; // initialized lazily by GetSourceLocation()
    public readonly Model model;

    protected virtual bool UseLocalsForCanonicalNames
    {
      get { return false; }
    }

    public readonly ViewOptions viewOpts;
    public LanguageModel(Model model, ViewOptions opts)
    {
      this.model = model;
      viewOpts = opts;
    }
    
    // Elements (other than integers and Booleans) get canonical names of the form 
    // "<base>'<idx>", where <base> is returned by this function, and <idx> is given 
    // starting with 0, and incrementing when there are conflicts between bases.
    //
    // This function needs to return an appropriate base name for the element. It is given
    // the element.
    //
    // A reasonable strategy is to check if it's a name of the local, and if so return it,
    // and otherwise use the type of element (e.g., return "seq" for elements representing
    // sequences). It is also possible to return "" in such cases.
    // 
    // The suff output parameter specifies whether the number sequence suffix should be 
    // always added, only when it's non-zero, or never.
    protected virtual string CanonicalBaseName(Model.Element elt, out NameSeqSuffix suff)
    {
      string res;
      if (elt is Model.Integer || elt is Model.Boolean) {
       suff = NameSeqSuffix.None;
       return elt.ToString();
      }
      suff = NameSeqSuffix.Always;
      if (UseLocalsForCanonicalNames) {
        if (localValue.TryGetValue(elt, out res))
          return res;
      }
      return "";
    }

    public virtual void RegisterLocalValue(string name, Model.Element elt)
    {
      string curr;
      if (localValue.TryGetValue(elt, out curr) && CompareFieldNames(name, curr) >= 0)
        return;
      localValue[elt] = name;
    }

    protected virtual string AppendSuffix(string baseName, int id)
    {
      return baseName + "'" + id.ToString();
    }

    public virtual string CanonicalName(Model.Element elt)
    {
      string res;
      if (canonicalName.TryGetValue(elt, out res)) return res;
      NameSeqSuffix suff;
      var baseName = CanonicalBaseName(elt, out suff);
      if (baseName == "")
        suff = NameSeqSuffix.Always;

      if (viewOpts.DebugMode && !(elt is Model.Boolean) && !(elt is Model.Number)) {
        baseName += string.Format("({0})", elt);
        suff = NameSeqSuffix.WhenNonZero;
      }
      
      int cnt;
      if (!baseNameUse.TryGetValue(baseName, out cnt))
        cnt = -1;
      cnt++;

      if (suff == NameSeqSuffix.Always || (cnt > 0 && suff == NameSeqSuffix.WhenNonZero))
        res = AppendSuffix(baseName, cnt);
      else
        res = baseName;
 
      baseNameUse[baseName] = cnt;
      canonicalName.Add(elt, res);
      invCanonicalName[res.Replace(" ", "")] = elt;
      return res;
    }

    public virtual Model.Element FindElement(string canonicalName)
    {
      Model.Element res;
      if (invCanonicalName.TryGetValue(canonicalName.Replace(" ", ""), out res))
        return res;
      return null;
    }
    
    public virtual string PathName(IEnumerable<IDisplayNode> path)
    {
      return path.Select(n => n.Name).Concat(".");
    }

    public abstract IEnumerable<IState> States { get; }

    /// <summary>
    /// Walks each input tree in BFS order, and force evaluation of Name and Value properties
    /// (to get reasonable numbering of canonical values).
    /// </summary>
    public void Flush(IEnumerable<IDisplayNode> roots)
    {
      var workList = new Queue<IDisplayNode>();

      Action<IEnumerable<IDisplayNode>> addList = (IEnumerable<IDisplayNode> nodes) =>
      {
        var tmp = nodes.Select(x => x.Name).ToArray();
        var ch = nodes.ToDictionary(x => x.Name);
        foreach (var k in SortFields(nodes))
          workList.Enqueue(ch[k]);
      };

      addList(roots);

      var visited = new HashSet<Model.Element>();
      while (workList.Count > 0) {
        var n = workList.Dequeue();
        
        var dummy1 = n.Name;
        var dummy2 = n.Value;

        if (n.Element != null) {
          if (visited.Contains(n.Element))
            continue;
          visited.Add(n.Element);
        }

        addList(n.Children);
      }
    }
    #region field name sorting
    /*
    static bool HasSpecialChars(string s)
    {
      for (int i = 0; i < s.Length; ++i)
        switch (s[i]) {
          case '[':
          case '<':
          case '>':
          case ']': 
          case '#':
          case '\\':
          case '(':
          case ')':
            return true;
        }
      return false;
    }
     */

    static ulong GetNumber(string s, int beg)
    {
      var end = beg;
      while (end < s.Length && char.IsDigit(s[end]))
        end++;
      ulong res;
      if (!ulong.TryParse(s.Substring(beg, end - beg), out res))
        return 0;
      return res;
    }

    public virtual int CompareFieldNames(string f1, string f2)
    {
      /*
      bool s1 = HasSpecialChars(f1);
      bool s2 = HasSpecialChars(f2);
      if (s1 && !s2)
        return 1;
      if (!s1 && s2)
        return -1; */
      var len = Math.Min(f1.Length, f2.Length);
      var numberPos = -1;
      for (int i = 0; i < len; ++i) {
        if (char.IsDigit(f1[i]) && char.IsDigit(f2[i])) {
          numberPos = i;
          break;
        }
        if (f1[i] != f2[i])
          break;
      }

      if (numberPos >= 0) {
        var v1 = GetNumber(f1, numberPos);
        var v2 = GetNumber(f2, numberPos);

        if (v1 < v2) return -1;
        else if (v1 > v2) return 1;
      }

      return string.CompareOrdinal(f1, f2);
    }

    public virtual int CompareFields(IDisplayNode n1, IDisplayNode n2)
    {
      var diff = (int)n1.Category - (int)n2.Category;
      if (diff != 0) return diff;
      else return CompareFieldNames(n1.Name, n2.Name);
    }

    public virtual IEnumerable<string> SortFields(IEnumerable<IDisplayNode> fields_)
    {
      var fields = new List<IDisplayNode>(fields_);
      fields.Sort(CompareFields);
      return fields.Select(f => f.Name);
    }
    #endregion



    #region Displaying source code
    class Position : IComparable<Position>
    {
      public int Line, Column, Index;
      public int CharPos;
      public string Name;

      public int CompareTo(Position other)
      {
        if (this.Line == other.Line)
          return this.Column - other.Column;
        return this.Line - other.Line;
      }
    }

    public SourceLocation GetSourceLocation(Model.CapturedState s)
    {
      if (sourceLocations == null) {
        GenerateSourceLocations();
      }

      SourceLocation res;
      sourceLocations.TryGetValue(s.Name, out res);
      return res;
    }

    protected virtual bool TryParseSourceLocation(string name, out string filename, out int line, out int column)
    {
      filename = name;
      line = 0;
      column = 0;

      var par = name.LastIndexOf('(');      
      if (par <= 0) return false;

      filename = name.Substring(0, par);
      var words = name.Substring(par + 1).Split(',', ')').Where(x => x != "").ToArray();
      if (words.Length != 2) return false;
      if (!int.TryParse(words[0], out line) || !int.TryParse(words[1], out column)) return false;

      return true;
    }

    protected virtual void GenerateSourceLocations()
    {
      sourceLocations = new Dictionary<string, SourceLocation>();

      var files = new Dictionary<string, List<Position>>();
      var sIdx = -1;
      foreach (var s in model.States) {
        sIdx++;
        int line, col;
        string fn;
        if (!TryParseSourceLocation(s.Name, out fn, out line, out col))
          continue;

        List<Position> positions;
        if (!files.TryGetValue(fn, out positions)) {
          positions = new List<Position>();
          files[fn] = positions;
        }
        positions.Add(new Position() { Name = s.Name, Line = line, Column = col, Index = sIdx });
      }

      foreach (var kv in files) {
        var positions = kv.Value;
        positions.Sort();

        string content = "";
        try {
          content = System.IO.File.ReadAllText(kv.Key);
        } catch {
          continue;
        }

        var currPosIdx = 0;
        var currLine = 1;
        var currColumn = 1;
        var output = new StringBuilder();
        var charPos = 0;

        foreach (var c in content) {
          if (c == '\n') {
            currColumn = int.MaxValue; // flush remaining positions in this line
          }

          while (currPosIdx < positions.Count && positions[currPosIdx].Line <= currLine && positions[currPosIdx].Column <= currColumn) {
            positions[currPosIdx].CharPos = charPos;
            SourceLocation.RtfAppendStateIdx(output, positions[currPosIdx].Index.ToString(), ref charPos);
            currPosIdx++;
          }

          SourceLocation.RtfAppend(output, c, ref charPos);

          if (c == '\n') {
            currLine++;
            currColumn = 1;
          } else {
            currColumn++;
          }
        }

        var resStr = output.ToString();
        foreach (var pos in positions) {
          sourceLocations[pos.Name] = new SourceLocation() { Header = pos.Name, Location = pos.CharPos, RichTextContent = resStr };
        }
      }
    }
    #endregion
  }

  public class EdgeName
  {
    static readonly Model.Element[] emptyArgs = new Model.Element[0];

    ILanguageSpecificModel langModel;
    string format;
    Model.Element[] args;

    public EdgeName(ILanguageSpecificModel n, string format, params Model.Element[] args)
    {
      this.langModel = n;
      this.format = format;
      this.args = args;
    }

    public EdgeName(string name) : this(null, name, emptyArgs) 
    {
      Util.Assert(name != null);
    }

    public override string ToString()
    {
      return Format();
    }

    public override int GetHashCode()
    {
      int res = format.GetHashCode();
      foreach (var c in args) {
        res += c.GetHashCode();
        res *= 13;
      }
      return res;
    }

    public override bool Equals(object obj)
    {
      EdgeName e = obj as EdgeName;
      if (e == null) return false;
      if (e == this) return true;
      if (e.format != this.format || e.args.Length != this.args.Length)
        return false;
      for (int i = 0; i < this.args.Length; ++i)
        if (this.args[i] != e.args[i])
          return false;
      return true;
    }

    protected virtual string Format()
    {
      if (args.Length == 0)
        return format;

      var res = new StringBuilder(format.Length);
      for (int i = 0; i < format.Length; ++i) {
        var c = format[i];

        /*
        var canonical = false;
        if (c == '%' && i < format.Length - 1) {
          if (format[i + 1] == 'c') {
            ++i;
            canonical = true;
          }
        }
         */

        if (c == '%' && i < format.Length - 1) {
          var j = i + 1;
          while (j < format.Length && char.IsDigit(format[j]))
            j++;
          var len = j - i - 1;
          if (len > 0) {
            var idx = int.Parse(format.Substring(i + 1, len));
            res.Append(langModel.CanonicalName(args[idx]));
            i = j - 1;
            continue;
          }
        }

        res.Append(c);
      }

      return res.ToString();
    }

    public virtual IEnumerable<Model.Element> Dependencies
    {
      get { return args; }
    }
  }

}
