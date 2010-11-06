using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  public abstract class LanguageModel : ILanguageSpecificModel
  {
    protected Dictionary<string, int> baseNameUse = new Dictionary<string, int>();
    protected Dictionary<Model.Element, string> canonicalName = new Dictionary<Model.Element, string>();
    protected Dictionary<Model.Element, string> localValue = new Dictionary<Model.Element, string>();

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
    protected virtual string CanonicalBaseName(Model.Element elt)
    {
      string res;
      if (localValue.TryGetValue(elt, out res))
        return res;
      return "";
    }

    public virtual void RegisterLocalValue(string name, Model.Element elt)
    {
      string curr;
      if (localValue.TryGetValue(elt, out curr) && CompareFields(name, curr) >= 0)
        return;
      localValue[elt] = name;
    }

    protected virtual string LiteralName(Model.Element elt)
    {
      if (elt is Model.Integer)
        return elt.ToString();
      if (elt is Model.Boolean)
        return elt.ToString();
      return null;
    }

    public virtual string CanonicalName(Model.Element elt)
    {
      string res;
      if (canonicalName.TryGetValue(elt, out res)) return res;
      res = LiteralName(elt);
      if (res == null) {
        var baseName = CanonicalBaseName(elt);
        int cnt;
        if (!baseNameUse.TryGetValue(baseName, out cnt)) {
          cnt = -1;
        }
        cnt++;
        res = baseName + "'" + cnt;
        baseNameUse[baseName] = cnt;
      }
      canonicalName.Add(elt, res);
      return res;
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
        var ch = nodes.ToDictionary(x => x.Name);
        foreach (var k in SortFields(ch.Keys))
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
    static bool HasAny(string s, string chrs)
    {
      foreach (var c in s)
        if (chrs.Contains(c))
          return true;
      return false;
    }

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

    public virtual int CompareFields(string f1, string f2)
    {
      bool s1 = HasAny(f1, "[<>]");
      bool s2 = HasAny(f2, "[<>]");
      if (s1 && !s2)
        return 1;
      if (!s1 && s2)
        return -1;
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

    public virtual IEnumerable<string> SortFields(IEnumerable<string> fields_)
    {
      var fields = new List<string>(fields_);
      fields.Sort(CompareFields);
      return fields;
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

    public EdgeName(string name) : this(null, name, emptyArgs) { }

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
