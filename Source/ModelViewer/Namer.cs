using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  class EltName
  {
    internal Model.Element elt;
    internal List<IEdgeName> nodes = new List<IEdgeName>();
    internal int score = StateNamer.maxScore;
    internal string theName;
    internal bool unfolded;
    internal int stateIdx;

    internal EltName(Model.Element e)
    {
      elt = e;
      theName = e.ToString();
    }
  }

  public class GlobalNamer
  {
    internal Dictionary<Model.Element, string> canonicalNames;
    INamerCallbacks cb;
    internal List<StateNamer> stateNamers = new List<StateNamer>();

    public GlobalNamer(INamerCallbacks cb)
    {
      this.cb = cb;
    }

    #region default namer callback implementations
    public static string DefaultCanonicalBaseName(Model.Element elt, IEdgeName edgeName, int stateIdx)
    {
      if (edgeName == null)
        return "";
      var name = edgeName.FullName();
      return name;
    }

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

    public static int CompareFields(string f1, string f2)
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

    public static IEnumerable<string> DefaultSortFields(IEnumerable<string> fields_)
    {
      var fields = new List<string>(fields_);
      fields.Sort(CompareFields);
      return fields;
    }
    #endregion

    public void ComputeCanonicalNames()
    {
      for (int i = 0; i < 2; i++)
        ComputeCanonicalNamesCore();
    }

    void ComputeCanonicalNamesCore()
    {
      var names = new Dictionary<Model.Element, EltName>();
      var namersArr = stateNamers.ToArray();
      for (int i = 0; i < namersArr.Length; ++i) {
        foreach (var n in namersArr[i].eltNames) {
          n.stateIdx = i;
          //if (n.nodes.Count == 0) continue;
          EltName curr;
          if (names.TryGetValue(n.elt, out curr) && curr.score <= n.score)
            continue;
          names[n.elt] = n;
        }
      }

      var canonicals = new Dictionary<Model.Element, string>();
      var usedNames = new Dictionary<string, int>();
      Model model = null;
      foreach (var n in names.Values) {
        string name = "";
        model = n.elt.Model;
        if (n.nodes.Count == 0) {
          name = cb.CanonicalBaseName(n.elt, null, 0);
          name = AppendIndex(usedNames, name);
        } else if (n.elt is Model.Boolean || n.elt is Model.Number)
          name = n.nodes[0].FullName();
        else {
          name = cb.CanonicalBaseName(n.elt, n.nodes[0], n.stateIdx);
          name = AppendIndex(usedNames, name);
        }
        canonicals[n.elt] = name;
      }

      canonicalNames = canonicals;

      foreach (var e in model.Elements) {
        if (!canonicals.ContainsKey(e)) {
          var name = cb.CanonicalBaseName(e, null, 0);
          canonicals[e] = AppendIndex(usedNames, name);
        }
      }

      for (int i = 0; i < namersArr.Length; ++i) {
        namersArr[i].ComputeBestName();
      }
    }

    private static string AppendIndex(Dictionary<string, int> usedNames, string name)
    {
      var idx = 0;
      if (!usedNames.TryGetValue(name, out idx))
        idx = 0;
      usedNames[name] = idx + 1;
      name = name + "'" + idx;
      return name;
    }

    public virtual string CanonicalName(Model.Element elt)
    {
      string res;
      if (canonicalNames != null && canonicalNames.TryGetValue(elt, out res))
        return res; // +" " + elt.ToString();
      return elt.ToString();
    }
  }

  public class StateNamer
  {
    GlobalNamer globalNamer;
    internal const int maxScore = 10000;
    internal List<EltName> eltNames = new List<EltName>();
    Dictionary<Model.Element, EltName> unfoldings = new Dictionary<Model.Element, EltName>();

    public StateNamer(GlobalNamer gn)
    {
      globalNamer = gn;
      gn.stateNamers.Add(this);
    }

    EltName GetName(Model.Element elt)
    {
      EltName res;
      if (unfoldings.TryGetValue(elt, out res))
        return res;
      res = new EltName(elt);
      eltNames.Add(res);
      unfoldings.Add(elt, res);
      return res;
    }

    int EdgeNameScore(IEdgeName name)
    {
      return name.Dependencies.Select(e => GetName(e).score).Concat1(0).Max() + name.Score;
    }

    internal void ComputeBestName()
    {
      foreach (var n in eltNames) {
        n.score = maxScore;
        string s;
        if (globalNamer.canonicalNames != null && globalNamer.canonicalNames.TryGetValue(n.elt, out s))
          n.theName = s;
      }

      while (true) {
        var changes = 0;
        var thisElts = eltNames.ToArray();
        foreach (var elt in thisElts) {
          var newScore = elt.nodes.Select(EdgeNameScore).Concat1(int.MaxValue).Min();
          if (newScore < elt.score) {
            elt.score = newScore;
            changes++;
          }
        }
        if (changes == 0 && thisElts.Length == eltNames.Count)
          break;
      }
      eltNames.Sort((x,y) => x.score - y.score);
      foreach (var elt in eltNames) {
        if (elt.nodes.Count > 0) {
          elt.nodes.Sort((x, y) => EdgeNameScore(x) - EdgeNameScore(y));
          elt.theName = elt.nodes[0].FullName();
        }
      }
    }

    void Unfold(IEnumerable<IDisplayNode> ns)
    {
      var workList = new Queue<IDisplayNode>(); // do BFS
      ns.Iter(workList.Enqueue);

      while (workList.Count > 0) {
        var n = workList.Dequeue();

        if (n.Element != null) {
          var prev = GetName(n.Element);
          prev.nodes.Add(n.Name);
          if (prev.unfolded) // we've already been here
            continue;
          prev.unfolded = true;
        }

        if (!n.Expandable) return;

        n.Expand().Iter(workList.Enqueue);
      }
    }

    public void AddName(Model.Element elt, IEdgeName name)
    {
      var e = GetName(elt);
      e.nodes.Add(name);
    }

    public void ComputeNames(IEnumerable<IDisplayNode> n)
    {
      Unfold(n);
      ComputeBestName();
    }

    public virtual string ElementName(Model.Element elt)
    {
      return GetName(elt).theName;
    }

    public virtual IEnumerable<IEdgeName> Aliases(Model.Element elt)
    {
      return GetName(elt).nodes;
    }

    public virtual string CanonicalName(Model.Element elt)
    {
      return globalNamer.CanonicalName(elt);
    }
  }

  public class EdgeName : IEdgeName
  {
    static readonly Model.Element[] emptyArgs = new Model.Element[0];

    string formatFull, formatShort;
    Model.Element[] args;
    StateNamer namer;

    public EdgeName(StateNamer n, string formatFull, string formatShort, params Model.Element[] args)
    {
      this.namer = n;
      this.formatFull = formatFull;
      this.formatShort = formatShort;
      this.args = args;
      Score = args.Length * 10;
    }

    public EdgeName(StateNamer n, string formatBoth, params Model.Element[] args)
      : this(n, formatBoth, formatBoth, args)
    {
    }

    public EdgeName(string name) : this(null, name, emptyArgs) { }

    public virtual int CompareTo(IEdgeName other)
    {
      return string.CompareOrdinal(this.FullName(), other.FullName());
    }

    public override string ToString()
    {
      return FullName();
    }

    public override int GetHashCode()
    {
      int res = formatFull.GetHashCode() + formatShort.GetHashCode() * 17;
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
      if (e.formatFull != this.formatFull || e.formatShort != this.formatShort || e.args.Length != this.args.Length)
        return false;
      for (int i = 0; i < this.args.Length; ++i)
        if (this.args[i] != e.args[i])
          return false;
      return true;
    }

    protected virtual string Format(string format)
    {
      if (args.Length == 0)
        return format;

      var res = new StringBuilder(format.Length);
      for (int i = 0; i < format.Length; ++i) {
        var c = format[i];
        var canonical = false;

        if (c == '%' && i < format.Length - 1) {
          if (format[i + 1] == 'c') {
            ++i;
            canonical = true;
          }
        }

        if (c == '%' && i < format.Length - 1) {
          var j = i + 1;
          while (j < format.Length && char.IsDigit(format[j]))
            j++;
          var len = j - i - 1;
          if (len > 0) {
            var idx = int.Parse(format.Substring(i + 1, len));
            res.Append(canonical ? namer.CanonicalName(args[idx]) : namer.ElementName(args[idx]));
            i = j - 1;
            continue;
          }
        }

        res.Append(c);
      }

      return res.ToString();
    }

    public virtual string FullName()
    {
      return Format(formatFull);
    }

    public virtual string ShortName()
    {
      return Format(formatShort);
    }

    public virtual IEnumerable<Model.Element> Dependencies
    {
      get { return args; }
    }

    public virtual int Score { get; set; }
  }

}
