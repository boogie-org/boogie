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
    internal int score = Namer.maxScore;
    internal string theName;
    internal bool unfolded;
    internal int stateIdx;

    internal EltName(Model.Element e)
    {
      elt = e;
      theName = e.ToString();
    }
  }

  public class Namer
  {
    internal const int maxScore = 10000;
    List<EltName> eltNames = new List<EltName>();
    Dictionary<Model.Element, EltName> unfoldings = new Dictionary<Model.Element, EltName>();
    Dictionary<Model.Element, string> canonicalNames;

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

    void ComputeBestName()
    {
      foreach (var n in eltNames) {
        n.score = maxScore;
        string s;
        if (canonicalNames != null && canonicalNames.TryGetValue(n.elt, out s))
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

    void Unfold(IDisplayNode n)
    {
      if (n.Element != null) {
        var prev = GetName(n.Element);
        prev.nodes.Add(n.Name);
        if (prev.unfolded) // we've already been here
          return;
        prev.unfolded = true;
      }

      if (!n.Expandable) return;

      foreach (var c in n.Expand()) {
        Unfold(c);
      }
    }

    public void AddName(Model.Element elt, IEdgeName name)
    {
      var e = GetName(elt);
      e.nodes.Add(name);
    }

    public void ComputeNames(IEnumerable<IDisplayNode> n)
    {
      n.Iter(Unfold);
      ComputeBestName();
    }

    public static void ComputeCanonicalNames(IEnumerable<Namer> namers)
    {
      var names = new Dictionary<Model.Element, EltName>();
      var namersArr = namers.ToArray();
      for (int i = 0; i < namersArr.Length; ++i) {
        foreach (var n in namersArr[i].eltNames) {
          n.stateIdx = i;
          if (n.nodes.Count == 0) continue;
          EltName curr;
          if (names.TryGetValue(n.elt, out curr) && curr.score <= n.score)
            continue;
          names[n.elt] = n;
        }
      }

      var canonicals = new Dictionary<Model.Element, string>();      
      foreach (var n in names.Values) {
        if (n.elt is Model.Boolean || n.elt is Model.Number)
          canonicals[n.elt] = n.nodes[0].FullName();
        else
          canonicals[n.elt] = n.nodes[0].FullName() + "." + n.stateIdx;
      }

      var unnamedIdx = 1;

      for (int i = 0; i < namersArr.Length; ++i) {
        namersArr[i].canonicalNames = canonicals;
        foreach (var n in namersArr[i].eltNames) {
          if (!canonicals.ContainsKey(n.elt)) {
            canonicals[n.elt] = string.Format("${0}", unnamedIdx++);
          }
        }
      }

      for (int i = 0; i < namersArr.Length; ++i) {
        namersArr[i].ComputeBestName();
      }
    }

    public virtual string CanonicalName(Model.Element elt)
    {
      string res;
      if (canonicalNames.TryGetValue(elt, out res))
        return res; // +" " + elt.ToString();
      return elt.ToString();
    }

    public virtual string ElementName(Model.Element elt)
    {
      return GetName(elt).theName;
    }

    public virtual IEnumerable<IEdgeName> Aliases(Model.Element elt)
    {
      return GetName(elt).nodes;
    }
  }

  public class EdgeName : IEdgeName
  {
    static readonly Model.Element[] emptyArgs = new Model.Element[0];

    string formatFull, formatShort;
    Model.Element[] args;
    Namer namer;

    public EdgeName(Namer n, string formatFull, string formatShort, params Model.Element[] args)
    {
      this.namer = n;
      this.formatFull = formatFull;
      this.formatShort = formatShort;
      this.args = args;
      Score = args.Length * 10;
    }

    public EdgeName(Namer n, string formatMixed, params Model.Element[] args)
      : this(n, formatMixed, formatMixed, args)
    {
      var beg = formatMixed.IndexOf("%(");
      var end = formatMixed.IndexOf("%)");
      if (beg >= 0 && end > beg) {
        this.formatShort = formatMixed.Substring(0, beg) + formatMixed.Substring(end + 2);
        this.formatFull = formatMixed.Replace("%(", "").Replace("%)", "");
      }
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
        if (c == '%' && i < format.Length - 1) {
          var j = i + 1;
          while (j < format.Length && char.IsDigit(format[j]))
            j++;
          var len = j - i - 1;
          if (len > 0) {
            var idx = int.Parse(format.Substring(i + 1, len));
            res.Append(namer.ElementName(args[idx]));
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
