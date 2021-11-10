using System.Collections.Generic;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.SMTLib
{
  public class SMTLibNamer : UniqueNamer
  {
    public IDictionary<string /*!*/, string /*!*/> /*!*/
      LabelCounters; // Absy id -> local id

    public IDictionary<string /*!*/, string /*!*/> /*!*/
      CounterToLabels; // local id -> Absy id

    private int CurrentLabelId;

    public override void ResetLabelCount()
    {
      LabelCounters = new Dictionary<string, string>();
      CounterToLabels = new Dictionary<string, string>();
      CurrentLabelId = 0;
    }

    public override string LabelVar(string s)
    {
      return "%lbl%" + LabelName(s);
    }

    public override string LabelName(string s)
    {
      if (s[0] == '+' || s[0] == '@')
      {
        return s[0] + AbsyIndexToLocalIndex(s.Substring(1));
      }
      else
      {
        return AbsyIndexToLocalIndex(s);
      }
    }

    private string AbsyIndexToLocalIndex(string s)
    {
      if (!LabelCounters.TryGetValue(s, out var counter))
      {
        counter = CurrentLabelId.ToString();
        CurrentLabelId++;
        LabelCounters[s] = counter;
        CounterToLabels[counter] = s;
      }

      return counter;
    }

    public override string AbsyLabel(string s)
    {
      if (s[0] == '+' || s[0] == '@')
      {
        return s[0] + cce.NonNull(CounterToLabels[s.Substring(1)]);
      }
      else
      {
        return cce.NonNull(CounterToLabels[s.Substring(1)]);
      }
    }

    public SMTLibNamer()
    {
      this.Spacer = "@@";
      LabelCounters = new Dictionary<string, string>();
      CounterToLabels = new Dictionary<string, string>();
      CurrentLabelId = 0;
    }

    private SMTLibNamer(SMTLibNamer namer) : base(namer)
    {
    }

    public override object Clone()
    {
      return new SMTLibNamer(this);
    }

    public override void Reset()
    {
      LabelCounters.Clear();
      CounterToLabels.Clear();
      CurrentLabelId = 0;
      base.Reset();
    }
  }
}