#nullable enable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace VCGeneration;

public class FocusOrigin : TokenWrapper, IImplementationPartOrigin {

  public FocusOrigin(IImplementationPartOrigin inner, List<(IToken Token, bool DidFocus)> focusChoices) : base(inner) {
    Inner = inner;
    FocusChoices = focusChoices;
  }

  public new IImplementationPartOrigin Inner { get; }
  public List<(IToken Token, bool DidFocus)> FocusChoices { get; }
  public string ShortName {
    get {
      var choices = string.Join(",", FocusChoices.Select(b => (b.DidFocus ? "+" : "-") + b.Token.line));
      return $"{Inner.ShortName}/focus[{choices}]";
    }
  }
}