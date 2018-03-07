// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type float = float24e8;

function {:builtin "fp.isNaN"} isNaN(float) returns (bool);
function {:inline} id(f:float) returns (float) {f}

procedure Main()
{
  var nan1, nan2: float;
  assume isNaN(nan1);
  nan2 := id(nan1);
  assert !isNaN(nan2);
}
