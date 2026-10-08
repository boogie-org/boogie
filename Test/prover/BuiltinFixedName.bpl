// RUN: ! %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Boogie declares tickleBool by a fixed name, so it cannot step aside for a {:builtin} function. The blank and
// the bars still name that symbol.

function {:builtin " |tickleBool|"} t(b: bool): bool;

procedure P()
{
  assume !t(true);
  assert false;
}
