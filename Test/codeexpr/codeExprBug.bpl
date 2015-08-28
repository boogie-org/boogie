// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure p() returns ($r: int);
  ensures |{ $bb0: return ($r == 1); }|;

implementation p() returns ($x: int)
{
  $x := 1;
  return;
}

procedure q()
  ensures |{ var $b: bool; $0: $b := true; goto $1; $1: return $b; }|;
{
}
