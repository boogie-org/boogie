// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Ref;
var Heap: HeapType;
type Field A B;
type HeapType = <A, B> [Ref, Field A B]B;

procedure mfl(one: float23e11, two: float23e11) returns ()
{
  assert two == one; 
}
