// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:inline 1} Copy<T>(v: T) returns (copy_v: T)
{
  copy_v := v;
}

type Value;
type Round;
datatype Option<T> { None(), Some(t: T) }

var decision: [Round]Option Value;
procedure Foo()
modifies decision;
{
  call decision := Copy((lambda r: Round :: None()));
  assert decision == (lambda r: Round :: None());
}
