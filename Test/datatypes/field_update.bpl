// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Pair<A, B> {
  Pair(first: A, second: B)
}

procedure GenericUpdate<T>(p: Pair T int, value: T)
{
  var q: Pair T int;
  q := p->(first := value);
  assert q->first == value;
  assert q->second == p->second;
  q->second := 42;
  assert q == Pair(value, 42);
}

datatype Choice<T> {
  Left(value: T, kept: int),
  Right(value: T, flag: bool),
  Other(other: int)
}

procedure SharedField(c: Choice int)
{
  var updated: Choice int;
  updated := c->(value := 17);
  assert c is Left ==> updated == Left(17, c->kept);
  assert c is Right ==> updated == Right(17, c->flag);
  assert c is Other ==> updated == c;
}

procedure MissingField(c: Choice int)
requires !(c is Left);
{
  var updated: Choice int;
  updated := c;
  updated->kept := 23;
  assert updated == c;
}
