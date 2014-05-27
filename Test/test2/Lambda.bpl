// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %boogie -noinfer -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo()
{
  var a: [int]int;
  var c:int,b:bool;
  a := (lambda y:int :: if b then y + c else 7);
  assume b;
  assert a[3] == c+3;
}

procedure bar()
{
  assert (lambda x:int :: x > 0)[10];
  
}

type t1;

procedure baz()
{
  var m:[int,t1]int;
  var t:t1, t2:t1;

  m := (lambda i:int, tt:t1 :: if tt == t then i else 12);
  assert m[1,t] == 1;
  assert t == t2 || m[1,t2] == 12;
  assert  m[12,t2] == 12;
  
}


procedure fail()
{
  var m:[int,t1]int;
  var t:t1, t2:t1;

  m := (lambda i:int, tt:t1 :: if tt == t then i else 12);
  assert m[1,t2] == 12;
  assert m[1,t] == 2;
}

type set = [int]bool;
function union(a:set, b:set) : set;
axiom (forall a,b:set :: union(a,b) == (lambda x:int :: a[x] || b[x]));

function diff(a:set, b:set) : set {(lambda x:int :: a[x] && !b[x]) }

procedure a()
{
  var a:set, b:set;
  assume a[1];
  assume b[2];
  assert union(a,b)[1];
  assert union(a,b)[2];
  assume !b[1];
  assert diff(a,b)[1];
  assert !diff(a,b)[2];
}

procedure nestedLambda()
{
  var a: [int][int]int;

  a := (lambda x: int :: (lambda y: int :: x+y));
}

// The following tests that the lambda in the desugaring of the
// call command gets replaced.
procedure P();
  ensures (lambda y: int :: y == y)[15];
procedure Q()
{
  call P();
}
