// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const K: int;

function f(int) returns (int);

axiom (exists k: int :: f(k) == K);

procedure Find(a: int, b: int) returns (k: int);
  requires a <= b && (forall j: int :: a < j && j < b ==> f(j) != K);
  ensures f(k) == K;

// nondeterministic, unstructured, recursive version
implementation Find(a: int, b: int) returns (k: int)
{
  entry:
    goto A, B, C;

  A:
    assume f(a) == K;
    k := a;
    return;

  B:
    assume f(b) == K;
    k := b;
    return;

  C:
    assume f(a) != K && f(b) != K;
    call k := Find(a-1, b+1);
    return;
}

// nondeterministic, recursive version
implementation Find(a: int, b: int) returns (k: int)
{
  if (*) {
    assume f(a) == K;
    k := a;
  } else if (*) {
    assume f(b) == K;
    k := b;
  } else {
    assume f(a) != K && f(b) != K;
    call k := Find(a-1, b+1);
  }
}

// deterministic, structured, recursive version
implementation Find(a: int, b: int) returns (k: int)
{
  if (f(a) == K) {
    k := a;
  } else if (f(b) == K) {
    k := b;
  } else {
    call k := Find(a-1, b+1);
  }
}
 
// deterministic, structured, iterative version
implementation Find(a: int, b: int) returns (k: int)
{
  var x: int, y: int;

  x := a;
  y := b;

  while (f(x) != K && f(y) != K)
    invariant x <= y && (forall j: int :: x < j && j < y ==> f(j) != K);
  {
    x := x-1;
    y := y+1;
  }

  if (f(x) == K) {
    k := x;
  } else {
    k := y;
  }
}
 
// deterministic, structured, iterative version with breaks
implementation Find(a: int, b: int) returns (k: int)
{
  var x: int, y: int;

  x := a;
  y := b;

  while (true)
    invariant x <= y && (forall j: int :: x < j && j < y ==> f(j) != K);
  {
    if (f(x) == K) {
      k := x;
      break;
    } else if (f(y) == K) {
      k := y;
      break;
    }
    x := x-1;
    y := y+1;
  }
}
 
// deterministic, somewhat structured, iterative version
implementation Find(a: int, b: int) returns (k: int)
{
  var x: int, y: int;

  x := a;
  y := b;

  while (true)
    invariant x <= y && (forall j: int :: x < j && j < y ==> f(j) != K);
  {
    if (f(x) == K) {
      goto FoundX;
    } else if (f(y) == K) {
      goto FoundY;
    }
    x := x-1;
    y := y+1;
  }

  FoundX:
  k := x;
  return;

  FoundY:
  k := y;
  return;
}
 
// deterministic, structured, iterative version with breaks
implementation Find(a: int, b: int) returns (k: int)
{
  var x: int, y: int;

  x := a;
  y := b;

  outer:
  if (true) {
    inner:
    while (true)
      invariant x <= y && (forall j: int :: x < j && j < y ==> f(j) != K);
    {
      if (f(x) == K) {
        break inner;
      } else if (f(y) == K) {
        break outer;
      }
      x := x-1;
      y := y+1;
    }

    k := x;
    return;
  }
  k := y;
}

// ----- free invariant -----

function Teal(int) returns (bool);
function ShadeOfGreen(int) returns (bool);
axiom (forall w: int :: Teal(w) ==> ShadeOfGreen(w));

procedure P(x: int) returns (y: int)
  requires Teal(x);
  ensures ShadeOfGreen(y);
{
  y := x;
  while (y < 100)
    free invariant Teal(y);
  {
    y := y + 5;
  }
}

// ----- run off the end of the BigBlock -----

procedure RunOffEnd0() returns (x: int)
  ensures x == 3;
{
  x := 0;
  Label0:
  x := x + 1;
  Label1:
  x := x + 1;
  Label2:
  Label3:
  Label4:
  x := x + 1;
}

procedure RunOffEnd1() returns (x: int)
  ensures x == 4;
{
  x := 0;
  Label0:
  x := x + 1;
  Label1:
  if (*) {
    Label2:
    x := x + 2;
  } else if (*) {
    Label3:
    x := 2;
    x := x + 2;
    Label4:
    Label5:
    x := x - 1;
  } else {
    if (*) {
      x := 0;
      while (x < 3)
        invariant x <= 3;
      { x := x + 1; }
    } else {
      x := x + 2;
    }
  }
  x := x + 1;
}

procedure RunOffEnd2() returns (x: int)
  ensures x == 10;
{
  while (true) {
    while (true) {
      if (*) {
        x := 10;
        break;
      }
    }
    if (*) { break; }
  }
}

procedure RunOffEnd3() returns (x: int)
  ensures x == 9;
{ x := 9;
  while (true) {
    while (true) {
      if (*) {
        x := 10;
        break;
      }
    }
    if (*) { break; }
  }  // error: violated postcondition
}

procedure RunOffEnd4() returns (x: int)
{
  var y: int;
  var bad: bool;

  while (true) {
    y := x;
    bad := false;
    if (*) {
      x := x + 1;
      bad := true;
    }
    if (x == y) { break; }
  }
  assert !bad;
}

procedure RunOffEnd5() returns (x: int)
{
  while (true) {
    if (x == 5) { }
  }
  assert false;
}

procedure RunOffEnd6() returns (x: int)
{
  x := 7;
  while (true)
    invariant x == 7;
  {
    x := 5;
    MyLabel:
    x := 7;
  }
}

// ----- jump optimizations -----

procedure Q0()
{
  var x: int;

  x := 0;
  if (*) {
    x := 1;
  }
  assert x == 1;  // error
}

procedure Q1() returns (x: int)
{
  if (x == 0) {
    A:
      x := x + 0;
      assert x == 0;  // error
    B:
      x := x + 1;
      goto A;
  }
}

procedure Q2() returns (x: int)
{
  if (x == 0) {
    while (x < 10)
      invariant x <= 10;
    {
      x := x + 1;
    }
  }
}

// There was once a bug in Boogie's handling of the following break statement.
procedure BreakIssue(x: int) returns (curr: int)
  ensures x == 18 || curr == 100;  // holds, because the procedure doesn't
                                   // actually ever terminate if x != 18
{
  while (x != 18) { 
    while (x != 19) {
      call curr := Read();
      if (curr == 0) {
        break;
      }
    }
  }
}

procedure Read() returns (val: int);
