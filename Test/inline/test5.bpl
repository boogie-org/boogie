// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// test a case, where the inlined proc comes before the caller

procedure {:inline 2} foo()
  modifies x;
{
  x := x + 1;
}

var x:int;

procedure  bar()
  modifies x;
{
  x := 3;
  call foo();
  assert x == 4;
  call foo();
  assert x == 5;
}

// -------------------------------------------------

var Mem : [int]int;

procedure {:inline 1} P(x:int)
  modifies Mem;
{
  Mem[x] := 1;
}

procedure mainA()
  modifies Mem;
{
  Mem[1] := 0;
  call P(0);
  call P(1);
  assert Mem[1] == 0;  // error
}

procedure mainB()
  modifies Mem;
{
  Mem[1] := 0;
  call P(0);
  call P(1);
  assert Mem[1] == 1;  // good
}

procedure mainC()
  modifies Mem;
{
  Mem[1] := 0;
  call P(0);
  call P(1);
  assert Mem[1] == 1;  // good
}

// -------------------------------------------------

type ref;
var xyz: ref;

procedure xyzA();
  modifies xyz;
  ensures old(xyz) == xyz;

procedure {:inline 1} xyzB()
  modifies xyz;
{
  call xyzA();
}

procedure xyzMain()
  modifies xyz;
{
  call xyzA();
  assert old(xyz) == xyz;
  call xyzB();
}
