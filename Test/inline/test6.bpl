// RUN: %boogie -inline:spec -print:- -env:0 -printInlined -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:inline 2} foo()
  modifies x;
{
  x := x + 1;
  call foo();
}

procedure {:inline 2} foo1()
  modifies x;
{
  x := x + 1;
  call foo2();
}

procedure {:inline 2} foo2()
  modifies x;
{
  x := x + 1;
  call foo3();
}

procedure {:inline 2} foo3()
  modifies x;
{
  x := x + 1;
  call foo1();
}

var x:int;

procedure  bar()
  modifies x;
{
  call foo();
  call foo1();
}

