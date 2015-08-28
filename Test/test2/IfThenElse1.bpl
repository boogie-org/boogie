// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type t1;

procedure ok()
{
  var b:bool, x:int, y:int;

  assert x == if b then x else x;
  assert x == if true then x else y;
}

procedure ok2()
{
  var x:int, y:int;
  var a:t1, b:t1, c:t1;

  c := if x > y then a else b;
  assert c == a || c == b;
  assume x > y;
  assert c == a;
}

procedure fail1()
{
  var b:bool, x:int, y:int;

  assert x == if b then x else y;
}

procedure fail2()
{
  var b:bool, x:int, y:int;

  assert x == if false then x else y;
}
