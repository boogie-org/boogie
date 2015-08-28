// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var x: int;
var y: int;

procedure P()
  modifies x;
  ensures x == old(x) + 1;
{
  start:
    x := 1 + x;
    return;
}

procedure Q();
  modifies x;
  ensures x == old(x) + 1;

implementation Q()
{
  start:
    x := 1 + x;
    return;
}

procedure R()
  modifies x;
  ensures x == old(x) + 1;
{
  start:
    return;
}  // error: does not establish postcondition

procedure Swap()
  modifies x, y;
  ensures x == old(y) && y == old(x);
{
  var t: int;

  start:
    goto A, B;
  A:
    t := x;
    x := y;
    y := t;
    goto end;
  B:
    x := x - y;       // x == old(x) - old(y)
    y := y + x;       // y == old(y) + (old(x) - old(y)) == old(x)
    x := y - x;       // x == old(x) - (old(x) - old(y)) == old(y)
    goto end;
  end:
    return;
}

procedure OutParam0(x: int) returns (y: int)
  ensures y == x + 1;
{
  start:
    y := x + 1;
    return;
}

// OutParam1 is like OutParam0, except that there's now a separate
// implementation declaration, which means that the specification
// and body use different AST nodes for the formal parameters.  This
// may make a difference in the various substitutions going on.
// (Indeed, a previous bug caused OutParam0 to verify but not OutParam1.)
procedure OutParam1(x: int) returns (y: int);
  ensures y == x + 1;
implementation OutParam1(x: int) returns (y: int)
{
  start:
    y := x + 1;
    return;
}

var a: [ref]int;
var b: [ref]int;

procedure SwapElems(o: ref) returns (p: ref)
  modifies a, b;
  ensures a[o] == old(b[p]) && b[o] == old(a[p]);
{
  var ta: int, tb: int;

  start:
    goto A, B, C;
  A:
    havoc p;
    goto B, C;
  B:
    ta := a[p];
    tb := b[p];
    a[o] := tb;
    b[o] := ta;
    return;
  C:
    assume a[o] == b[o];assume false;

    p := o;
    return;
}



//-------------------------------------------------------------------------
// Test old in Boogie PL code
//-------------------------------------------------------------------------

var Global0: int;

// Good
procedure OldInCode0()
  requires Global0 >= 0;
  ensures Global0 <= old(Global0) + 1;
  modifies Global0;
{
  var local0: int;
 
  start:
    goto A,B;
  A:
    assert Global0 == old(Global0);
    return;

  B:
    local0 := Global0 + 1;
    local0 := local0 - 1;
    Global0 := old(local0 + 1);
    return;
}

type ref;
