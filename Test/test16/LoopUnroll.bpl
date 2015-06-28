// RUN: %boogie -loopUnroll:1 -logPrefix:-lu1 LoopUnroll.bpl > "%t1"
// RUN: %diff "%s.1.expect" "%t1"
// RUN: %boogie -loopUnroll:2 -logPrefix:-lu2 -proc:ManyIterations LoopUnroll.bpl > "%t2"
// RUN: %diff "%s.2.expect" "%t2"
// RUN: %boogie -loopUnroll:3 -logPrefix:-lu3 -proc:ManyIterations LoopUnroll.bpl > "%t3"
// RUN: %diff "%s.3.expect" "%t3"
procedure P()
{
  var x: int;

  A:
    x := 0;
    goto B, Goner, C;

  B:
    x := 1;
    goto D;

  C:
    x := 2;
    goto D;
  
  Goner:
    x := 5;
    assume false;
    x := 6;
    goto B;

  D:
    x := 3;
    goto LoopHead;

  LoopHead:
    assert x < 100;
    goto LoopBody, LoopDone;

  LoopBody:
    x := x + 1;
    goto LoopHead, LoopBodyMore;

  LoopBodyMore:
    x := x + 2;
    goto LoopHead;

  LoopDone:
    x := 88;
    return;
}

type MyValue;
const SpecialValue: MyValue;

procedure WrongRange(a: [int]MyValue, N: int)
  requires 0 <= N;
{
  var i: int, v: MyValue;

  i := 1;  // bad idea
  while (i <= N)  // also a bad idea
  {
    assert 0 <= i;  // lower bounds check
    assert i < N;  // error: upper bounds check
    v := a[i];
    i := i + 1;
  }
}

procedure ManyIterations(a: [int]MyValue, N: int)
  requires 0 <= N;
  requires a[0] != SpecialValue && a[1] != SpecialValue;
{
  var i: int, v: MyValue;

  i := 0;
  while (i < N)
  {
    assert 0 <= i;  // lower bounds check
    assert i < N;  // upper bounds check
    v := a[i];
    assert a[i] != SpecialValue;  // error: after more than 2 loop unrollings
    i := i + 1;
  }
}

// ERROR:  /printInstrumented seems to erase filename source-location information
