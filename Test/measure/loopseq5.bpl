// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

procedure one();

implementation one()
{
  var n: int;
  var old_50_31: int;

  /*** structured program:
    n := 10;
    while (n >= 1)
      invariant n >= 0;
      measure n;
    {
        n := n - 1;
    }
  **** end structured program */

  anon0:
    n := 10;
    goto anon2_LoopHead;

  anon2_LoopHead:
    assert n >= 0;
    measure n;
    n := n + 1;
    goto anon2_LoopDone, anon2_LoopBody;


  anon2_LoopBody:
    assume {:partition} n >= 1;
    n := n - 1;
    goto anon2_LoopHead;

  anon2_LoopDone:
    assume {:partition} 1 > n;
    return;
}


