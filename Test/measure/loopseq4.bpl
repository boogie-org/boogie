// Boogie program verifier version 3.5.6.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: loopseq2.bpl /print:un.bpl /printMeasureDesugaring

var x: int;

procedure one();

implementation one()
{
  var n: int;
  var old_50_31: int;

  anon0:
    n := 10;
    goto anon2_LoopHead;

  anon2_LoopHead:
    measure n;
    measure n + 1;
    goto anon2_LoopDone, anon2_LoopBody;

  anon2_LoopBody:
    assume {:partition} n >= 1;
    n := n - 1;
    goto anon2_LoopHead;

  anon2_LoopDone:
    assume {:partition} 1 > n;
    return;
}


