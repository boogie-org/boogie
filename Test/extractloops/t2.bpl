// RUN: %boogie -stratifiedInline:1 -extractLoops -removeEmptyBlocks:0 -coalesceBlocks:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: int;


procedure foo()
{
  var t: int;
  t := 0;
}

procedure {:entrypoint} A()
modifies g;
{
  var x: int;
  var y: int;

  anon0:
    assume g == 0;
    x := 4;
    goto anon3_LoopHead;

  anon3_LoopHead:
    call foo();
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume g < x;
    g := g + 1;
    x := x - 1;
    y := 0;
    goto lab1_LoopHead;

  lab1_LoopHead:
    goto lab1_LoopBody, lab1_LoopDone;

  lab1_LoopBody:
    assume y < 2;
    y := y + 1;
    goto lab1_LoopHead;
    
  lab1_LoopDone:
    assume y >= 2;
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume g >= x;
    goto anon2;

  anon2:
    return;
}


