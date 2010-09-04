var g: int;

procedure A();
  requires g == 0;
  modifies g;

procedure {:inline 1} {:verify false} foo(); 

implementation foo() {
  var t: int;
  t := 0;
}

implementation A()
{
  var x: int;
  var y: int;

  anon0:
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
    assert false;
    assert x == 1;
    return;
}


