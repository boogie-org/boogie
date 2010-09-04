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
    goto anon3_LoopHead;

  anon3_LoopDone:
    assume g >= x;
    goto anon2;

  anon2:
    assert x == 1;
    return;
}


