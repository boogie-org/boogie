// RUN: %boogie "%s" -infer:j > "%t"
// RUN: %diff "%s.expect" "%t"
procedure main()
{
  var x: int, y: int, z: int;

  start:
    x := 2;
    y := 6;
    goto LoopHead;

  LoopHead:
    assert y < 10;  // error: the loop body sets y to an arbitrary value
    goto LoopBody, LoopEnd;

  LoopBody:
    havoc y;
    goto LoopHead;

  LoopEnd:
    return;
}

procedure SimpleWhile5() returns (returnValue: int)
{
  var i: int;

  start:
    returnValue := 1;
    havoc i;
    goto LoopHead;

  LoopHead:
    goto LoopBody, LoopEnd;

  LoopBody:
    // here, we would simply like to "assume 1 <= i", but the interval domain doesn't interpret
    // assume commands, so we start a loop
    i := 1;
    goto IncLoopHead;

  IncLoopHead:
    goto IncI, IncDone;

  IncI:
    i := i + 1;
    goto IncLoopHead;

  IncDone:
    // now we have 1 <= i
    assert 1 <= i;

    returnValue := returnValue * i;
    i := i - 1;
    goto LoopHead;

  LoopEnd:
    assert returnValue >= 1;
    return;
}
