implementation Ex() returns (y: int)
{
  var x: int;
  var x#AT#0: int;
  var y#AT#0: int;
  var x#AT#1: int;
  var y#AT#1: int;
  var y#AT#2: int;


  PreconditionGeneratedEntry:
    goto anon0;

  anon0:
    assume 5 + 0 == 5;
    assume 5 * 5 <= 25;
    goto anon5_LoopHead;

  anon5_LoopHead:
    assume x#AT#0 + y#AT#0 == 5;
    assume x#AT#0 * x#AT#0 <= 25;
    goto anon5_LoopBody;

  anon5_LoopBody:
    assume {:partition} x#AT#0 > 0;
    assume x#AT#1 == x#AT#0 - 1;
    assume (x#AT#1 + y#AT#0) * (x#AT#1 + y#AT#0) > 25;
    assume y#AT#1 == y#AT#0 + 1;
    goto anon6_Then;

  anon6_Then:
    assume {:partition} x#AT#1 < 3;
    assume 2 < 2;
    assert {:split_here} y#AT#1 * y#AT#1 > 4;
    goto ;
}


