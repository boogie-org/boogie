// RUN: %boogie -noinfer -contractInfer -printAssignment -abstractHoudini:IA[ConstantProp] "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Example to test candidate annotations on loops

function {:existential true} Assert(): bool;
function {:existential true} b1():bool;
function {:existential true} b2():bool;
function {:existential true} b3():bool;
function {:existential true} b4():bool;
function {:existential true} b5():bool;
function {:existential true} b6():bool;
function {:existential true} b7():bool;

var x: int;
var y: int;


procedure foo() 
modifies x;
modifies y;
ensures (b4() || x == 0);
ensures (b5() || y == 10);
ensures (b6() || x == 10);
ensures (b7() || y == 11);

{
  x := 10;
  y := 0;

  goto Head;

Head: 

  //loop invariants
 assert (b1() || x < 0);
 assert (b2() || x >= 0);
 assert (b3() || x + y == 10);
 goto Body, Exit;

Body:
  assume x > 0;
  x := x - 1;
  y := y + 1;


  goto Head;

Exit:
  assume !(x > 0);
  return;
}

// expected assigment: Assert -> false, b1->true,b2->false,b3->false,b4->false, b5->false, b6->true,b7->true







