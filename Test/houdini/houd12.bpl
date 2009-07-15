// Example to test candidate annotations on loops

const {:existential true} b1:bool;
const {:existential true} b2:bool;
const {:existential true} b3:bool;
const {:existential true} b4:bool;
const {:existential true} b5:bool;
const {:existential true} b6:bool;
const {:existential true} b7:bool;

var x: int;
var y: int;


procedure foo() 
modifies x;
modifies y;
ensures (b4 ==> x == 0);
ensures (b5 ==> y == 10);
ensures (b6 ==> x == 10);
ensures (b7 ==> y == 11);

{
  x := 10;
  y := 0;

  goto Head;

Head: 

  //loop invariants
 assert (b1 ==> x < 0);
 assert (b2 ==> x >= 0);
 assert (b3 ==> x + y == 10);
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

// expected outcome: Correct
// expected assigment: b1->False,b2->True,b3->True,b4->True, b5->True, b6->False,b7->False







