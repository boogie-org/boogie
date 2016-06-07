// RUN: %boogie -noinfer -contractInfer -printAssignment "%s" | %OutputCheck -d "%s"
// Example to test candidate annotations on loops

// CHECK-L: Assignment computed by Houdini:
// CHECK-NEXT-L: b1 = False
const {:existential true} b1:bool;
// CHECK-NEXT-L: b2 = True
const {:existential true} b2:bool;
// CHECK-NEXT-L: b3 = True
const {:existential true} b3:bool;
// CHECK-NEXT-L: b4 = True
const {:existential true} b4:bool;
// CHECK-NEXT-L: b5 = True
const {:existential true} b5:bool;
// CHECK-NEXT-L: b6 = False
const {:existential true} b6:bool;
// CHECK-NEXT-L: b7 = False
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

// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors
