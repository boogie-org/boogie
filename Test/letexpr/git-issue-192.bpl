// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type AAA;
type BBB;
type CCC;

function Apple(AAA, BBB): CCC;
function Banana(int): BBB;

procedure Proc()
{
  var m: [AAA]CCC;
  m :=
      // Once upon a time, the lambda lifting for the following body switched
      // the roles of 15 and Banana(700), by traversing the components of let
      // expressions in a different order when figuring out holes from when
      // replacing the holes with new bound variables of the lambda lifting.
      (lambda aaa: AAA :: 
          (var g := 15;
             Apple(aaa, Banana(700))
          )
      );
}
