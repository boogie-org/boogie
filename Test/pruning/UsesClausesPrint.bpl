// RUN: %parallel-boogie /print:"%t" /errorTrace:0 "%s"
// RUN: %OutputCheck "%s" --file-to-check="%t"
// UNSUPPORTED: batch_mode

const unique four: int;

const unique ProducerConst: bool uses {
    axiom four == 4;
}
// CHECK-L: uses {
// CHECK-L: axiom four == 4
// CHECK-L: }

function ProducerFunc(x: int): bool uses {
    axiom (forall x: int :: ConsumerFunc(x) == 3);
}
// CHECK-L: uses {
// CHECK-L: axiom (forall x: int :: ConsumerFunc(x) == 3)
// CHECK-L: }

procedure hasAxioms()
  requires ProducerFunc(2);
  requires ProducerConst;
  ensures four == 4;
{

}