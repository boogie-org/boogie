// RUN: %parallel-boogie /prune /printPruned:"%tpruned" /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const unique four: int;
const unique ProducerConst: bool uses {
    axiom four == 4;
}

function ConsumerFunc(x: int): int;

function ProducerFunc(x: int): bool uses {
    axiom (forall x: int :: ConsumerFunc(x) == 3);
}

procedure hasAxioms()
  requires ProducerFunc(2);
  requires ProducerConst;
  ensures ConsumerFunc(4) == 3;
  ensures four == 4;
{
  
}

procedure doesNotHaveAxioms() 
  ensures ConsumerFunc(4) == 3; // The ConsumerFunc axiom is pruned away, so this fails to verify
  ensures four == 4; // The ProducerConstant axiom is pruned away, so this fails to verify 
{
  
}