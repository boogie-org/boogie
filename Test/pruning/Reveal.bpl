// RUN: %parallel-boogie /prune:1 /errorTrace:0 /printPruned:"%t" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f1 <T> (x: T) : int uses {
  axiom (forall <T> x: T :: {f1(x)} f1(x) == 42);
}

// Both f1 and the axiom will be monomorphized into bool and int instances.
// Automatic edge inference would already ensure that only the monomorphized instances
// are incoming, however we want to test here how the new uses clauses are determined.
//
// After instantiation, each instance of f1 for some T should *only* have 
// the T-instantiated axiom as outgoing. 

procedure caller()
{
  call callee();
}


procedure callee()
  ensures f1(true) == 42;
  ensures f1(3) == 42;
{
}