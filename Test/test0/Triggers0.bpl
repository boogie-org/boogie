// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Trigger errors

function f(int, int) returns (int);
function P(int, int) returns (bool);

// -------------- tests specific to pattern exclusions

axiom (forall x: int ::
       {:nopats f(x,10) }
       { :   nopats   f(x,10) }
       f(x,10) == 3);

axiom (forall x: int ::
       {:nopats f(x,10), f(x,x) }  // error: a pattern exclusion can only mention one expression
       f(x,10) == 3);
