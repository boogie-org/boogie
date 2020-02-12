// RUN: %boogie -typeEncoding:n -logPrefix:0n "%s" > "%t"
// RUN: %diff "%s.n.expect" "%t"
// RUN: %boogie -typeEncoding:p -logPrefix:0p "%s" > "%t"
// RUN: %diff "%s.p.expect" "%t"
// RUN: %boogie -typeEncoding:a -logPrefix:0a "%s" > "%t"
// RUN: %diff "%s.a.expect" "%t"

procedure P() returns () {

 assume (forall<t> m : [t]bool ::                // uses "infinitely many" map types
         (forall x : t ::    m[x] == false));

}


procedure Q() returns () {
 var h : [int] bool;

 assume (forall<t> m : [t]bool, x : t ::    m[x] == false);
 assert !h[42];
 assert false;                    // should really be provable
}



procedure R() returns () {
 var h : [int] bool;

 assume (forall<t> m : [t]bool, x : t ::    m[x] == false);
 assert !h[42];
 assert !h[42 := true][42];
 assert false;                    // wow
}
