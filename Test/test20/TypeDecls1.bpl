// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// set of maps from anything to a specific type a
const mapSet : <a>[<b>[b]a]bool;

const emptySet : <a>[a]bool;

axiom mapSet[5];                            // type error

axiom mapSet[emptySet] == true;

axiom mapSet[emptySet := false] != mapSet;

axiom mapSet[emptySet := 5] == mapSet;      // type error

axiom emptySet[13 := true][13] == true;

axiom (forall f : <c>[c]int, x : ref :: mapSet[f] ==> f[x] >= 0);

axiom (forall f : <c>[c]c :: mapSet[f]);    // type error

axiom mapSet[mapSet] == true;               // type error

type ref;
