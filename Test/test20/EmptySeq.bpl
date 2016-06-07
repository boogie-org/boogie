// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type Seq T;

function Seq#Length<T>(Seq T) returns (int);
function Seq#Empty<T>() returns (Seq T);

axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
