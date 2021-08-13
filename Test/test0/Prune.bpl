// RUN: %boogie /pruneFunctionsAndAxioms "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:exclude_dep} f1 (x: int) : int;
function f2(x: int) : int;

function P(x: int, y: int) : bool;
function Q(x: int) : bool;
function R(x: int) : bool;

const unique B: bool;
const unique C: bool;

axiom B;

axiom (forall x: int ::
  {f1(x)}
  {f2(x)}
  f1(x) == 5 || f2(x) == 7 <==> B);

axiom false; // this is always pruned away

axiom (forall x: int ::
  {f1(x)}
  {f2(x), R(x)}
  false);

procedure I1(x : int) returns (y: int)
  requires R(x);
  ensures Q(f1(y)); // this doesn't prove because f1 (attributed as exclude_dep) is removed from the outgoing set of I1
                    // so the axiom with {f1} and {f2, R} as triggers is pruned away.
{
}

procedure I2(x : int) returns (y: int)
  requires R(x);
  ensures Q(f2(y)) && B;
{
}
