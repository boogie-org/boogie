// RUN: %parallel-boogie /prune /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f1 (x: int) : int;
function {:include_dep} f2(x: int) : int;

function P(x: int, y: int) : bool; // should not show up in the smt2 file
function Q(x: int) : bool;
function R(x: int) : bool;

const A: bool;
const B: bool;

axiom false; // this is always pruned away

axiom (forall x: int :: Q(f1(x)));

procedure I1(x : int) returns (y: int)
  requires R(x);
  ensures Q(f1(x)); // this post-condition doesn't prove because f1 is attributed as exclude_dep and
                    // is thus removed from the outgoing set of I1.
                    // This makes the axiom on line 16 unreachable from I1, which is thus pruned away.
{
}

axiom {:include_dep} (forall x: int :: Q(f2(x)));

procedure I2(x : int) returns (y: int)
  requires R(x);
  ensures Q(f2(x)); // proved using the axiom on line 16
{
}


axiom {:include_dep} (forall x: int :: A);

function Def1(x: int) : bool
{
  A
}

axiom {:include_dep} (forall x: int ::
  {f1(x)}
  B);

function Def2(x: int) : bool
{
  B
}

procedure I3(x : int) returns (y: int)
  requires R(x);
  ensures Def1(x); // the axiom about A kicks in because it has no triggers and its body is used to determine incoming edges.
  ensures Def2(x); // fails because the axiom about B is pruned away.
{
}
