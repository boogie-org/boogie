// RUN: %boogie /prune "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:exclude_dep} f1 (x: int) : int;
function f2(x: int) : int;

function P(x: int, y: int) : bool;
function Q(x: int) : bool;
function R(x: int) : bool;

const unique B: bool;

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
  ensures Q(f1(y));
{
}

procedure I2(x : int) returns (y: int)
  requires R(x);
  ensures Q(f2(y));
{
}
