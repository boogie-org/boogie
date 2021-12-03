 // RUN: %parallel-boogie /prune /errorTrace:0 "%s" > "%t"
 // RUN: %diff "%s.expect" "%t"

function f1 (x: int) : bool;

axiom (forall x: int :: {f1(x)} f1(x));

procedure oneTriggerOneRef(x : int)
  ensures f1(x);
{
}

function f2 (x: int) : bool;
function f3 (x: bool) : bool;
axiom (forall x: int :: {f3(f2(x))} f2(x));

procedure oneTriggerTwoRefsSuccess(x : int)
  requires f3(f2(x));
  ensures f2(x);
{
  assert f3(f2(x));
}

procedure oneTriggerTwoRefsFail(x : int)
  ensures f2(x);
{
}

function f4 (x: int) : bool;
function f5 (x: bool) : bool;
axiom (forall x: int :: {f5(f4(x)), f4(x)} f4(x));
procedure twoTriggers(x : int)
  ensures f4(x);
{
}