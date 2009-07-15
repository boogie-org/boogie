

type Wicket;

const unique r: Wicket;
const unique s, t: Wicket extends unique r;

procedure P() returns () {
  assert (forall x:Wicket, y:Wicket :: x <: s && y <: t ==> x != y);
  assert false;          // unprovable
}