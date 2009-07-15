

type Box, C;

function box<a>(a) returns (Box);
function unbox<a>(Box) returns (a);

axiom (forall<a> x:a :: unbox(box(x)) == x);

axiom (forall<a> x:Box :: {unbox(x):a} box(unbox(x):a) == x);

axiom (forall x:Box :: box(unbox(x)) == x);     // warning

procedure P() {
  var b : Box;
  var i : C;

  assert unbox(box(13)) == 13;

  i := unbox(b);
  assert b == box(i);

  assert false;
}