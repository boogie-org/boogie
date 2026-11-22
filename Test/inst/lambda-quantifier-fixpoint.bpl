// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function P(int, int, int): bool;

procedure NestedLambdaCreatesQuantifier()
{
  var rows: [int][int]bool;

  rows := (lambda {:pool "FixpointOuter"} x: int ::
    (lambda {:pool "FixpointInner"} y: int ::
      (forall {:pool "FixpointQuantifier"} z: int :: P(x, y, z))));
  assert {:add_to_pool "FixpointOuter", 0}
         {:add_to_pool "FixpointInner", 1}
         {:add_to_pool "FixpointQuantifier", 2}
    rows[0][1] ==> P(0, 1, 2);
}
