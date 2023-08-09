// RUN: %parallel-boogie /prune /trace /errorTrace:0 "%s" > "%t"
// RUN: %OutputCheck "%s" --file-to-check="%t"

// Related PR #767.

function f1 (x: int) : int;
function f2 (x: int) : int uses
{
  axiom f1(0) == 1 && f2(0) == 2;
}

// Above axiom will be split into two during monomorphization into
// axiom f1(0) == 1 and axiom f2(0) == 2.
// Current implementation ensures that f1(0) == 1 is kept as a dependency
// of f1, and f2(0) is moved to be a dependency of f2. If there would be
// other symbols in the axiom, the new split axioms would be added to those
// if they contained those symbols.

procedure nonMonomorphicSplitPass()
  ensures f1(0) == 1 && f2(0) == 2;
{
}
// CHECK-L: 1 proof obligation]  verified

function f3 (x: int) : int;
function f4 (x: int) : int;

axiom f3(0) == 1 && f4(0) == 2;

// This one is expected to fail. We do not want to preserve axioms not inside
// uses clauses automatically, as this weakens pruning.

procedure nonMonomorphicSplitFail()
  ensures f3(0) == 1 && f4(0) == 2;
{
}
// CHECK-L: 1 proof obligation]  error
