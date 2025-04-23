// RUN: %boogie "%s" > "%t.plain"
// RUN: %diff "%s.expect" "%t.plain"
// RUN: %boogie -trackVerificationCoverage -trace "%s" > "%t.coverage"
// RUN: %OutputCheck "%s" --file-to-check="%t.coverage"
// CHECK: Proof dependencies:
// CHECK:   a0
// CHECK:   assert_a0
// CHECK:   assert_r0
// CHECK:   r0
// CHECK: Proof dependencies:
// CHECK:   invariant sinv_not_1 established
// CHECK:   invariant sinv_not_1 maintained
// CHECK:   invariant sinv1 assumed in body
// CHECK:   invariant sinv1 established
// CHECK:   invariant sinv1 maintained
// CHECK:   invariant sinv2 assumed in body
// CHECK:   invariant sinv2 established
// CHECK:   invariant sinv2 maintained
// CHECK:   spost
// CHECK:   spre1
// CHECK: Proof dependencies:
// CHECK:   cont_assume_1
// CHECK:   cont_assume_2
// CHECK: Proof dependencies:
// CHECK:   false_req
// CHECK: Proof dependencies:
// CHECK:   cont_req_1
// CHECK:   cont_req_2
// CHECK: Proof dependencies:
// CHECK:   assumeFalse
// CHECK: Proof dependencies:
// CHECK:   tee0
// CHECK:   tee1
// CHECK:   ter0
// CHECK: Proof dependencies:
// CHECK:   call2_tee1
// CHECK:   ensures clause tee0 from call call1
// CHECK:   ensures clause tee0 from call call2
// CHECK:   ensures clause tee1 from call call2
// CHECK:   requires clause ter0 proved for call call1
// CHECK:   requires clause ter0 proved for call call2
// CHECK:   tee_not_1
// CHECK:   ter1
// CHECK:   xy_sum
// CHECK: Proof dependencies:
// CHECK:   a_gt_10
// CHECK:   constrained
// CHECK:   x_gt_10
// CHECK: Proof dependencies:
// CHECK:   ensures clause cont_ens_abs from call call_cont
// CHECK:   requires clause xpos_abs proved for call call_cont
// CHECK:   xpos_caller
// CHECK: Proof dependencies:
// CHECK:   someInteger_value_axiom
// CHECK: Proof dependencies of whole program:
// CHECK:   a_gt_10
// CHECK:   a0
// CHECK:   assert_a0
// CHECK:   assert_r0
// CHECK:   assumeFalse
// CHECK:   call2_tee1
// CHECK:   constrained
// CHECK:   cont_assume_1
// CHECK:   cont_assume_2
// CHECK:   cont_req_1
// CHECK:   cont_req_2
// CHECK:   ensures clause cont_ens_abs from call call_cont
// CHECK:   ensures clause tee0 from call call1
// CHECK:   ensures clause tee0 from call call2
// CHECK:   ensures clause tee1 from call call2
// CHECK:   false_req
// CHECK:   invariant sinv_not_1 established
// CHECK:   invariant sinv_not_1 maintained
// CHECK:   invariant sinv1 assumed in body
// CHECK:   invariant sinv1 established
// CHECK:   invariant sinv1 maintained
// CHECK:   invariant sinv2 assumed in body
// CHECK:   invariant sinv2 established
// CHECK:   invariant sinv2 maintained
// CHECK:   r0
// CHECK:   requires clause ter0 proved for call call1
// CHECK:   requires clause ter0 proved for call call2
// CHECK:   requires clause xpos_abs proved for call call_cont
// CHECK:   someInteger_value_axiom
// CHECK:   spost
// CHECK:   spre1
// CHECK:   tee_not_1
// CHECK:   tee0
// CHECK:   tee1
// CHECK:   ter0
// CHECK:   ter1
// CHECK:   x_gt_10
// CHECK:   xpos_caller
// CHECK:   xy_sum
// RUN: %boogie -trackVerificationCoverage "%s" > "%t.coverage"
// RUN: %diff "%s.expect" "%t.coverage"
// RUN: %boogie -trackVerificationCoverage -typeEncoding:a -prune:1 "%s" > "%t.coverage-a"
// RUN: %diff "%s.expect" "%t.coverage-a"
// RUN: %boogie -trackVerificationCoverage -typeEncoding:p -prune:1 "%s" > "%t.coverage-p"
// RUN: %diff "%s.expect" "%t.coverage-p"
// RUN: %boogie -trackVerificationCoverage -normalizeDeclarationOrder:1 -prune:1 "%s" > "%t.coverage-d"
// RUN: %diff "%s.expect" "%t.coverage-d"
// RUN: %boogie -trackVerificationCoverage -warnVacuousProofs -trace -normalizeNames:1 -prune:1 "%s" | grep -v "solver resource count" | grep -v "batch mode" > "%t.coverage-n"
// RUN: %diff "%s.expect-trace" "%t.coverage-n"

procedure testRequiresAssign(n: int)
  requires {:id "r0"} n > 0; // covered
  requires {:id "r_not_1"} n < 10; // not covered
{
    var x: int;
    x := {:id "a0"} n + 1; // covered
    assert {:id "assert_a0"} x == n + 1; // covered
    x := {:id "a_not_1"} 0; // not covered
    assert {:id "assert_r0"} n > 0; // covered
}

procedure sum(n: int) returns (s: int)
  requires {:id "spre1"} n >= 0; // covered
  ensures {:id "spost"} s == (n * (n + 1)) div 2; // covered
{
  var i: int;
  var foo: int;

  i := 0;
  s := 0;
  foo := 27;
  while (i < n)
    invariant {:id "sinv1"} 0 <= i && i <= n; // covered: established, maintained, assumed
    invariant {:id "sinv2"} s == (i * (i + 1)) div 2; // covered: established, maintained, assumed
    invariant {:id "sinv_not_1"} n >= 0; // covered: established, maintained, NOT assumed
  {
    i := i + 1;
    s := s + i;
    foo := {:id "update_foo"} foo * 2; // not covered
  }
}

procedure contradictoryAssume(n: int)
{
    assume {:id "cont_assume_1"} n > 0; // covered
    assume {:id "cont_assume_2"} n < 0; // covered
    assume {:id "unreach_assume_1"} n == 5; // not covered
    assert {:id "unreach_assert_1"} n < 10; // not covered
}

// NB: an explicit `requires false` leads to _nothing_ being covered
procedure falseRequires(n: int)
  requires {:id "false_req"} n != n; // covered
{
    assert {:id "false_assert"} false; // not covered
}

procedure contradictoryRequires(n: int)
  requires {:id "cont_req_1"} n > 0; // covered
  requires {:id "cont_req_2"} n < 0; // covered
{
    assume {:id "n_eq_5"} n == 5; // not covered
    assert {:id "n_lt_10"} n > 10; // not covered
}

procedure assumeFalse() {
  assume {:id "assumeFalse"} false; // covered
  assert {:id "assertSimple"} 1 + 1 == 2; // not covered
}

procedure testEnsuresCallee(n: int) returns (r: int)
  requires {:id "ter0"} n > 0; // covered
  ensures {:id "tee0"} r > n; // covered by this procedure and caller
  ensures {:id "tee1"} r > 0; // covered when proving this procedure, not from caller
{
  r := n + 1;
}

procedure testEnsuresCaller(n: int) returns (r: int)
  requires {:id "ter1"} n > 0; // covered
  ensures {:id "tee_not_1"} r > n; // covered
{
  var x: int;
  var y: int;
  call {:id "call1"} x := testEnsuresCallee(n+1); // requires and ensures covered
  call {:id "call2"} y := testEnsuresCallee(n+1); // requires and ensures covered
  assert {:id "call2_tee1"} y > 0;
  r := {:id "xy_sum"} x + y; // covered
}

procedure obviouslyUnconstrainedCode(x: int) returns (a: int, b: int)
  requires {:id "x_gt_10"} x > 10; // covered
  requires {:id "x_lt_100"} x < 100; // not covered
  ensures {:id "a_gt_10"} a > 10; // covered
{
  a := {:id "constrained"} x + 1;     // covered: constrained by ensures clause
  b := {:id "not_constrained"} x - 1; // not covered: not constrained by ensures clause
}


procedure contradictoryEnsuresClause(x: int) returns (r: int);
  requires {:id "xpos_abs"} x > 1; // covered (established by caller)
  ensures  {:id "cont_ens_abs"} r > x && r < 0; // covered (used by caller proof)

// Call function that has contradictory ensures clauses.
procedure callContradictoryFunction(x: int) returns (r: int)
  requires {:id "xpos_caller"} x > 1; // covered
  ensures {:id "caller_ensures"} r < 0; // not covered
{
  call {:id "call_cont"} r := contradictoryEnsuresClause(x); // requires and ensures covered
  r := {:id "unreachable_assignment"} r - 1; // not covered
}

function someInteger(i: int) : int uses {
  axiom {:id "someInteger_value_axiom"} (forall i: int :: someInteger(i) == 3);

  axiom {:id "uselessAxiom"} (3 == 3);
}

procedure usesSomeInteger() returns (r: bool)
  ensures r;
{
  r := someInteger(7) == 3;
}
