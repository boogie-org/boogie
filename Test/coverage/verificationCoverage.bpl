// RUN: %boogie "%s" > "%t.plain"
// RUN: %diff "%s.expect.plain" "%t.plain"
// RUN: %boogie -printVerificationCoverage "%s" > "%t.coverage"
// RUN: %diff "%s.expect.coverage" "%t.coverage"

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
  call {:id "call1"} x := testEnsuresCallee(n+1); // covered
  call {:id "call2"} y := testEnsuresCallee(n+1); // covered
  r := x + y; // covered
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
  call {:id "call_cont"} r := contradictoryEnsuresClause(x);
  r := {:id "unreachable_assignment"} r - 1; // not covered
}
