// RUN: %parallel-boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test that trigger legality checks consider inline function bodies

function Q(int): bool;

// --- Illegal trigger: inline function with body containing boolean operators ---

function {:inline} IllegalInline(x: int): bool {
  0 <= x && x < 100
}

procedure P1() {
  assume (forall z: int :: {IllegalInline(z)} IllegalInline(z) ==> Q(z));
  assert Q(28);
}

// --- Legal trigger: inline function with legal body ---

function {:inline} LegalInline(x: int): int {
  x + 1
}

procedure P2() {
  // This should be allowed: the body of LegalInline is a legal trigger expression
  assume (forall z: int :: {LegalInline(z)} LegalInline(z) > 0 ==> Q(z));
  assert Q(28);
}

// --- Illegal trigger: nested inline functions with illegal body ---

function {:inline} OuterInline(x: int): bool {
  InnerInline(x)
}

function {:inline} InnerInline(x: int): bool {
  x > 0 && x < 100
}

procedure P3() {
  assume (forall z: int :: {OuterInline(z)} OuterInline(z) ==> Q(z));
  assert Q(28);
}

// --- Illegal trigger: inline function with equality in body ---

function {:inline} HasEquality(x: int): bool {
  x == 5
}

procedure P4() {
  assume (forall z: int :: {HasEquality(z)} HasEquality(z) ==> Q(z));
  assert Q(28);
}
