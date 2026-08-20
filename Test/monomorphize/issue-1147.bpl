// RUN: %parallel-boogie /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The execution traces are suppressed because they name inlined monomorphic instances
// (inline$Rec_65$0$...), and that numbering shifts whenever type allocation elsewhere
// changes, which would make the expected output brittle for reasons unrelated to this test.

// Instantiating the body of a recursive polymorphic inlined procedure re-entered
// InstantiateImplementation with the same (implementation, type arguments) pair before
// that pair had been registered, so the guard on implInstantiations never fired and the
// monomorphizer recursed until the stack overflowed and the process aborted. The
// recursion in the source is bounded, but the monomorphizer recurses on the syntactic
// call rather than on the value, so the bound is irrelevant.
//
// Every inlining depth below exceeds the recursion depth of the corresponding call, so
// the base case is reached and the assertions are not discharged vacuously. That matters
// for the error cases: under the default /inline:assume a call still standing at the
// depth bound is replaced by "assume false", which would make the false assertions in
// RecError and MutualError verify instead of reporting an error.

procedure {:inline 3} Rec<T>(x: T, n: int) returns (y: T)
{
  if (n > 0) { call y := Rec(x, n - 1); } else { y := x; }
}

procedure RecInt()
{
  var a: int;
  var b: int;
  a := 3;
  call b := Rec(a, 2);
  assert b == 3;
}

// A second instantiation of the same implementation. The registration is keyed by the
// type arguments, so this one must be built independently of the first.

procedure RecBool()
{
  var p: bool;
  var q: bool;
  p := true;
  call q := Rec(p, 2);
  assert q;
}

// A cycle spanning two implementations rather than a self-call.

procedure {:inline 3} Ping<T>(x: T, n: int) returns (y: T)
{
  if (n > 0) { call y := Pong(x, n - 1); } else { y := x; }
}

procedure {:inline 3} Pong<T>(x: T, n: int) returns (y: T)
{
  if (n > 0) { call y := Ping(x, n - 1); } else { y := x; }
}

procedure Mutual()
{
  var a: int;
  var b: int;
  a := 5;
  call b := Ping(a, 2);
  assert b == 5;
}

// A nested instantiation: while Nest is being instantiated at int, its own body asks for Nest at
// bool. An instantiation under construction is identified by the implementation together with its
// type arguments, so the inner request has to be built rather than mistaken for the outer one; a
// check that looked only at the implementation would drop it.

procedure {:inline 3} Nest<T>(x: T, n: int) returns (y: T)
{
  var c: bool;
  if (n > 0) { call c := Nest(true, 0); call y := Nest(x, n - 1); } else { y := x; }
}

procedure Nested()
{
  var a: int;
  var b: int;
  a := 7;
  call b := Nest(a, 2);
  assert b == 7;
}

// The obligations above are really checked, not vacuously discharged.

procedure RecError()
{
  var a: int;
  var b: int;
  a := 3;
  call b := Rec(a, 2);
  assert b == 4;  // error
}

procedure MutualError()
{
  var a: int;
  var b: int;
  a := 5;
  call b := Ping(a, 2);
  assert b == 6;  // error
}

procedure NestedError()
{
  var a: int;
  var b: int;
  a := 7;
  call b := Nest(a, 2);
  assert b == 8;  // error
}
