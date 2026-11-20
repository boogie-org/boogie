// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /proverOpt:O:smt.mbqi.max_iterations=10 /typeEncoding:a "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /proverOpt:O:smt.mbqi.max_iterations=10 /typeEncoding:p "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /proverOpt:O:smt.mbqi.max_iterations=10 /typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Issue #1168.  The arguments encoding erases every non-built-in type to one
// sort U, with casts in and out of U for each built-in type.  Beside the left
// inverse U_2_int(int_2_U(n)) == n, which makes U infinite, it used to emit
// reverse casts such as
//   forall x: U :: bool_2_U(U_2_bool(x)) == x
// which say that every value of U is a bool, so that U has at most two
// elements.  Together they have no model, and model-based quantifier
// instantiation found that out: it proved "assert false" below under
// /typeEncoding:a.  No encoding may prove it.  The iteration bound keeps the
// search short: when the solver reaches it, it answers unknown, and the
// assertion is reported as not proved.

type Box;
function Box<T>(x: T): Box;
function Unbox<T>(b: Box): T;
axiom (forall<T> x: T :: { Box(x) } Unbox(Box(x)): T == x);

procedure P(b: bool, n: int)
{
  assert Unbox(Box(b)): bool == b && Unbox(Box(n)): int == n;
  assert false;  // not provable
}
