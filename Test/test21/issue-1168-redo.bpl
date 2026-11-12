// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /proverOpt:O:smt.mbqi.max_iterations=10 /typeEncoding:a "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /proverOpt:O:smt.mbqi.max_iterations=10 /typeEncoding:p "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %parallel-boogie /proverOpt:O:smt.mbqi=true /proverOpt:O:smt.mbqi.max_iterations=10 /typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Issue #1168, continued (see issue-1168.bpl).  The last two axioms below are
// quantifiers whose int (bool) variable occurs in the trigger only under a cast,
// Box(intType, int_2_U(n)).  The arguments encoding used to redo such a
// quantifier with the variable retyped to U, so that the trigger matches boxed
// values that are not casts; the redone body is then stated for every value of U,
// not only the ints (bools), and only the reverse casts made the two readings
// agree.  So dropping the reverse casts is not enough: with the retyping kept,
// the bool axiom says that every value boxed at bool is a bool, and with
// Unbox(Box(x)) == x that bounds U to two elements again.  Every axiom here is
// true in Boogie's semantics, and no encoding may prove "assert false".

type Box;
function Box<T>(x: T): Box;
function Unbox<T>(b: Box): T;
axiom (forall<T> x: T :: { Box(x) } Unbox(Box(x)): T == x);

function IdI(n: int): int;
axiom (forall n: int :: { IdI(n) } IdI(n) == n);
function IdB(b: bool): bool;
axiom (forall b: bool :: { IdB(b) } IdB(b) == b);

axiom (forall n: int :: { Box(n) } Box(n) == Box(IdI(n)));
axiom (forall b: bool :: { Box(b) } Box(b) == Box(IdB(b)));

procedure P(n: int)
{
  assert Unbox(Box(n)): int == n;
  assert false;  // not provable
}
