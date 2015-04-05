// Z3 4.1: /trace /z3opt:MBQI=true /proverOpt:OPTIMIZE_FOR_BV=true /z3opt:RELEVANCY=0
function {:inline} xor(a: bool, b: bool) returns (bool)  { (!a && b) || (a && !b) }

procedure Incorrect_A(
    {:visible} a: bool, {:hidden} b: bool)
returns ({:visible} ap: bool, {:hidden} bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   ap := a;
   bp := b;
}

procedure Incorrect_B(
    {:hidden} a: bool, {:visible} b: bool)
returns ({:hidden} ap: bool, {:visible} bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   ap := a;
   bp := b;
}

procedure Incorrect_X(
    {:hidden} a: bool, {:hidden} b: bool)
returns ({:hidden} ap: bool, {:hidden} bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   ap := a;
   bp := b;
}

procedure Correct_A(
    {:visible} a: bool, {:hidden} b: bool)
returns ({:visible} ap: bool, {:hidden} bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   havoc ap;
   bp := xor(xor(ap, a), b);
}

procedure Correct_B(
    {:hidden} a: bool, {:visible} b: bool)
returns ({:hidden} ap: bool, {:visible} bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   havoc ap;
   bp := xor(xor(ap, a), b);
}

procedure Correct_X(
    {:hidden} a: bool, {:hidden} b: bool)
returns ({:hidden} ap: bool, {:hidden} bp: bool)
  ensures xor(ap, bp) == xor(a, b);
{
   havoc ap;
   bp := xor(xor(ap, a), b);
}

