// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:never_pattern true} f1(x:int) returns(int);
function {:never_pattern false} f2(x:int) returns(int);
function f3(x:int) returns(int);


procedure foo()
{
  assume (forall x : int :: f1(x) > 0 && f2(x) > 0 && f3(x) > 0);
  assert f2(3) > 0;
  assert f3(4) > 0;
}

procedure bar()
{
  assume (forall x : int :: f1(x) > 0 && f2(x) > 0 && f3(x) > 0 && f1(7) == 3);
  assert f1(3) > 0;
}

procedure bar1()
{
  assume (forall x : int :: {:nopats f2(x)} f1(x) > 0 && f2(x) > 0 && f3(x) > 0 && f1(7) == 3);
  assert f1(3) > 0;
}

procedure bar2()
{
  assume (forall x : int :: {:nopats f2(x)} f1(x) > 0 && f2(x) > 0 && f3(x) > 0 && f1(7) == 3);
  assert f2(3) > 0;
}

// ----- nested binders -----

function {:never_pattern} P(int): bool;
function F(int, int): int;
function G(int): bool;

procedure NestedBinders()
{
  goto A, B, C, D;
  A:
    assume (forall s: int ::
      // the occurrence of P in the next line had once caused a crash
      (forall x: int :: { F(s, x) } P(F(s, x)))
      ==> G(s));  // this places the nested forall in a negative position
    goto End;

  B:
    assume (forall s: int ::
      // the occurrence of P in the next line had once caused a crash
      (exists x: int :: { F(s, x) } P(F(s, x))));
    goto End;

  C:
    assume (forall s: int, m: [int]bool ::
      // the occurrence of P in the next line had once caused a crash
      (lambda x: int :: P(F(s, x))) == m);
    goto End;

  D:
    assume (forall x0: int ::
             // The following quantifier will get a {:nopats P(x1,s)}, which is good.
             // But that added trigger expression had once caused the outer quantifier
             // to crash.
             (forall x1: int :: P(x1)));
    goto End;

  End:
}
