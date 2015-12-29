// RUN: %boogie -infer:j "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const N: int;
axiom 0 <= N;

procedure P(K: int)
  requires 0 <= K;
{
  var b: bool, x, k: int;

  if (!b) {
    b := !b;
  }
  x := if b then 13 else 10;
  k := K;
  while (k != 0) {
    x := x + k;
    k := k - 1;
  }
  assert 13 <= x;
}

procedure Thresholds0()
{
  var i: int;
  i := 0;
  while (i < 200)
  {
    i := i + 1;
  }
  assert i == 200;
}

procedure Thresholds1()
{
  var i: int;
  i := 0;
  while (i <= 199)
  {
    i := i + 1;
  }
  assert i == 200;
}

procedure Thresholds2()
{
  var i: int;
  i := 100;
  while (0 < i)
  {
    i := i - 1;
  }
  assert i == 0;
}

procedure Thresholds3()
{
  var i: int;
  i := 0;
  while (i < 200)
  {
    i := i + 1;
  }
  assert i == 199;  // error
}

procedure Thresholds4()
{
  var i: int;
  i := 0;
  while (i + 3 < 203)
  {
    i := i + 1;
  }
  assert i * 2 == 400;  // error: this would hold in an execution, but /infer:j is too weak to infer invariant i<=200
}

procedure UnaryNegation0() returns (x: int)  // this was once buggy
{
  x := -1;
  loop_head:
    x := x;
    goto loop_head, after_loop;
  after_loop:
  assert x == -1;
}
procedure UnaryNegation1() returns (x: int)  // this was once buggy
{
  x := -1;
  loop_head:
    x := x;
    goto loop_head, after_loop;
  after_loop:
  assert x == 1;  // error
}

// --------------------------- test {:identity} annotation --------------------

function {:identity} MyId(x: int): int;
function MyStealthyId(x: int): int;  // this one messes up the abstract interpretation
function {:identity false} {:identity}/*the last attribute rules*/ MyPolyId<T>(x: T): T;
function {:identity /*this is a lie*/} MyBogusId(x: int): int { -x }
function {:identity /*ignored, since the function takes more than one argument*/} MultipleArgs(x: int, y: int): int;
function {:identity /*ignored, since the return type is not equal to the argument type*/} BoolToInt(b: bool): int;
function {:identity true/*in some contexts, the type of this function makes sense as an identity*/} SometimesId0<T>(x: T): int;
function {:identity true/*in some contexts, the type of this function makes sense as an identity*/} SometimesId1<T>(x: int): T;
function {:identity true/*in some contexts, the type of this function makes sense as an identity*/} SometimesId2<T,U>(x: T): U;


procedure Id0(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + 1;
  }
  assert 0 <= i;
}

procedure Id1(n: int)
{
  var i: int;
  i := MyId(0);
  while (i < n)
  {
    i := i + MyId(1);
  }
  assert 0 <= i;
}

procedure Id2(n: int)
{
  var i: int;
  i := MyStealthyId(0);
  while (i < n)
  {
    i := i + 1;
  }
  assert 0 <= i;  // error: abstract interpreter does not figure this one out
}

procedure Id3(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + MyStealthyId(1);
  }
  assert 0 <= i;  // error: abstract interpreter does not figure this one out
}

procedure Id4(n: int)
{
  var i: int;
  i := MyPolyId(0);
  while (i < n)
  {
    i := i + MyPolyId(1);
  }
  assert 0 <= i;
}

procedure Id5(n: int)
{
  var i: int;
  var b: bool;
  i, b := 0, false;
  while (i < n)
  {
    i, b := i + 1, false;
  }
  assert !b;
}

procedure Id6(n: int)
{
  var i: int;
  var b: bool;
  i, b := 0, MyPolyId(false);
  while (i < n)
  {
    i, b := i + 1, false;
  }
  assert !b;
}

procedure Id7(n: int)
{
  var i, k, y, z: int;
  i, k := 0, 0;
  while (i < n)
  {
    i := i + 1;
    y, z := MyBogusId(5), -5;
    k := k + z;
    if (*) {
      assert y == z;  // fine
    }
  }
  assert 0 <= k;  // error: this does not hold -- k may very well be negative
}

procedure Id8(n: int)
{
  var i, k: int;
  i, k := 0, 0;
  while (i < n)
  {
    i := i + 1;
    k := k + MyBogusId(5);
  }
  assert 0 <= k;  // since we lied about MyBogusId being an {:identity} function, the abstract interpreter gives us this bogus invariant
}

procedure Id9(n: int)
  requires 0 < n;
{
  var i, k: int;
  i, k := 0, 0;
  while (i < n)
    invariant i <= n && -k == 5*i;
  {
    i := i + 1;
    k := k + MyBogusId(5);
  }
  assert -k == 5*n;
  assert false;  // this just shows the effect of MyBogusId even more; there is no complaint about this assert
}

procedure Id10(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + MultipleArgs(19, 23);
  }
  assert 0 <= i;  // error: no information is known about i
}

procedure Id11(n: int)
{
  var i, k: int;
  i, k := 0, 0;
  while (i < n)
  {
    i := i + 1;
    k := k + BoolToInt(false);  // this should not be treated as an identity function, since it goes from one type to another
  }
  assert 0 <= k;  // error: no information is known about k
}

procedure Id12(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + SometimesId0(false);
  }
  assert 0 <= i;  // error: no information is known about i
}

procedure Id13(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + SometimesId0(1);
  }
  assert 0 <= i;
}

procedure Id14(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + SometimesId0(-1);
  }
  assert 0 <= i;  // error: this does not hold
}

procedure Id15(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + SometimesId1(1);
  }
  assert 0 <= i;  // fine: SometimesId1 claims to be an identity and the use of it is int->int
}

procedure Id16(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + SometimesId2(false);
  }
  assert 0 <= i;  // error: no information is known about i
}

procedure Id17(n: int)
{
  var i: int;
  i := 0;
  while (i < n)
  {
    i := i + SometimesId2(1);
  }
  assert 0 <= i;  // fine: SometimesId2 claims to be an identity and the use of it is int->int
}

// real numbers

procedure W0(N: real)
{
  var i, bf0: real;
  i := 0.0;
  while (i < N) {
    bf0 := N - i;
    i := i + 1.0;
    // check termination:
    assert 0.0 <= bf0;
    assert N - i <= bf0 - 1.0;
  }
}

// mod

procedure Mod0(n: int)
  requires 10 < n;
{
    var i: int;

    i := 0;
    while (i < 10)
    {
        i := (i mod n) + 1;
    }
    assert i == 10;
}
