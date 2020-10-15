// RUN: %boogie -useArrayTheory -lib -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} Vec _;
function {:constructor} Vec<T>(contents: [int]T, len: int): Vec T;
function Default<T>(): T;

const Identity: [int]int;
axiom (forall x: int :: Identity[x] == x);
function {:inline} AtLeast(x: int): [int]bool
{
  MapLe(MapConst(x), Identity)
}
function {:inline} Range(from: int, n: int): [int]bool {
  MapDiff(AtLeast(from), AtLeast(from + n))
}
axiom {:ctor "Vec"} (forall<T> x: Vec T :: {len#Vec(x)}{contents#Vec(x)} MapIte(Range(0, len#Vec(x)), MapConst(Default()), contents#Vec(x)) == MapConst(Default()));
axiom {:ctor "Vec"} (forall<T> x: Vec T :: {len#Vec(x)} len#Vec(x) >= 0);

function {:inline} Empty<T>(): Vec T
{
  Vec(MapConst(Default()), 0)
}
function {:inline} Append<T>(v: Vec T, x: T) : Vec T
{
  Vec(contents#Vec(v)[len#Vec(v) := x], len#Vec(v) + 1)
}
function {:inline} Update<T>(v: Vec T, i: int, x: T) : Vec T
{
  if (0 <= i && i < len#Vec(v)) then Vec(contents#Vec(v)[i := x], len#Vec(v)) else v
}
function {:inline} Nth<T>(v: Vec T, i: int): T
{
  contents#Vec(v)[i]
}
function {:inline} Len<T>(v: Vec T): int
{
  len#Vec(v)
}

procedure test0()
{
  var s: Vec int;

  s := Append(Empty(), 0);
  s := Append(s, 1);
  s := Append(s, 2);
  assert Len(s) == 3;
  assert Nth(s, 1) == 1;
  s := Update(s, 1, 3);
  assert Nth(s, 0) == 0;
  assert Nth(s, 1) == 3;
  assert Len(s) == 3;
}

procedure test1(s: Vec int, x: int)
requires 0 <= x && x < Len(s);
requires (forall i: int :: 0 <= i && i < Len(s) ==> Nth(s, i) == 0);
ensures Nth(s, x) == 0;
{
}

procedure test2(s: Vec int, x: int, y: int)
requires 0 <= x && x <= y && y < Len(s);
requires (forall i, j: int :: 0 <= i && i <= j && j < Len(s) ==> Nth(s, i) <= Nth(s, j));
ensures Nth(s, x) <= Nth(s, y);
{
}

procedure lookup(s: Vec int, x: int) returns (b: bool)
ensures b == (exists i: int :: 0 <= i && i < Len(s) && x == Nth(s, i));
{
  var i: int;

  b := false;
  i := 0;
  while (i < Len(s))
  invariant (forall u: int :: 0 <= u && u < i ==> x != Nth(s, u));
  invariant 0 <= i;
  {
    if (Nth(s, i) == x) {
      b := true;
      return;
    }
    i := i + 1;
  }
}

procedure equality(s: Vec int, s': Vec int)
requires Len(s) == Len(s');
requires (forall i: int :: 0 <= i && i < Len(s) ==> Nth(s, i) == Nth(s', i));
ensures s == s';
{
}

procedure update(s: Vec int, pos: int, val: int) returns (s': Vec int)
requires 0 <= pos && pos < Len(s);
requires Nth(s, pos) == val;
ensures s' == s;
{
  s' := Update(s, pos, val);
}

procedure sorted_update(s: Vec int, pos: int, val: int) returns (s': Vec int)
requires (forall i, j: int :: 0 <= i && i <= j && j < Len(s) ==> Nth(s, i) <= Nth(s, j));
requires 0 <= pos && pos < Len(s);
requires (forall i: int:: 0 <= i && i < pos ==> Nth(s, i) <= val);
requires (forall i: int :: pos < i && i < Len(s) ==> val <= Nth(s, i));
ensures (forall i, j: int :: 0 <= i && i <= j && j < Len(s') ==> Nth(s', i) <= Nth(s', j));
{
  s' := Update(s, pos, val);
}

procedure sorted_insert(s: Vec int, x: int) returns (s': Vec int)
requires (forall i, j: int :: 0 <= i && i <= j && j < Len(s) ==> Nth(s, i) <= Nth(s, j));
ensures (forall i, j: int :: 0 <= i && i <= j && j < Len(s') ==> Nth(s', i) <= Nth(s', j));
{
  var pos: int;
  var val: int;

  pos := 0;
  while (pos < Len(s) && Nth(s, pos) <= x)
  invariant 0 <= pos;
  invariant (forall i: int:: 0 <= i && i < pos ==> Nth(s, i) <= x);
  {
    pos := pos + 1;
  }

  val := x;
  s' := s;
  while (pos < Len(s'))
  invariant 0 <= pos;
  invariant (forall i: int:: 0 <= i && i < pos ==> Nth(s', i) <= val);
  invariant (forall i, j: int :: 0 <= i && i <= j && j < Len(s') ==> Nth(s', i) <= Nth(s', j));
  invariant (forall i: int :: pos <= i && i < Len(s') ==> val <= Nth(s', i));
  {
    s', val := Update(s', pos, val), Nth(s', pos); // swap s'[pos] and val
    pos := pos + 1;
  }
  s' := Append(s', val);
}

type {:datatype} Value;
function {:constructor} Integer(i: int): Value;
function {:constructor} Vector(v: Vec Value): Value;

procedure test3(val: Value) returns (val': Value)
requires is#Vector(val) && Len(v#Vector(val)) == 1 && Nth(v#Vector(val), 0) == Integer(0);
ensures val == val';
{
  var s: Vec Value;

  s := Empty();
  s := Append(s, Integer(0));
  val' := Vector(s);
}

function has_zero(val: Value): (bool)
{
  if (is#Integer(val))
  then val == Integer(0)
  else (exists i: int :: 0 <= i && i < Len(v#Vector(val)) && has_zero(Nth(v#Vector(val), i)))
}

procedure traverse(val: Value) returns (b: bool)
ensures b == has_zero(val);
{
  var s: Vec Value;
  var i: int;

  b := false;
  if (is#Integer(val)) {
      b := val == Integer(0);
      return;
  }
  s := v#Vector(val);
  i := 0;
  while (i < Len(s))
  invariant !b;
  invariant 0 <= i;
  invariant (forall j: int :: 0 <= j && j < i ==> !has_zero(Nth(s, j)));
  {
    call b := traverse(Nth(s, i));
    if (b) {
        return;
    }
    assert !has_zero(Nth(s, i));
    i := i + 1;
  }
}
