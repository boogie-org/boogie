// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0()
{
  var s: Vec int;

  s := Vec_Append(Vec_Empty(), 0);
  s := Vec_Append(s, 1);
  s := Vec_Append(s, 2);
  assert Vec_Len(s) == 3;
  assert Vec_Nth(s, 1) == 1;
  s := Vec_Update(s, 1, 3);
  assert Vec_Nth(s, 0) == 0;
  assert Vec_Nth(s, 1) == 3;
  assert Vec_Len(s) == 3;
}

procedure test1(s: Vec int, x: int)
requires 0 <= x && x < Vec_Len(s);
requires (forall i: int :: 0 <= i && i < Vec_Len(s) ==> Vec_Nth(s, i) == 0);
ensures Vec_Nth(s, x) == 0;
{
}

procedure test2(s: Vec int, x: int, y: int)
requires 0 <= x && x <= y && y < Vec_Len(s);
requires (forall i, j: int :: 0 <= i && i <= j && j < Vec_Len(s) ==> Vec_Nth(s, i) <= Vec_Nth(s, j));
ensures Vec_Nth(s, x) <= Vec_Nth(s, y);
{
}

procedure lookup(s: Vec int, x: int) returns (b: bool)
ensures b == (exists i: int :: 0 <= i && i < Vec_Len(s) && x == Vec_Nth(s, i));
{
  var i: int;

  b := false;
  i := 0;
  while (i < Vec_Len(s))
  invariant (forall u: int :: 0 <= u && u < i ==> x != Vec_Nth(s, u));
  invariant 0 <= i;
  {
    if (Vec_Nth(s, i) == x) {
      b := true;
      return;
    }
    i := i + 1;
  }
}

procedure equality(s: Vec int, s': Vec int)
requires Vec_Len(s) == Vec_Len(s');
requires (forall i: int :: 0 <= i && i < Vec_Len(s) ==> Vec_Nth(s, i) == Vec_Nth(s', i));
ensures s == s';
{
}

procedure update(s: Vec int, pos: int, val: int) returns (s': Vec int)
requires 0 <= pos && pos < Vec_Len(s);
requires Vec_Nth(s, pos) == val;
ensures s' == s;
{
  s' := Vec_Update(s, pos, val);
}

procedure sorted_update(s: Vec int, pos: int, val: int) returns (s': Vec int)
requires (forall i, j: int :: 0 <= i && i <= j && j < Vec_Len(s) ==> Vec_Nth(s, i) <= Vec_Nth(s, j));
requires 0 <= pos && pos < Vec_Len(s);
requires (forall i: int:: 0 <= i && i < pos ==> Vec_Nth(s, i) <= val);
requires (forall i: int :: pos < i && i < Vec_Len(s) ==> val <= Vec_Nth(s, i));
ensures (forall i, j: int :: 0 <= i && i <= j && j < Vec_Len(s') ==> Vec_Nth(s', i) <= Vec_Nth(s', j));
{
  s' := Vec_Update(s, pos, val);
}

procedure sorted_insert(s: Vec int, x: int) returns (s': Vec int)
requires (forall i, j: int :: 0 <= i && i <= j && j < Vec_Len(s) ==> Vec_Nth(s, i) <= Vec_Nth(s, j));
ensures (forall i, j: int :: 0 <= i && i <= j && j < Vec_Len(s') ==> Vec_Nth(s', i) <= Vec_Nth(s', j));
{
  var pos: int;
  var val: int;

  pos := 0;
  while (pos < Vec_Len(s) && Vec_Nth(s, pos) <= x)
  invariant 0 <= pos;
  invariant (forall i: int:: 0 <= i && i < pos ==> Vec_Nth(s, i) <= x);
  {
    pos := pos + 1;
  }

  val := x;
  s' := s;
  while (pos < Vec_Len(s'))
  invariant 0 <= pos;
  invariant (forall i: int:: 0 <= i && i < pos ==> Vec_Nth(s', i) <= val);
  invariant (forall i, j: int :: 0 <= i && i <= j && j < Vec_Len(s') ==> Vec_Nth(s', i) <= Vec_Nth(s', j));
  invariant (forall i: int :: pos <= i && i < Vec_Len(s') ==> val <= Vec_Nth(s', i));
  {
    s', val := Vec_Update(s', pos, val), Vec_Nth(s', pos); // swap s'[pos] and val
    pos := pos + 1;
  }
  s' := Vec_Append(s', val);
}

type {:datatype} Value;
function {:constructor} Integer(i: int): Value;
function {:constructor} Vector(v: Vec Value): Value;

procedure test3(val: Value) returns (val': Value)
requires val is Vector && Vec_Len(val->v) == 1 && Vec_Nth(val->v, 0) == Integer(0);
ensures val == val';
{
  var s: Vec Value;

  s := Vec_Empty();
  s := Vec_Append(s, Integer(0));
  val' := Vector(s);
}

function has_zero(val: Value): (bool)
{
  if (val is Integer)
  then val == Integer(0)
  else (exists i: int :: 0 <= i && i < Vec_Len(val->v) && has_zero(Vec_Nth(val->v, i)))
}

procedure traverse(val: Value) returns (b: bool)
ensures b == has_zero(val);
{
  var s: Vec Value;
  var i: int;

  b := false;
  if (val is Integer) {
      b := val == Integer(0);
      return;
  }
  s := val->v;
  i := 0;
  while (i < Vec_Len(s))
  invariant !b;
  invariant 0 <= i;
  invariant (forall j: int :: 0 <= j && j < i ==> !has_zero(Vec_Nth(s, j)));
  {
    call b := traverse(Vec_Nth(s, i));
    if (b) {
        return;
    }
    assert !has_zero(Vec_Nth(s, i));
    i := i + 1;
  }
}
