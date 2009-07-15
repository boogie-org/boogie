function G(int) returns (int);
axiom (forall x: int :: { G(x) } 0 <= x ==> G(x) == x);

function F(int) returns (int);
axiom (forall x: int :: { F(G(x)) } 0 <= x ==> F(G(x)) == 5);

procedure Lemma(y: int)
  requires 0 <= y;
  ensures F(y) == 5;
{
  // proof:
  assert G(y) == y;
}

procedure Main0()
{
  assert F(2) == 5;  // error: cannot prove this directly, because of the trigger
}

procedure Main1()
{
  call Lemma(2);
  assert F(2) == 5;
}

procedure Main2()
{
  call Lemma(3);
  assert F(2) == 5;  // error: Lemma was instantiated the wrong way
}

procedure Main3()
{
  call forall Lemma(*);
  assert F(2) == 5;
}

procedure Main4()
{
  call forall Lemma(*);
  assert false;  // error
}

procedure Main5(z: int)
{
  call forall Lemma(*);
  assert F(z) == 5;  // error: z might be negative
}

procedure Main6(z: int)
  requires 0 <= z;
{
  call forall Lemma(*);
  assert F(z) == 5;
}

// ------------ several parameters

function K(int, int) returns (int);
axiom (forall x: int, y: int :: { K(G(x), G(y)) } 0 <= x && 0 <= y ==> K(G(x), G(y)) == 25);

procedure MultivarLemma(x: int, y: int)
  requires 0 <= x;
  requires 0 <= y;
  ensures K(x,y) == 25;
{
  // proof:
  assert G(x) == x;
  assert G(y) == y;
}

procedure Multi0(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  assert K(x,y) == 25;  // error
}

procedure Multi1(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call MultivarLemma(x, y);
  assert K(x,y) == 25;
}

procedure Multi2(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call forall MultivarLemma(x, y);
  assert K(x,y) == 25;
}

procedure Multi3(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call forall MultivarLemma(*, y);
  assert K(x,y) == 25;
}

procedure Multi4(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call forall MultivarLemma(x, *);
  assert K(x,y) == 25;
}

procedure Multi5(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call forall MultivarLemma(2 + 100, *);
  assert K(102, y) == 25;
  assert false;  // error
}

procedure Multi6(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call forall MultivarLemma(*, y);
  assert K(x+2,y+2) == 25;  // error
}

procedure Multi7(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call forall MultivarLemma(x, *);
  assert K(x+2,y+2) == 25;  // error
}

procedure Multi8(x: int, y: int)
  requires 0 <= x && 0 <= y;
{
  call forall MultivarLemma(*, *);
  assert K(x+2,y+2) == 25;  // that's the ticket!
}

