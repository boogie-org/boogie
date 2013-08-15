var g: bool;

procedure {:inline 1} bar() returns (l: bool) 
{
  l := g;
}

procedure A1() 
modifies g;
{
    g := true;
    assert |{ var l: bool; A: call l := bar(); return l; }|;
    assert (exists p: bool :: |{ var l: bool; A: call l := bar(); return l; }|);
    assert (forall p: bool :: |{ var l: bool; A: call l := bar(); return l; }|);
}

procedure A2() 
{
    assert |{ var l: bool; A: assume g; call l := bar(); return l; }|;
    assert g ==> |{ var l: bool; A: call l := bar(); return l; }|;
    assert (exists p: bool :: g ==> |{ var l: bool; A: call l := bar(); return l; }|);
    assert (forall p: bool :: g ==> |{ var l: bool; A: call l := bar(); return l; }|);
}

procedure A3() 
{
    assume |{ var l: bool; A: call l := bar(); return l; }|;
    assert |{ var l: bool; A: call l := bar(); return l; }|;
}

procedure A4()
modifies g;
{
    g := true;
    assert |{ var l: bool; A: call l := bar(); return !l; }|;
}