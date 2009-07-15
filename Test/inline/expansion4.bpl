function f(x:int) returns(bool);
axiom {:ignore "bvInt"} {:inline true} (forall x:int :: f(x) <==> true);
axiom {:ignore "bvDefSem"} {:inline true} (forall x:int :: f(x) <==> false);

procedure {:forceBvZ3Native true} foo()
{
  assert f(3);
}

procedure {:forceBvInt true} foo2()
{
  assert !f(3);
}

axiom  (forall x: bv64, y: bv64 :: { $sub.unchk.u8(x, y) } $check.sub.u8(x, y) ==> $sub.u8(x, y) == $sub.unchk.u8(x, y));
axiom {:inline true} {:ignore "bvDefSem"} (forall x: bv64, y: bv64 :: { $check.sub.u8(x, y) } 
$check.sub.u8(x, y) <==> $_inrange.u8($sub.i8(x, y)));

function $check.sub.u8(x: bv64, y: bv64) returns (bool);
function $_inrange.u8(bv64) returns (bool);
function {:bvbuiltin "bvsub"} $sub.unchk.u8(x: bv64, y: bv64) returns (bv64);
function {:bvbuiltin "bvsub"} {:bvint "-"} $sub.i8(x: bv64, y: bv64) returns (bv64);
function {:bvbuiltin "bvsub"} {:bvint "-"} $sub.u8(x: bv64, y: bv64) returns (bv64);


procedure {:forceBvZ3Native true} baz()
{
    return;
}


