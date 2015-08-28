function {:existential true} {:absdomain "ImplicationDomain"} b1(x1: bool, x2: bool) : bool;
function {:existential true} {:absdomain "ImplicationDomain"} b2(x1: bool, x2: bool) : bool;

var x: int;
var flag: bool;

procedure foo ()
  modifies x, flag;
  ensures b1(flag, x == 0);
{
   flag := true;
   x := 0;
}

procedure bar()
  modifies x, flag;
  ensures b2(flag, x == 0);
{
   flag := false;
   x := 0;
}
