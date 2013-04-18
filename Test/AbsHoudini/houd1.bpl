function {:existential true} b1(x: bool) : bool;

var myVar: int;

procedure foo (i:int)
modifies myVar;
// comment
ensures b1(myVar>0);
{
  if (i>0) {
    myVar := 5;
  } else {
    myVar := 0;
  }
}

// expected end assigment: b1(x) = true
