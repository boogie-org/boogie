// RUN: %boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Test the constant propagation AI

var GlobalFlag : bool;

const A, B, C:int;		// Consts

procedure Join (b : bool)
  modifies GlobalFlag;
{  
  var x, y, z:int;
  
  start:
    GlobalFlag := true;
    x := 3;
    y := 4;
    z := x + y;
    goto Then, Else; // if (b)
 
  Then:
    assume b == true;
    x := x + 1;
    goto join;

  Else:
    assume b == false;
    y := 4;
    goto join;
    
  join:
    assert y == 4;
    assert z == 7;
    assert GlobalFlag == true;
    return;
}    


procedure Loop ()
{
  var c, i: int;

  start:
    c := 0; i := 0;
    goto test;
 
  test:
    // if (i < 10);
    goto Then, Else;

  Then:
    assume (i < 10);
    i := i + 1;
    goto test;

  Else:
    return;
}

procedure Evaluate () 
{
 var i : int;

 start:
 i := 5;
 i := 3 * i + 1;
 i := 3 * (i + 1);
 i := 1 + 3 * i;
 i := (i + 1) * 3;
 return;
}
