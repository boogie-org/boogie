// RUN: %boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Test the polyhedra domain for linear inequalities


procedure SimpleLoop ()
{  
  var i : int;
  
  start:
    i := 0;
    goto test;
 
  test:
    goto Then, Else;

  Then:
    assume i < 10;
    i := i + 1;
    goto test;

  Else:
    assume ! (i < 10);
    return;
}    


procedure VariableBoundLoop (n : int)
{  
  var i : int;
  
  start:
    i := 0;
    goto test;
 
  test:
    goto Then, Else;

  Then:
    assume i < n;
    i := i + 1;
    goto test;

  Else:
    assume ! (i < n);
    return;
}    

procedure Foo () 
{
 var i : int;

 start:
 i := 3 * i + 1;
 i := 3 * (i + 1);
 i := 1 + 3 * i;
 i := (i + 1) * 3 ;
 return;
}

procedure FooToo () 
{
 var i : int;

 start:
 i := 5;
 i := 3 * i + 1;
 i := 3 * (i + 1);
 i := 1 + 3 * i;
 i := (i + 1) * 3 ;
 return;
}

procedure FooTooStepByStep () 
{
 var i : int;

 L0: i := 5; goto L1;
 L1: i := 3 * i + 1; goto L2;
 L2: i := 3 * (i + 1); goto L3;
 L3: i := 1 + 3 * i; goto L4;
 L4: i := (i + 1) * 3; return;
}
