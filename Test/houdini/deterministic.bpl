// RUN: %boogie  /nologo /contractInfer /inlineDepth:1 /printAssignment /noinfer  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


function f(a:int):int;

procedure {:inline 1} Foo(x:int) returns (r:int) 
free ensures r == f(x);
{
     if (x >0 ) {    
     call r := Foo(x);
     r := r + 1;
     havoc r;
    } else {
     r := 0;
    }
     return;
}

procedure Check(x1:int, x2:int) 
{
      var r1: int, r2:int;
 
      call r1 := Foo(x2); //inlined
      call r2 := Foo(x2);  //inlined
      assert r1 == r2;
}
