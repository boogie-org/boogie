// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var sdv_7: int;
var sdv_21: int;
const {:existential true} b1: bool;
const{:existential true}  b2: bool;
const{:existential true}  b3: bool;
const{:existential true}  b4: bool;

procedure push(a:int)
modifies sdv_7, sdv_21;
{
   sdv_21 := sdv_7;
   sdv_7 := a;
}

procedure pop()
modifies sdv_7, sdv_21;
{
   sdv_7 := sdv_21;
   havoc sdv_21;
}

procedure foo()
modifies sdv_7, sdv_21;
requires {:candidate} b1 ==> (sdv_7 == 0);
ensures{:candidate}  b2 ==> (sdv_7 == old(sdv_7));
{
   call push(2);
   call pop();
   call bar();
}

procedure bar()
requires{:candidate} b3 ==> (sdv_7 == 0);
ensures{:candidate}  b4 ==> (sdv_7 == old(sdv_7));
modifies sdv_7, sdv_21;
{
   call push(1);
   call pop();
}

procedure main()
modifies sdv_7, sdv_21;
{
   sdv_7 := 0;
   call foo();
}

