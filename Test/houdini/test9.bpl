// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var v1: int;
var v2: int;
var v3: int;
const{:existential true} b1: bool;
const{:existential true} b2: bool;
const{:existential true} b3: bool;
const{:existential true} b4: bool;
const{:existential true} b5: bool;
const{:existential true} b6: bool;
const{:existential true} b7: bool;
const{:existential true} b8: bool;
const{:existential true} b9: bool;
const{:existential true} b10: bool;
const{:existential true} b11: bool;
const{:existential true} b12: bool;
const{:existential true} b13: bool;
const{:existential true} b14: bool;
const{:existential true} b15: bool;
const{:existential true} b16: bool;

procedure push() 
requires {:candidate} b1 ==> v1 == 0;
requires {:candidate} b2 ==> v1 == 1;
ensures  {:candidate} b3 ==> v1 == 0;
ensures {:candidate}  b4 ==> v1 == 1;
modifies v1,v2;
{
   v2 := v1;
   v1 := 1;
}

procedure pop()
modifies v1,v2;
requires {:candidate} b5 ==> v1 == 0;
requires {:candidate} b6 ==> v1 == 1;
ensures  {:candidate} b7 ==> v1 == 0;
ensures {:candidate}  b8 ==> v1 == 1;
{
   v1 := v2;
   havoc v2;
}

procedure foo() 
modifies v1,v2;
requires {:candidate} b9 ==> v1 == 0;
requires {:candidate} b10 ==> v1 == 1;
ensures  {:candidate} b11 ==> v1 == 0;
ensures {:candidate}  b12 ==> v1 == 1;
{
   call push();
   call pop();
}

procedure bar()
modifies v1,v2;
requires {:candidate} b13 ==> v1 == 0;
requires {:candidate} b14 ==> v1 == 1;
ensures  {:candidate} b15 ==> v1 == 0;
ensures {:candidate}  b16 ==> v1 == 1;
{
   call push();
   call pop();
}

procedure main() 
modifies v1,v2;
{
   v1 := 1;
   call foo();
   havoc v1;
   call bar();
}

