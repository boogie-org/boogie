// RUN: %boogie -noinfer -contractInfer -printAssignment -useUnsatCoreForContractInfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: bool;

procedure foo(x:int, y:int, z:int)
//requires
requires br0 ==> x == 1; 
requires br1 ==> y == 1; 
requires br2 ==> z == 1; 
//ensures
ensures  be0 ==> x == 1;
{
   
}


const {:existential true} br0: bool;
const {:existential true} br1: bool;
const {:existential true} br2: bool;
const {:existential true} be0: bool;


