// RUN: %boogie -noinfer -contractInfer -printAssignment -useUnsatCoreForContractInfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Example to exercise the unsatcore to optimize houdini

procedure foo(x:int, y:int, z:int)
//requires
requires br0 ==> x == 1; 
requires br1 ==> y == 1; 
requires br2 ==> z == 1; 
//ensures
ensures  be0 ==> x == 1;
{
   
}

procedure bar()
{
   call foo(1, 2, 3);

}

const {:existential true} br0: bool;
const {:existential true} br1: bool;
const {:existential true} br2: bool;
const {:existential true} be0: bool;


// The output does not have any details to illustrate the flag (its an optimization)
// One way to make sure it works is to run with -trace
//
// $boogie_codeplex\binaries\boogie.exe -noinfer -contractInfer -printAssignment -trace testUnsatCore.bpl
//
// and lookout for the following lines
//
// Number of unsat core prover queries = 2
// Number of unsat core prunings = 2