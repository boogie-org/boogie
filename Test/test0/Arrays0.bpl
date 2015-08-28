// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff NoErrors.expect "%t"
var one: [int]int;
var two: [int,int]int;
var three: [int,int,int]int;  // three's a crowd
