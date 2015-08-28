// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff NoErrors.expect "%t"
// Test to parse large integer literals

axiom 1234567890987654321 == 1234567890987654321;

function f(int) returns (int);

axiom f(1234567890987654321) == 0;
