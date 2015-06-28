// RUN: %boogie -infer:j -instrumentInfer:e -printInstrumented -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Simple test file for checking the inference of linear constraints.

var x: int;
var y: int;
var z: int;

procedure p()
{
A:
    goto B, C;
B:
    assume x <= 0;
    goto D;
C:
    assume y <= 0;
    goto D;
D:
    return;
}
