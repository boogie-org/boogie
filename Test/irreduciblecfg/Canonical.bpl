// RUN: %parallel-boogie "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors

procedure Irreducible ()
{
A: goto B,C;
B: goto C,D;
C: goto B;
D: return;
} 
