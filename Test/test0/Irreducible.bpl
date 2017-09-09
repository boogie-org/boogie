// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Irreducible ()
{
A: goto B,C;
B: goto C,D;
C: goto B;
D: return;
} 
