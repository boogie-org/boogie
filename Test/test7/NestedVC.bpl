// RUN: %boogie -vc:nested "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P()
{
A: goto B, C;
B: goto G;
C: goto D, E;
D: goto F;
E: goto F;
F: goto G;
G: return;
}

procedure Q(x: bool)
{
A: goto B, C;
B: assert x; goto G;
C: goto D, E;
D: goto F;
E: goto F;
F: goto G;
G: return;
}
