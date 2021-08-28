// RUN: %parallel-boogie -errorLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure ManyErrors()
{
    L0: goto L1, L2, L3, L4, L5, L6, L7, L8, L9, L10;
    L1: assert false;
    L2: assert false;
    L3: assert false;
    L4: assert false;
    L5: assert false;
    L6: assert false;
    L7: assert false;
    L8: assert false;
    L9: assert false;
    L10: assert false;
}
