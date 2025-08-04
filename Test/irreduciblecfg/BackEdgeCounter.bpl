// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure irreducible() {
    var i: int;
    var j: int;

    i := 1;
    goto B1, B4;

    B1:
        assume j > 0;
        goto B2;
    
    B2:
        assert i > 0;
        goto B3;
    
    B3:
        assert j > 0;
        goto B4;
    
    B4:
        i := i+1;
        goto B2;
}