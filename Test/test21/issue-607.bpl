// RUN: %parallel-boogie /enhancedErrorMessages:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure p(error:bool) {
    if (error) {
        assume {:print "ModelCaptured"} true;
        assert false;
    }
}