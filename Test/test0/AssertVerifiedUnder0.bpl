// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0()
{
    assert {:verified_under} true;
    assert {:verified_under true, false} true;
}
