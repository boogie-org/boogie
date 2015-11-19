// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure test0()
{
    assert {:verified_under 4} true;
    assert {:verified_under 3.0} true;
}
