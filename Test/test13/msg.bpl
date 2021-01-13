// RUN: %boogie -errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Foo()
{
    assert {:msg "My error message"} false;
}
