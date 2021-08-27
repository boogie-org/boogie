// RUN: %parallel-boogie -errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Foo0()
{
    assert {:msg "My error message for assertion failure"} false;
}

procedure Foo1()
requires {:msg "My error message for precondition failure"} false;
{

}

procedure CallerFoo1()
{
    call Foo1();
}

procedure Foo2()
ensures {:msg "My error message for postcondition failure"} false;
{
    call Foo1();
}

procedure {:msg_if_verifies "Are you sure this procedure should verify?"} Foo3()
{

}
