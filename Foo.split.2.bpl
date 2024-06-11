implementation Foo()
{

  anon0:
    goto anon3_Then;

  anon3_Then:
    assert {:split_here} 2 == 1 + 1;
    assume false;
    return;
}


