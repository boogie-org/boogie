implementation Foo()
{

  anon0:
    goto anon3_Else;

  anon3_Else:
    assume 2 == 1 + 1;
    assert {:split_here} 3 == 2 + 1;
    goto ;
}


