// id = "P1:0"
// priority = 3
// checksum = "123"
// 
// Action: verify
procedure {:priority 3} {:checksum "123"} P1()
{
    assert false;
}


// id = "P2:0"
// priority = 3
// checksum = null
//
// Action: verify
procedure {:priority 3} P2()
{
    assert false;
}


// id = "P3:0"
// priority = 1
// checksum = null
//
// Action: verify
procedure P3()
{
    assert false;
}


// id = "P0:1"
// priority = 5
// checksum = "012"
//
// Action: verify
procedure {:id "P0:1"} {:priority 5} {:checksum "012"} P0()
{
    assert false;
}
