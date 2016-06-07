// id = "P0:1"
// priority = 5
// checksum = "012"
//
// Action: skip
procedure {:id "P0:1"} {:priority 5} {:checksum "012"} P0()
{
    assert false;
}


// id = "P1:0"
// priority = 1
// checksum = "234"
//
// Action: skip
procedure {:priority 1} {:checksum "234"} P1()
{
    assert true;
}


// id = "P3:0"
// priority = 1
// checksum = "234"
//
// Action: skip
procedure {:checksum "234"} P3()
{
    assert true;
}
