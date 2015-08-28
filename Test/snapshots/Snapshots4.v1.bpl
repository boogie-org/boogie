procedure {:checksum "P0$proc#0"} P0();
// Action: skip
// Priority: 0
implementation {:id "P0"} {:checksum "P0$impl#0"} P0()
{
}


procedure {:checksum "P1$proc#0"} P1();
// Action: verify
// Priority: 1
implementation {:id "P1"} {:checksum "P1$impl#0"} P1()
{
    call P2();
}


procedure {:checksum "P3$proc#0"} P3();
// Action: verify
// Priority: 2
implementation {:id "P3"} {:checksum "P3$impl#1"} P3()
{
    assert false;
}


procedure {:checksum "P2$proc#0"} P2();
  ensures G();
// Action: verify
// Priority: 3
implementation {:id "P2"} {:checksum "P2$impl#0"} P2()
{
}


function {:checksum "G#0"} G() : bool
{
    F()
}


function {:checksum "F#1"} F() : bool
{
    false
}
