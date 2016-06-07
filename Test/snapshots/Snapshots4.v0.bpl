procedure {:checksum "P0$proc#0"} P0();
// Action: verify
implementation {:id "P0"} {:checksum "P0$impl#0"} P0()
{
}


procedure {:checksum "P1$proc#0"} P1();
// Action: verify
implementation {:id "P1"} {:checksum "P1$impl#0"} P1()
{
    call P2();
}


procedure {:checksum "P2$proc#0"} P2();
  ensures G();


procedure {:checksum "P3$proc#0"} P3();
// Action: verify
implementation {:id "P3"} {:checksum "P3$impl#0"} P3()
{
}


function {:checksum "G#0"} G() : bool
{
    F()
}


function {:checksum "F#0"} F() : bool
{
    true
}
