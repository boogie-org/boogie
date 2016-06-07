procedure {:checksum "P0$proc#0"} P0();
ensures G();
// Action: verify
implementation {:id "P0"} {:checksum "P0$impl#0"} P0()
{
}


function {:checksum "F#1"} F() : bool
{
    false
}


function {:checksum "G#0"} G() : bool
{
    F()
}
