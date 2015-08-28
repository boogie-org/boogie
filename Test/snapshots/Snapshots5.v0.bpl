procedure {:checksum "P0$proc#0"} P0(n: int where F(n));
// Action: verify
implementation {:id "P0"} {:checksum "P0$impl#0"} P0(n: int)
{
    assert false;
}

function {:checksum "F#1"} F(n: int) : bool
{
    false
}
