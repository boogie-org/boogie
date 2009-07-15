var Q: [int,int][int]int;

procedure P()
{
  var q: [int]int;

  start:
    // here's how to do it:
    q := Q[5,8];
    q[13] := 21;
    Q[5,8] := q;

    // not like this:
    Q[5,8][13] := 21;  // error: the updated array must be an identifier
    return;
}
