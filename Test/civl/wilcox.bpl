// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure {:layer 1} GhostRead() returns (oldx: int)
ensures x == oldx;
{
   oldx := x;
}


var {:layer 0,2} x: int;

procedure {:yields} {:layer 0,1} IncX();
  ensures {:both} |{ A: x := x + 1; return true; }|;

procedure {:yields} {:layer 1,2} SlowAdd(n: int)
  requires {:layer 1} n >= 0;       
  ensures {:both} |{ A: x := x + n; return true; }|; {
    var i: int;
    var {:layer 1} oldx: int;
    yield;

    call oldx := GhostRead();
    i := 0;
    while (i < n)
        invariant {:layer 1} i <= n;    
        invariant {:layer 1} x == oldx + i;
    {
        call IncX();
        i := i + 1;
    }

    assert {:layer 1} i == n;

    yield;
}