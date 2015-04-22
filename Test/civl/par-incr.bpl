// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0} x: int;

procedure {:yields} {:layer 0,1} Incr();
ensures {:right} |{ A: x := x + 1; return true; }|;

procedure {:yields} {:layer 1,2} Incr2() 
ensures {:right} |{ A: x := x + 2; return true; }|;
{
  yield;
  par Incr() | Incr();
  yield;
}

procedure {:yields} {:layer 1} Yield()
{
   yield;
}

procedure {:yields} {:layer 2,3} Incr4() 
ensures {:atomic} |{ A: x := x + 4; return true; }|;
{
  yield;
  par Incr2() | Incr2() | Yield();
  yield;
}



