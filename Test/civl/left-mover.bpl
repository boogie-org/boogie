// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,2} x : int;

procedure {:left} {:layer 1} inc ()
modifies x;
{ x := x + 1; }

// Error: Gate failure of ass_eq_1 not preserved by inc
procedure {:atomic} {:layer 1} ass_eq_1 ()
{ assert x == 1; } 

// Correct
procedure {:atomic} {:layer 1} ass_leq_1 ()
{ assert x <= 1; }   

// Error: init and inc do not commute
procedure {:atomic} {:layer 1} init ()
modifies x;
{ x := 0; }          

////////////////////////////////////////////////////////////////////////////////

// Error block is blocking
procedure {:left} {:layer 2} block ()
{ assume x >= 0; } 
