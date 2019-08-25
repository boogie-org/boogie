// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory -doModSetAnalysis "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:builtin "MapConst"} mapconstbool(bool) : [int]bool;
function {:builtin "MapOr"} mapunion([int]bool, [int]bool) : [int]bool;

function {:inline} {:linear "1"} SetCollector1(x: [int]bool) : [int]bool
{
  x
}

procedure Split({:linear_in "1"} xls: [int]bool) returns ({:linear "1"} xls1: [int]bool, {:linear "1"} xls2: [int]bool);
ensures xls == mapunion(xls1, xls2) && xls1 != mapconstbool(false) && xls2 != mapconstbool(false);

procedure Allocate() returns ({:linear "1"} x: [int]bool);

procedure main() 
{
   var {:linear "1"} x: [int] bool;
   var {:linear "1"} x1: [int] bool;
   var {:linear "1"} x2: [int] bool;

   call x := Allocate();
   assume x == mapconstbool(true);

   call x1, x2 := Split(x);
   assert false;
}
