// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"






type {:linear "1"} X = int;

procedure Split({:linear_in "1"} xls: [int]bool) returns ({:linear "1"} xls1: [int]bool, {:linear "1"} xls2: [int]bool);
ensures xls == MapOr(xls1, xls2) && xls1 != MapConst(false) && xls2 != MapConst(false);

procedure Allocate() returns ({:linear "1"} x: [int]bool);

procedure main()
{
   var {:linear "1"} x: [int] bool;
   var {:linear "1"} x1: [int] bool;
   var {:linear "1"} x2: [int] bool;

   call x := Allocate();
   assume x == MapConst(true);

   call x1, x2 := Split(x);
   assert false;
}
