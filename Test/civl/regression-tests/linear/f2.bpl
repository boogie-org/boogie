// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure Split({:linear_in} xls: [int]bool) returns ({:linear} xls1: [int]bool, {:linear} xls2: [int]bool);
ensures xls == MapOr(xls1, xls2) && xls1 != MapConst(false) && xls2 != MapConst(false);

procedure Allocate() returns ({:linear} x: [int]bool);

procedure main()
{
   var {:linear} x: [int] bool;
   var {:linear} x1: [int] bool;
   var {:linear} x2: [int] bool;

   call x := Allocate();
   assume x == MapConst(true);

   call x1, x2 := Split(x);
   assert false;
}
