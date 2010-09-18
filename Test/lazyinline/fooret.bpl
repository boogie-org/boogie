
procedure A()
{
  var x : int;
  var y : int;
  var nondet: bool;

start:
  x := 0;
  assume y == 2;
  goto lh;

lh:
  goto lab1, lab2;

lab1:
   assume x < y;
   x := x + 1;
   havoc nondet;
   goto lab3, lab4;

lab3:
   assume !nondet;
   goto lh;

lab4:
   assume nondet;
   return;

lab2: 
   assume x >= y;
   assert false;

}


