// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Test1()
{
   entry:
      assert !true == false;
      return;
}

procedure Test2()
{
   var b: bool;

   entry:
      assume b != false;
      assert b;
      return;
}
