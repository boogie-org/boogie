// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Check that assumes in loop invariants are handled correctly

var x : int;

procedure Test()
  modifies x;
{
   entry:
      goto loophead, exit;

   loophead:
      assume x >= 0;
      x := 0;
      goto loophead, exit; 

   exit:
      assume x < 0;
      assert false;
      return;
}
