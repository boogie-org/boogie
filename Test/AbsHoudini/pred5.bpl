// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:PredicateAbs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} b1(x: bool) : bool;

procedure main() 
{
   var i: int;
   var x: int;
   var arr: [int] int;

   i := 0;

   while(*) 
     invariant b1((i >= 0) && (forall j: int :: (0 <= j && j < i) ==> arr[j] == 0));
   {
       havoc x;
       assume x == 0;

       arr[i] := x;
       i := i + 1;
   }

   havoc x;
   assume x >= 0 && x < i;
   assert b1(arr[x] == 0);
}
