// RUN: %boogie -noinfer -contractInfer -printAssignment -inlineDepth:1 -abstractHoudini:HoudiniConst -z3opt:MBQI=true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:existential true} {:absdomain "Intervals"} b1(x: int) : bool;

procedure main() 
{
   var i: int;
   var x: int;
   var arr: [int] int;

   i := 0;

   while(*) 
     invariant (i >= 0) && (forall j: int :: (0 <= j && j < i) ==> b1(arr[j]));
   {
       havoc x;
       assume x == 0 || x == 1;

       arr[i] := x;
       i := i + 1;
   }

   havoc x;
   assume x >= 0 && x < i;
   assert arr[x] == 0 || arr[x] == 1;
}
