// RUN: %boogie -stratifiedInline:1 -extractLoops -removeEmptyBlocks:0 -coalesceBlocks:0 -deterministicExtractLoops -recursionBound:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g:int;

procedure {:entrypoint} Foo(a:int)
requires a >= 0;
modifies g;
{
   var b: int;
   b := 0;
   g := a;
  
LH:
   goto L_true, L_false;

L_true:
   assume (b < a); 
   goto L6;

L6: 
  b := b + 1;
  g := 5;
  goto LH;

L_false:
   assume (b >= a);	      
   goto L_end;

L_end:
   assume (b != a); //modeling assert for stratified inlining
   return;
}
