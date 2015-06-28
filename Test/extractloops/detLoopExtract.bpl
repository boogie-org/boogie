// RUN: %boogie -stratifiedInline:1 -extractLoops -removeEmptyBlocks:0 -coalesceBlocks:0 -deterministicExtractLoops -recursionBound:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g:int;
var h:int; //not modified
var k:int; //modified in a procedure call

procedure {:entrypoint} Foo(a:int)
modifies g;
modifies h;
modifies k;
//ensures  g == old(g);
{
   var b: int;
   b := 0;
   g := a;
   h := 5;  
      
LH:    //assert (b + g == a);
       if (g == 0) {
          goto LE;
       }
       //assume (b + g == a); // to help the loop extraction figure out the loop invariant
       b := b + 1;
       call Bar();
       g := g - 1;
       if (b > 100) {
   	  goto L2;
       }            
       goto LH;

LE: 

    
L2: //g := old(g);
    //assert (b == a);
    assume (b != a);
    return;

}

procedure Bar() 
modifies k;
{
 k := 0;
 return; 
}
