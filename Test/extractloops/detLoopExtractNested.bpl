// RUN: %boogie  -nologo -stratifiedInline:1 -extractLoops -deterministicExtractLoops -recursionBound:100  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//This example checks the bug fix in the loop extract for http://symdiff.codeplex.com/workitem/1

var t: int;
procedure {:entrypoint} NestedLoops()
modifies t;
//ensures t == 6;
{
   var i:int, j:int;
   i, j, t := 0, 0, 0;
   while(i < 2) {
     j := 0;
     while (j < 3) {
       t := t + 1;
       j := j + 1;
     }
     i := i + 1;
   }
   assume true; //would be provable (!true) wihtout the fix
}

