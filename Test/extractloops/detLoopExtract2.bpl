// RUN: %boogie -nologo -nologo -stratifiedInline:1 -extractLoops -deterministicExtractLoops -recursionBound:6  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//This example checks the bug fix in the loop extract for http://symdiff.codeplex.com/workitem/4
procedure {:entrypoint} Main() returns(r:int)
{ 
  var i, j : int;
  var Flag : bool;
  var b : bool;
  i := 0;
  j := 0;
  Flag := false;
  while(i<3)
  {
    havoc b;
    if (b || Flag) {
      i := i + 1;
      j := j + 1; 
    }
    else {
     Flag := true;
     j := j + 1;
    }
  }
  assume !(i == j || i == j - 1);
  return;
}
