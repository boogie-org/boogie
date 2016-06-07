type ref;

function Rep(int, int) returns (int);
axiom(forall n:int, x:int :: {Rep(n,x)} 
  (exists k:int :: Rep(n,x) - x  == n*k));

procedure  main(x:int) 
{
assert((Rep(0,x)==x));
return;
}