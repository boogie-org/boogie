type ref;
type W;

function f1(W,int) returns (int);
function f1(W,int,int) returns (int);

procedure main() 
{  
  var w: W;
  assert(f1(w,0)==f1(w,0,0));
}