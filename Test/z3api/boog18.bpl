type ref;
const A100INT4_name:int;

function Match(a:int, t:int) returns (int);
function Array(int, int, int) returns (bool);

axiom(forall a:int :: {Match(a, A100INT4_name)} Array(a, 4, 100));

const myNull: int;
var p: int;
procedure main() 
modifies p;
ensures p!=myNull;
{
  p:=myNull;
}