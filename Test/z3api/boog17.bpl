type name;
type ref;
const unique g : int;
axiom(g != 0);

const unique PINT4_name:name;

function PLUS(a:int, a_size:int, b:int) returns (int);
axiom(forall a:int, a_size:int, b:int :: {PLUS(a,a_size,b)} PLUS(a,a_size,b) == a + a_size * b);

function HasType(v:int, t:name) returns (bool);


procedure  main ( ) returns ($result.main$11.5$1$:int) {
  var p : int;

start:
  assume(HasType(p, PINT4_name));
  goto label_3;

label_3:
  goto label_4;

label_4:
  p := PLUS(g, 4, 55) ;
  assert(HasType(p, PINT4_name));
}