type ref;
// types
type Color;
const unique red: Color;
const unique blue: Color;
const unique green: Color;

axiom (forall ce:Color :: ce==red || ce==blue || ce==green);
var myColor: Color;

// procedure
procedure SetTo(c: Color);
  modifies myColor
;

  ensures myColor==c;

implementation SetTo(c: Color) {
  assert (blue==green);
  myColor:=blue;
}



