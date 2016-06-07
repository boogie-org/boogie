type ref;
// types
type Color;
const blue: Color;

var myArray:[int] Color;
var myMatrix:[int,int] Color;

// procedure
procedure SetTo(c: Color);
  modifies myArray, myMatrix
;

  ensures myArray[0]==c;

implementation SetTo(c: Color) {
  myMatrix[0,1]:=c;
  myArray[0]:=blue;
}



