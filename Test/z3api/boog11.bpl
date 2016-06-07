type ref;
// types
const top: ref;
var myRef: ref;

// procedure
procedure SetTo(r: ref);
  modifies myRef
;

  ensures myRef==r;

implementation SetTo(c: ref) {
  myRef:=top;
}



