type ref;
// consts
const w: int;


// vars
var favorite: int;

// procedure
procedure SetToSeven(p: int);
  modifies favorite
;

  ensures favorite==p;

implementation SetToSeven(l: int) {
  favorite:=w;
}



