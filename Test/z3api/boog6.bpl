type ref;
// types
type Wicket;

// consts
var favorite: Wicket;

// axioms
const b: bool;
axiom b==true;

// procedure
procedure SetToSeven(p: Wicket);
  modifies favorite
;

  ensures favorite==p;

implementation SetToSeven(l: Wicket) {
  favorite:=l;
}



