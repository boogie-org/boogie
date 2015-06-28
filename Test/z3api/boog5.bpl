type ref;
// types
type Wicket;

// consts
const w: Wicket;
const myBool: bool;
const v: Wicket;
const u: Wicket;
const x: Wicket;


// vars
var favorite: Wicket;

// functions
function age(Wicket) returns (int);

// axioms
axiom age(w)==6;
axiom age(u)==5;
axiom age(x)==4;


// procedure
procedure SetToSeven(p: Wicket);
  modifies favorite
;

  ensures favorite==p;

implementation SetToSeven(l: Wicket) {
  if (age(w)==7) {
    favorite:=l;
  } else {
    favorite:=v;
  }


}



