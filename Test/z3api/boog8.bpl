type ref;
// types
type Wicket;
var favorite: Wicket;


const myBv: bv5;
axiom myBv==1bv2++2bv3;

const myBool: bool;
axiom myBool==true;


// procedure
procedure SetToSeven(p: Wicket);
  modifies favorite
;

  ensures favorite==p;

implementation SetToSeven(l: Wicket) {
  favorite:=favorite;
}



