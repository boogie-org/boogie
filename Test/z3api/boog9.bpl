type ref;
// types
type Wicket;
var favorite: Wicket;

function age(w:Wicket) returns (int);
axiom (forall v:Wicket :: age(v)==7);
axiom (exists v:Wicket :: age(v)<8);


// procedure
procedure SetToSeven(p: Wicket);
  modifies favorite
;

  ensures favorite==p;

implementation SetToSeven(l: Wicket) {
  favorite:=favorite;
}



