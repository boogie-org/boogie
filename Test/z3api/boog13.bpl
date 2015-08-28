type ref;
// types
type Wicket;
var favorite: Wicket;
var v: Wicket;

function age(w:Wicket) returns (int);

axiom (exists v:Wicket :: age(v)<8 && 
          (forall v:Wicket
 :: age(v)==7) 

      );


// procedure
procedure SetToSeven(p: Wicket);
  modifies favorite
;

  ensures favorite==p;

implementation SetToSeven(l: Wicket) {
  favorite:=favorite;
}



