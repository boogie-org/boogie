type ref;
type Wicket;
const w: Wicket;
var favorite: Wicket;

function age(Wicket) returns (int);

axiom age(w)==7;

procedure NewFavorite(p: Wicket);
  modifies favorite
;

  ensures favorite==p;

implementation NewFavorite(l: Wicket) {
  favorite:=l;
}