type ref;
type Wicket;

var favorite: Wicket;
var hate: Wicket;

procedure NewFavorite(p: Wicket);
  modifies favorite
;

  ensures favorite==p;

implementation NewFavorite(l: Wicket) {
  favorite:=l;
}


procedure Swap();
  modifies favorite,hate;
  ensures favorite==old(hate);

implementation Swap() {
  hate := favorite;
}