type ref;
type Wicket;
const w: Wicket;
var favorite: Wicket;
function age(Wicket) returns (int);

axiom age(w)==7;

procedure NewFavorite(p: Wicket);
  modifies favorite;

  ensures favorite==p;

implementation NewFavorite(l: Wicket) {
  favorite:=l;
}

const myBool: bool;
const myRef: ref;
const v: Wicket;

axiom 7 < 8;
axiom 7 <= 8;
axiom 8 > 7;
axiom 8 >= 7;
axiom 6 != 7;

axiom 7+1==8;
axiom 8-1==7;
axiom 7/1==7;
axiom 7%2==1;
axiom 4*2==8;

axiom ((7==7) || (8==8));
axiom ((7==7) ==> (7<8));
axiom ((7==7) <==> (10==10));
axiom ((7==7) && (8==8));

var favorite2: Wicket;
procedure SwapFavorites() 
  modifies favorite,favorite2;

  ensures (favorite==old(favorite2)) && (favorite2==old(favorite));
{
  var temp: Wicket;
  temp:=favorite;
  favorite:=favorite2;
  // favorite2:=temp; // commenting this line seeds a bug
}
