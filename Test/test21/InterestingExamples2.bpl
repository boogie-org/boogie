

procedure P() returns () {
var m : <a>[a]ref;
var n : <b>[b]b;
var o : ref;

m[5] := null;
assert m[true := o][5] == null;
assert m[n[true] := o][5] == null;
}

type ref;
const null : ref;
