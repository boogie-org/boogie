
procedure P() returns () {
var a : <t>[t]int;

a[5] := 0;
a[true] := 1;
assert a[5] == 0;
}