// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var m: []int;
var p: <a>[]a;

type C _;
var bad: <a,b>[]C a;  // error: b is not used

function F<a>(a, int) returns (bool) { true }

type Set _;
function EmptySet<a>() returns (Set a);
function G<a>(a, int) returns (Set a) { EmptySet() }

function H<a>(int) returns (Set a);

function {:inline true} K<a>(int) returns (Set a)
{ EmptySet() }


procedure P<a>(x: int, y: bool) returns (z: int, w: bool);  // error: "a" is not used

procedure Q<a>(x: int, y: bool) returns (z: int, w: a);
procedure R<a>(x: int, y: bool) returns (z: int, w: Set a);
procedure S<a>(x: a, y: bool) returns (z: int, w: Set a);


function K2<a>(int) returns (Set a)  // now ok
{ EmptySet() }
