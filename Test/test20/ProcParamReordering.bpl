// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type C _;


procedure P<a, b>(x : a, y : b) returns ();

implementation P<a, b>(x : a, y : b) returns () {}

implementation P<c, d>(a : c, b : d) returns () {}

implementation P<d, c>(a : c, b : d) returns () {}

implementation P<d, c>(a : c, b : C d) returns () {}

implementation P<a>(x : a, y : a) returns () {}