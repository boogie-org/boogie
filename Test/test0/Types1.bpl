type T, U;
type V;

function h(T) returns (int);
function k(x:T) returns (int);
function l(x) returns (int);  // resolve error
function m(x:int, x) returns (bool);  // resolve error
