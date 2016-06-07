// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function union(<a> [a] bool, <a> [a] bool) returns (<a> [a] bool);

axiom (forall<alpha>             // error: alpha has to occur in dummy types
              x : <a> [a] bool, y : <a> [a] bool,
              z : int ::
              { union(x, y)[z] } 
              union(x, y)[z] == (x[z] || y[z]));

function poly<a>() returns (a);

axiom (forall<alpha>
              x : <a> [a] bool, y : <a> [a] bool,
              z : int ::
              { union(x, y)[z], poly() : alpha } 
              union(x, y)[z] == (x[z] || y[z]));

