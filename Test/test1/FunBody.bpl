// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function g0<beta>(x:beta) returns (beta);
function g1<beta>() returns (beta);

function {:inline true} f1() returns (int) { 13 }
function {:inline true} f2() returns (int) { true }                  // wrong type
function {:inline true} f3<alpha>(x:alpha) returns (alpha) { g0(x) }
function {:inline true} f4<alpha>(x:alpha) returns (alpha) { g0(5) } // wrong type
function {:inline true} f5<alpha>() returns (alpha) { g1() }
function {:inline true} f6<alpha>() returns (alpha) { g1():int }     // wrong type



