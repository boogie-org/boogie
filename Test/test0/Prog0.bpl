// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff NoErrors.expect "%t"
// BoogiePL Examples

type elements;

var x:int;  var y:real;  var z:ref;		// Variables
var x.3:bool; var $ar:ref;		// Names can have glyphs

const a, b, c:int;		// Consts

function f (int, int) returns (int);	// Function with arity 2
function g (   int , int) returns (int);	// Function with arity 2
function h(int,int) returns (int);	// Function with arity 2

function m (int) returns (int);	// Function with arity 1
function k(int) returns (int);	// Function with arity 1


axiom 	
  (forall x : int :: f(g(h(a,b),c),x) > 100) ;

procedure p (x:int, y:ref) returns (z:int, w:[int,ref]ref, q:int);


procedure q(x:int, y:ref) returns (z:int)	// Procedure with output params
  requires x > 0;		// as many req/ens/mod you want
  ensures z > 3;	
  ensures old(x) == 1;		// old only in ensures..
  modifies z,y,$ar;
{  
  var t, s: int;
  var r: [int,ref]ref;
  
  start:			// one label per block
    t := x;
    s := t;
    z := x + t;
    call s, r,z := p(t,r[3,null]);	// procedure call with mutiple returns
    goto continue, end ;	// as many labels as you like
 
  continue:
    return;			// ends control flow
    
  end:
    goto start;
}    

procedure s(e: elements) { L: return; }
procedure r (x:int, y:ref) returns (z:int);

type ref;
const null : ref;
