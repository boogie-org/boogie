// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Trigger errors

function f(int, int) returns (int);
function P(int, int) returns (bool);

axiom (forall x: int ::
       { f(x,10) && f(x,9) }   // error: && not allowed
       f(x,10) == 3);

axiom (forall x: int ::
       { ((((f(x,10) || f(x,9))))) }   // error: || not allowed
       f(x,10) == 3);

axiom (forall x: int ::
       { !f(x,10) }   // error: ! not allowed
       f(x,10) == 3);

axiom (forall x: int ::
       { (!f(x,10)) }   // error: ! not allowed
       f(x,10) == 3);

axiom (forall x: int ::
       { P(x,10) ==> P(20,x) }   // error: ==> not allowed
       f(x,10) == 3);

axiom (forall x: int ::
       { P(x,10) <==> P(20,x) }   // error: <==> not allowed
       f(x,10) == 3);


axiom (forall x: int ::
       { f(x,10) == 3 }   // error: == not allowed
       f(x,10) == 3);

axiom (forall x: int ::
       { f(x,10) < 3 }   // error: < not allowed
       f(x,10) == 3);


axiom (forall x: int ::
       { f(x,10) + f(x,x) != 3 }   // yes, != is allowed
       f(x,10) == 3);

axiom (forall b: bool ::
       { (forall y: int :: b) }   // error: quantifiers not allowed
       b);

// -------------- tests of free variables

const g: int;

axiom (forall x: int ::
       { false, 6 }             // error: does not mention "x"
       x < x + 1);

axiom (forall x: int ::
       { false, x+1, 6 }        // allowed
       x < x + 1);

axiom (forall x: int, y: int ::
       { x+1 }                  // error: does not mention "y"
       { y+1 }                  // error: does not mention "x"
       x < y + 1);

axiom (forall x: int ::
       { g+x != 65 }            // allowed
       x < x + 1);

axiom (forall x: int ::
       { x }                    // "x" by itself is not a good trigger
       x < x + 1);

//axiom (forall x: any ::  // PR: removed for the time being
//       { cast(x,int) }          // can't fool me, still not allowed
//       x == x );

// --- multiple triggers

axiom (forall x: int, y: int, z: int ::
       { x+y+z }                // good
       { x+y, y+z }             // also good
       { f(f(x,y),y) }          // error: does not mention z
       x == x );

// --- multi-triggers

axiom (forall x: int, y: int, z: int ::
       { f(x,x), f(y,y), f(z,z) }  // good
       f(x,y) < f(y,z) );

// --- pattern exclusion

axiom (forall x: int, y: int ::
       {:nopats x }                   // error: "x" by itself is not allowed here either
       {:nopats g }                   // error: "g" by itself is not allowed here either
       x < y);

axiom (forall x: int, y: int ::
       {:nopats f(g,g) }              // but it is okay not to mention the bound variables (in a pattern exclusion)
       x < y);

// --- merging of nested quantifiers (disabled unless both have no triggers)

axiom (forall x:int :: (forall y:int :: { f(x,y) } f(x,y) > 0)); // OK, but no merging - outer quantifier has no trigger
axiom (forall x:int :: (forall y:int :: { f(x,x) } f(x,x) > 0)); // error
axiom (forall x:int :: (forall y:int :: { f(y,y) } f(y,y) > 0)); // OK - no merging

// three levels
axiom (forall x:int :: (forall y:int :: (forall z:int :: { f(x,y) } f(y,y) > 0))); // error - z not mentioned
axiom (forall x:int :: (forall y:int :: (forall z:int :: { f(x,z) } f(y,y) > 0))); // OK - only outer two quantifiers are merged
//axiom (forall x:int :: (forall y:int :: (forall z:int :: f(y,y) > 0))); // OK - all three are merged
axiom (forall x:int :: (forall y:int :: (forall z:int :: { f(x,y), f(y,z) } f(y,y) > 0))); // OK - but not a trigger for outer x,y (which get merged)

// --- no free variables

var h0: int;
var h1: [ref,ref]int;

axiom (forall o: ref, f: ref  :: h1[o,f] // error: cannot mention free variable "h1"
                               < h0);    // error: cannot mention free variable "h0"

const c0: int;
const c1: [ref,ref]int;

axiom (forall o: ref, f: ref :: c1[o,f] < c0);

type ref;
