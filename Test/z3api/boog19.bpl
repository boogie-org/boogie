type name;
type ref;
var alloc:[int]name;


function Field(int) returns (name);
function Base(int) returns (int);

// Constants
const unique UNALLOCATED:name;
const unique ALLOCATED: name;
const unique FREED:name;

const unique BYTE:name;

function Equal([int]bool, [int]bool) returns (bool);
function Subset([int]bool, [int]bool) returns (bool);
function Disjoint([int]bool, [int]bool) returns (bool);

function Empty() returns ([int]bool);
function Singleton(int) returns ([int]bool);
function Reachable([int,int]bool, int) returns ([int]bool);
function Union([int]bool, [int]bool) returns ([int]bool);
function Intersection([int]bool, [int]bool) returns ([int]bool);
function Difference([int]bool, [int]bool) returns ([int]bool);
function Dereference([int]bool, [int]int) returns ([int]bool);
function Inverse(f:[int]int, x:int) returns ([int]bool);

function AtLeast(int, int) returns ([int]bool);
function Rep(int, int) returns (int);
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x)[y]} AtLeast(n,x)[y] ==> x <= y && Rep(n,x) == Rep(n,y));
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x),Rep(n,x),Rep(n,y)} x <= y && Rep(n,x) == Rep(n,y) ==> AtLeast(n,x)[y]);
axiom(forall n:int, x:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);
axiom(forall n:int, x:int, z:int :: {PLUS(x,n,z)} Rep(n,x) == Rep(n,PLUS(x,n,z)));
axiom(forall n:int, x:int :: {Rep(n,x)} (exists k:int :: Rep(n,x) - x  == n*k));


function Array(int, int, int) returns ([int]bool);
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z <= 0 ==> Equal(Array(x,n,z), Empty()));
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z > 0 ==> Equal(Array(x,n,z), Difference(AtLeast(n,x),AtLeast(n,PLUS(x,n,z)))));


axiom(forall x:int :: !Empty()[x]);

axiom(forall x:int, y:int :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:int :: {Singleton(y)} Singleton(y)[y]);

/* this formulation of Union IS more complete than the earlier one */
/* (A U B)[e], A[d], A U B = Singleton(c), d != e */
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T)[x]} Union(S,T)[x] <==> S[x] || T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T), S[x]} S[x] ==> Union(S,T)[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T), T[x]} T[x] ==> Union(S,T)[x]);

axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T)[x]} Intersection(S,T)[x] <==>  S[x] && T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T), S[x]} S[x] && T[x] ==> Intersection(S,T)[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T), T[x]} S[x] && T[x] ==> Intersection(S,T)[x]);

axiom(forall x:int, S:[int]bool, T:[int]bool :: {Difference(S,T)[x]} Difference(S,T)[x] <==> S[x] && !T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Difference(S,T), S[x]} S[x] ==> Difference(S,T)[x] || T[x]);

axiom(forall x:int, S:[int]bool, M:[int]int :: {Dereference(S,M)[x]} Dereference(S,M)[x] ==> (exists y:int :: x == M[y] && S[y]));
axiom(forall x:int, S:[int]bool, M:[int]int :: {M[x], S[x], Dereference(S,M)} S[x] ==> Dereference(S,M)[M[x]]);
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} !S[x] ==> Equal(Dereference(S,M[x := y]), Dereference(S,M)));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] &&  Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Difference(Dereference(S,M), Singleton(M[x])), Singleton(y))));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] && !Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Dereference(S,M), Singleton(y))));

axiom(forall f:[int]int, x:int :: {Inverse(f,f[x])} Inverse(f,f[x])[x]);
axiom(forall f:[int]int, x:int, y:int :: {Inverse(f[x := y],y)} Equal(Inverse(f[x := y],y), Union(Inverse(f,y), Singleton(x))));
axiom(forall f:[int]int, x:int, y:int, z:int :: {Inverse(f[x := y],z)} y == z || Equal(Inverse(f[x := y],z), Difference(Inverse(f,z), Singleton(x))));

axiom(forall S:[int]bool, T:[int]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x], Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[int]bool, T:[int]bool :: {Subset(S,T)} Subset(S,T) || (exists x:int :: S[x] && !T[x]));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x], Disjoint(S,T), T[x]} !(S[x] && Disjoint(S,T) && T[x]));
axiom(forall S:[int]bool, T:[int]bool :: {Disjoint(S,T)} Disjoint(S,T) || (exists x:int :: S[x] && T[x]));

function Unified([name][int]int) returns ([int]int);
axiom(forall M:[name][int]int, x:int :: {Unified(M)[x]} Unified(M)[x] == M[Field(x)][x]);
axiom(forall M:[name][int]int, x:int, y:int :: {Unified(M[Field(x) := M[Field(x)][x := y]])} Unified(M[Field(x) := M[Field(x)][x := y]]) == Unified(M)[x := y]);
// Memory model

var Mem: [name][int]int;

function Match(a:int, t:name) returns (bool);
function HasType(v:int, t:name) returns (bool);
function Values(t:name) returns ([int]bool);

axiom(forall v:int, t:name :: {Values(t)[v]} Values(t)[v] ==> HasType(v, t));
axiom(forall v:int, t:name :: {HasType(v, t), Values(t)} HasType(v, t) ==> Values(t)[v]);

// Field declarations


// Type declarations

const unique A100INT4_name:name;
const unique INT4_name:name;
const unique PA100INT4_name:name;
const unique PINT4_name:name;
const unique PPINT4_name:name;

// Field definitions

// Type definitions

axiom(forall a:int :: {Match(a, A100INT4_name)} Subset(Empty(), Array(a, 4, 100)));
axiom(forall a:int, e:int :: {Match(a, A100INT4_name), Array(a, 4, 100)[e]}
    Match(a, A100INT4_name) && Array(a, 4, 100)[e] ==> Match(e, INT4_name));

axiom(forall a:int :: {Match(a, INT4_name)}
    Match(a, INT4_name) <==> Field(a) == INT4_name);
axiom(forall v:int :: HasType(v, INT4_name));

axiom(forall a:int :: {Match(a, PA100INT4_name)}
    Match(a, PA100INT4_name) <==> Field(a) == PA100INT4_name);
axiom(forall v:int :: {HasType(v, PA100INT4_name)} {Match(v, A100INT4_name)}
    HasType(v, PA100INT4_name) <==> (v == 0 || (v > 0 && Match(v, A100INT4_name))));

axiom(forall a:int :: {Match(a, PINT4_name)}
    Match(a, PINT4_name) <==> Field(a) == PINT4_name);
axiom(forall v:int :: {HasType(v, PINT4_name)} {Match(v, INT4_name)}
    HasType(v, PINT4_name) <==> (v == 0 || (v > 0 && Match(v, INT4_name))));

axiom(forall a:int :: {Match(a, PPINT4_name)}
    Match(a, PPINT4_name) <==> Field(a) == PPINT4_name);
axiom(forall v:int :: {HasType(v, PPINT4_name)} {Match(v, PINT4_name)}
    HasType(v, PPINT4_name) <==> (v == 0 || (v > 0 && Match(v, PINT4_name))));

function MINUS_BOTH_PTR_OR_BOTH_INT(a:int, b:int, size:int) returns (int); 
axiom(forall a:int, b:int, size:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)} 
size * MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size) <= a - b && a - b < size * (MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size) + 1));

function MINUS_LEFT_PTR(a:int, a_size:int, b:int) returns (int);
axiom(forall a:int, a_size:int, b:int :: {MINUS_LEFT_PTR(a,a_size,b)} MINUS_LEFT_PTR(a,a_size,b) == a - a_size * b);

function PLUS(a:int, a_size:int, b:int) returns (int);
axiom(forall a:int, a_size:int, b:int :: {PLUS(a,a_size,b)} PLUS(a,a_size,b) == a + a_size * b);

function MULT(a:int, b:int) returns (int); // a*b
axiom(forall a:int, b:int :: {MULT(a,b)} MULT(a,b) == a * b);

function DIV(a:int, b:int) returns (int); // a/b	
	      
axiom(forall a:int, b:int :: {DIV(a,b)}
a >= 0 && b > 0 ==> b * DIV(a,b) <= a && a < b * (DIV(a,b) + 1)
); 

axiom(forall a:int, b:int :: {DIV(a,b)}
a >= 0 && b < 0 ==> b * DIV(a,b) <= a && a < b * (DIV(a,b) - 1)
); 

axiom(forall a:int, b:int :: {DIV(a,b)}
a < 0 && b > 0 ==> b * DIV(a,b) >= a && a > b * (DIV(a,b) - 1)
); 

axiom(forall a:int, b:int :: {DIV(a,b)}
a < 0 && b < 0 ==> b * DIV(a,b) >= a && a > b * (DIV(a,b) + 1)
); 

function BINARY_BOTH_INT(a:int, b:int) returns (int);
/*
function POW2(a:int) returns (bool);
axiom POW2(1);
axiom POW2(2);
axiom POW2(4);
axiom POW2(8);
axiom POW2(16);
axiom POW2(32);
axiom POW2(64);
axiom POW2(128);
axiom POW2(256);
axiom POW2(512);
axiom POW2(1024);
axiom POW2(2048);
axiom POW2(4096);
axiom POW2(8192);
axiom POW2(16384);
axiom POW2(32768);
axiom POW2(65536);
axiom POW2(131072);
axiom POW2(262144);
axiom POW2(524288);
axiom POW2(1048576);
axiom POW2(2097152);
axiom POW2(4194304);
axiom POW2(8388608);
axiom POW2(16777216);
axiom POW2(33554432);
*/
function LIFT(a:bool) returns (int);
axiom(forall a:bool :: {LIFT(a)} a <==> LIFT(a) != 0);

function NOT(a:int) returns (int);
axiom(forall a:int :: {NOT(a)} a == 0 ==> NOT(a) != 0);
axiom(forall a:int :: {NOT(a)} a != 0 ==> NOT(a) == 0);

function NULL_CHECK(a:int) returns (int);
axiom(forall a:int :: {NULL_CHECK(a)} a == 0 ==> NULL_CHECK(a) != 0);
axiom(forall a:int :: {NULL_CHECK(a)} a != 0 ==> NULL_CHECK(a) == 0);

const unique g : int;
axiom(g != 0);


procedure  main ( ) returns ($result.main$11.5$1$:int)

//TAG: requires __objectOf(g) != 0
requires(Base(g) != 0);

//TAG: requires __allocated(g)
requires(alloc[Base(g)] == ALLOCATED);

//TAG: requires __allocated(g + 55)
requires(alloc[Base(PLUS(g, 4, 55))] == ALLOCATED);

//TAG: Type Safety Precondition
requires(forall a:int :: {Mem[Field(a)][a]} HasType(Mem[Field(a)][a], Field(a)));
requires(HasType(g, PA100INT4_name));

{
var p : int;

assume(HasType(p, PINT4_name));
p := PLUS(g, 4, 55) ;
assert(HasType(p, PINT4_name));

}

