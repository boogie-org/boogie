type name;
type ref;
type byte;
function OneByteToInt(byte) returns (int);
function TwoBytesToInt(byte, byte) returns (int);
function FourBytesToInt(byte, byte, byte, byte) returns (int);
axiom(forall b0:byte, c0:byte :: {OneByteToInt(b0), OneByteToInt(c0)} OneByteToInt(b0) == OneByteToInt(c0) ==> b0 == c0);
axiom(forall b0:byte, b1: byte, c0:byte, c1:byte :: {TwoBytesToInt(b0, b1), TwoBytesToInt(c0, c1)} TwoBytesToInt(b0, b1) == TwoBytesToInt(c0, c1) ==> b0 == c0 && b1 == c1);
axiom(forall b0:byte, b1: byte, b2:byte, b3:byte, c0:byte, c1:byte, c2:byte, c3:byte :: {FourBytesToInt(b0, b1, b2, b3), FourBytesToInt(c0, c1, c2, c3)} FourBytesToInt(b0, b1, b2, b3) == FourBytesToInt(c0, c1, c2, c3) ==> b0 == c0 && b1 == c1 && b2 == c2 && b3 == c3);

// Mutable
var Mem_BYTE:[int]byte;
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

const unique INT4_name:name;
const unique PINT4_name:name;

// Field definitions

// Type definitions

axiom(forall a:int :: {Match(a, INT4_name)}
    Match(a, INT4_name) <==> Field(a) == INT4_name);
axiom(forall v:int :: HasType(v, INT4_name));

axiom(forall a:int :: {Match(a, PINT4_name)}
    Match(a, PINT4_name) <==> Field(a) == PINT4_name);
axiom(forall v:int :: {HasType(v, PINT4_name)} {Match(v, INT4_name)}
    HasType(v, PINT4_name) <==> (v == 0 || (v > 0 && Match(v, INT4_name))));

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

function choose(a:bool, b:int, c:int) returns (x:int);
axiom(forall a:bool, b:int, c:int :: {choose(a,b,c)} a ==> choose(a,b,c) == b);
axiom(forall a:bool, b:int, c:int :: {choose(a,b,c)} !a ==> choose(a,b,c) == c);

function BIT_BAND(a:int, b:int) returns (x:int);
axiom(forall a:int, b:int :: {BIT_BAND(a,b)} a == b ==> BIT_BAND(a,b) == a);
axiom(forall a:int, b:int :: {BIT_BAND(a,b)} POW2(a) && POW2(b) && a != b ==> BIT_BAND(a,b) == 0);
axiom(forall a:int, b:int :: {BIT_BAND(a,b)} a == 0 || b == 0 ==> BIT_BAND(a,b) == 0);

function BIT_BOR(a:int, b:int) returns (x:int);

function BIT_BXOR(a:int, b:int) returns (x:int);

function BIT_BNOT(a:int) returns (int);

function LIFT(a:bool) returns (int);
axiom(forall a:bool :: {LIFT(a)} a <==> LIFT(a) != 0);

function NOT(a:int) returns (int);
axiom(forall a:int :: {NOT(a)} a == 0 ==> NOT(a) != 0);
axiom(forall a:int :: {NOT(a)} a != 0 ==> NOT(a) == 0);

function NULL_CHECK(a:int) returns (int);
axiom(forall a:int :: {NULL_CHECK(a)} a == 0 ==> NULL_CHECK(a) != 0);
axiom(forall a:int :: {NULL_CHECK(a)} a != 0 ==> NULL_CHECK(a) == 0);

procedure nondet_choice() returns (x:int);


procedure havoc_assert(i:int);
requires (i != 0);

procedure havoc_assume(i:int);
ensures (i != 0);

procedure __HAVOC_free(a:int);
modifies alloc;
ensures (forall x:int :: {alloc[x]} x == a || old(alloc)[x] == alloc[x]);
ensures (alloc[a] == FREED);
// Additional checks guarded by tranlator flags
// requires alloc[a] == ALLOCATED;
// requires Base(a) == a;

procedure __HAVOC_malloc(obj_size:int) returns (new:int);
requires obj_size >= 0;
modifies alloc;
ensures (new > 0);
ensures (forall x:int :: {Base(x)} new <= x && x < new+obj_size ==> Base(x) == new);
ensures (forall x:int :: {alloc[x]} x == new || old(alloc)[x] == alloc[x]);
ensures old(alloc)[new] == UNALLOCATED && alloc[new] == ALLOCATED;

procedure _strdup(str:int) returns (new:int);

procedure _xstrcasecmp(a0:int, a1:int) returns (ret:int);

procedure _xstrcmp(a0:int, a1:int) returns (ret:int);





procedure  main ( ) returns ($result.main$3.5$1$:int)

modifies alloc;
//TAG: no freed locations
ensures(forall f:int :: {alloc[Base(f)]} old(alloc)[Base(f)] == UNALLOCATED || old(alloc)[Base(f)] == alloc[Base(f)]);

modifies Mem;
//TAG: no updated memory locations
ensures(forall f: name, m:int :: {Mem[f][m]} Mem[f][m] == old(Mem[f])[m]);
free ensures(Mem[Field(0)][0] == old(Mem[Field(0)])[0]);

//TAG: Type Safety Precondition
requires(forall a:int :: {Mem[Field(a)][a]} HasType(Mem[Field(a)][a], Field(a)));
//TAG: Type Safety Postcondition
ensures(forall a:int :: {Mem[Field(a)][a]} HasType(Mem[Field(a)][a], Field(a)));
ensures(HasType($result.main$3.5$1$, INT4_name));
{
var havoc_stringTemp:int;
var condVal:int;
var $a$1$4.6$main : int;
var b : int;
var c : int;
var flag : int;
var tempBoogie0:int;
var tempBoogie1:int;
var tempBoogie2:int;
var tempBoogie3:int;
var tempBoogie4:int;
var tempBoogie5:int;
var tempBoogie6:int;
var tempBoogie7:int;
var tempBoogie8:int;
var tempBoogie9:int;
var tempBoogie10:int;
var tempBoogie11:int;
var tempBoogie12:int;
var tempBoogie13:int;
var tempBoogie14:int;
var tempBoogie15:int;
var tempBoogie16:int;
var tempBoogie17:int;
var tempBoogie18:int;
var tempBoogie19:int;


start:

assume(HasType($a$1$4.6$main, INT4_name));
assume(HasType(b, INT4_name));
assume(HasType(c, INT4_name));
assume(HasType(flag, INT4_name));
assume(HasType($result.main$3.5$1$, INT4_name));
goto label_3;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(20)
label_1:
assume (forall m:int :: {Mem[Field(m)][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[Field(m)][m] == old(Mem[Field(m)])[m]);
return;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(20)
label_2:
assume false;
return;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(4)
label_3:
goto label_4;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(4)
label_4:
goto label_5;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(4)
label_5:
goto label_6;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(5)
label_6:
goto label_7;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(7)
label_7:
c := LIFT(b < $a$1$4.6$main) ;
//TAG: Type Safety Assertion
assert(forall a:int :: {Mem[Field(a)][a]} HasType(Mem[Field(a)][a], Field(a)));
assert(HasType($a$1$4.6$main, INT4_name));
assert(HasType(b, INT4_name));
assert(HasType(c, INT4_name));
assert(HasType(flag, INT4_name));
goto label_8;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(9)
label_8:
goto label_8_true , label_8_false ;


label_8_true :
assume (c != 0);
goto label_10;


label_8_false :
assume (c == 0);
goto label_9;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(12)
label_9:
flag := 0 ;
//TAG: Type Safety Assertion
assert(forall a:int :: {Mem[Field(a)][a]} HasType(Mem[Field(a)][a], Field(a)));
assert(HasType($a$1$4.6$main, INT4_name));
assert(HasType(b, INT4_name));
assert(HasType(c, INT4_name));
assert(HasType(flag, INT4_name));
goto label_11;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(10)
label_10:
flag := 1 ;
//TAG: Type Safety Assertion
assert(forall a:int :: {Mem[Field(a)][a]} HasType(Mem[Field(a)][a], Field(a)));
assert(HasType($a$1$4.6$main, INT4_name));
assert(HasType(b, INT4_name));
assert(HasType(c, INT4_name));
assert(HasType(flag, INT4_name));
goto label_11;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(15)
label_11:
goto label_11_true , label_11_false ;


label_11_true :
assume (b < $a$1$4.6$main);
goto label_13;


label_11_false :
assume !(b < $a$1$4.6$main);
goto label_12;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(18)
label_12:
//TAG: flag == 0
assert (flag == 0);
goto label_1;


// c:\espmain1\esp\tests\hvregr\split_memory\014\bool_vals_gt.c(16)
label_13:
//TAG: flag == 1
assert (flag == 1);
goto label_1;

}

