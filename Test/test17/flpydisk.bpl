type ptr;
function Ptr(ref, int) returns (ptr);
function Obj(ptr) returns (ref);
function Off(ptr) returns (int);

// Ptr, Obj, Off axioms
axiom(forall x:ptr :: {Obj(x)}{Off(x)} x == Ptr(Obj(x), Off(x)));
axiom(forall x_obj:ref, x_off:int :: {Ptr(x_obj, x_off)} x_obj == Obj(Ptr(x_obj, x_off)));
axiom(forall x_obj:ref, x_off:int :: {Ptr(x_obj, x_off)} x_off == Off(Ptr(x_obj, x_off)));

// Mutable
var Mem:[ptr]ptr;
var alloc:[ref]name;
var BS:[ptr]bool;
const field:[ptr]name;

// Immutable
function Size(ref) returns (int);
function Type(ref) returns (int);
function IsHeap(ref) returns (bool); //if the object was allocated by malloc or allocation due to address taken

// Constants
const unique UNALLOCATED:name;
const unique ALLOCATED:name;

function In(ptr, [ptr]bool) returns (bool);
function Subset([ptr]bool, [ptr]bool) returns (bool);
//function Equal([ptr]bool, [ptr]bool) returns (bool);
function Disjoint([ptr]bool, [ptr]bool) returns (bool);
//function UniqueDereference([ptr]bool, [ptr]ptr, ptr) returns (bool);

//function Element(a:ptr) returns (bool);
//axiom(forall a:ptr, S:[ptr]bool :: {In(a,S)} Element(a));

function Empty() returns ([ptr]bool);
function Singleton(ptr) returns ([ptr]bool);
function Reachable([ptr,ptr]bool, ptr) returns ([ptr]bool);
function Union([ptr]bool, [ptr]bool) returns ([ptr]bool);
function Intersection([ptr]bool, [ptr]bool) returns ([ptr]bool);
function Difference([ptr]bool, [ptr]bool) returns ([ptr]bool);
function Decrement([ptr]bool, int) returns ([ptr]bool);
function Increment([ptr]bool, int) returns ([ptr]bool);
function Dereference([ptr]bool, [ptr]ptr) returns ([ptr]bool);
function Array(ptr, int, ptr) returns ([ptr]bool);
function Array1(ptr, ptr) returns ([ptr]bool);


axiom(forall x:ptr :: !In(x, Empty()));

axiom(forall x:ptr, y:ptr :: {In(x, Singleton(y))} In(x, Singleton(y)) ==> x == y);
axiom(forall y:ptr :: {Singleton(y)} In(y, Singleton(y)));

/* this formulation of Union IS more complete than the earlier one */
/* In(e, A U B), In(d, A), A U B = Singleton(c), d != e */
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x, Union(S,T))} In(x, Union(S,T)) ==> In(x, S) || In(x,T));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {Union(S,T), In(x,S)} In(x, S) ==> In(x, Union(S,T)));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {Union(S,T), In(x,T)} In(x, T) ==> In(x, Union(S,T)));

axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x,S), In(x,T), Intersection(S,T)} In(x,S) && In(x,T) ==> In(x, Intersection(S,T)));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x,Intersection(S,T))} In(x, Intersection(S,T)) ==>  In(x,S) && In(x,T));

axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {Difference(S,T), In(x,S)} In(x, S) ==> In(x, Difference(S,T)) || In(x,T));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x,Difference(S,T))} In(x, Difference(S,T)) ==> In(x, S));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x,Difference(S,T)), In(x,T)} !(In(x, Difference(S,T)) && In(x,T)));

axiom(forall x:ptr, n:int, S:[ptr]bool :: {In(x, Decrement(S,n))} In(x, Decrement(S,n)) <==> In(Ptr(Obj(x),Off(x)+n),S));
axiom(forall x:ptr, n:int, S:[ptr]bool :: {In(x, Increment(S,n))} In(x, Increment(S,n)) <==> In(Ptr(Obj(x),Off(x)-n),S));

axiom(forall x:ptr, S:[ptr]bool, M:[ptr]ptr :: {In(x, Dereference(S,M))} In(x, Dereference(S,M)) ==> (exists y:ptr :: x == M[y] && In(y,S)));
axiom(forall x:ptr, S:[ptr]bool, M:[ptr]ptr :: {M[x], In(x, S), Dereference(S,M)} In(x, S) ==> In(M[x], Dereference(S,M)));

axiom(forall a:ptr, x:ptr, n:int, z:ptr :: {In(a,Array(x,n,z))} 
					   In(a,Array(x,n,z)) ==> 
					   (Obj(a) == Obj(x) && Obj(z) == null && (exists k:int :: 0 <= k && k < Off(z) && Off(a) == Off(x) + n*k)));

axiom(forall a:ptr, x:ptr, n:int, z:ptr :: {In(a, Array(x,n,z))} 
	     In(a, Array(x,n,z)) ==> (exists k:int :: 0 <= k && a == PLUS(x,n,Ptr(null,k))));
axiom(forall x:ptr, n:int, z:ptr :: {Array(x,n,z)} Obj(z) == null && Off(z) > 0 ==> In(x, Array(x,n,z)));
axiom(forall x:ptr, n:int, y:ptr, z:ptr :: {PLUS(x,n,y), Array(x,n,z)} 
	     Obj(y) == null && Obj(z) == null && Off(x) <= Off(PLUS(x,n,y)) && Off(PLUS(x,n,y)) < Off(PLUS(x,n,z)) <==> In(PLUS(x,n,y), Array(x,n,z)));

axiom(forall x:ptr, y:ptr, z:ptr :: {In(x,Array1(y,z))} 
				    In(x,Array1(y,z)) <==> 
				    (Obj(x) == Obj(y) && Off(y) <= Off(x) && Off(x) < Off(y) + Off(z)));


/*
axiom(forall x:ptr :: !In(x, Empty()));
axiom(forall x:ptr, y:ptr :: {In(x, Singleton(y))} In(x, Singleton(y)) <==> x == y);

axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x, Union(S,T))} In(x, Union(S,T)) <==> In(x, S) || In(x,T));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {Union(S,T), In(x,S)} In(x, S) ==> In(x, Union(S,T)));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {Union(S,T), In(x,T)} In(x, T) ==> In(x, Union(S,T)));

axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x, Difference(S,T))} In(x, Difference(S,T)) <==> In(x, S) && !In(x,T));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {Difference(S,T), In(x,S), In(x,T)}  (In(x, S) && !In(x,T)) ==> In(x, Difference(S,T)));

axiom(forall x:ptr, n:int, S:[ptr]bool :: {In(x, Decrement(S,n))} In(x, Decrement(S,n)) <==> In(Ptr(Obj(x),Off(x)+n),S));
axiom(forall x:ptr, n:int, S:[ptr]bool :: {In(x, Increment(S,n))} In(x, Increment(S,n)) <==> In(Ptr(Obj(x),Off(x)-n),S));
axiom(forall x:ptr, S:[ptr]bool, M:[ptr]ptr :: {In(x, Dereference(S,M))} In(x, Dereference(S,M)) <==> (exists y:ptr :: x == M[y] && In(y,S)));
axiom(forall x:ptr, S:[ptr]bool, M:[ptr]ptr :: {In(x, S), Dereference(S,M)} In(x, S) ==> In(M[x], Dereference(S,M)));

axiom(forall a:ptr, x:ptr, n:int, z:ptr :: {In(a,Array(x,n,z))} 
					   In(a,Array(x,n,z)) ==> 
					   (Obj(a) == Obj(x) && Obj(z) == null && (exists k:int :: 0 <= k && k < Off(z) && Off(a) == Off(x) + n*k)));

axiom(forall a:ptr, x:ptr, n:int, z:ptr :: {In(a, Array(x,n,z))} 
	     In(a, Array(x,n,z)) ==> (exists k:int :: 0 <= k && a == PLUS(x,n,Ptr(null,k))));
axiom(forall x:ptr, n:int, z:ptr :: {Array(x,n,z)} Obj(z) == null && Off(z) > 0 ==> In(x, Array(x,n,z)));
axiom(forall x:ptr, n:int, y:ptr, z:ptr :: {PLUS(x,n,y), Array(x,n,z)} 
	     Obj(y) == null && Obj(z) == null && Off(x) <= Off(PLUS(x,n,y)) && Off(PLUS(x,n,y)) < Off(PLUS(x,n,z)) <==> In(PLUS(x,n,y), Array(x,n,z)));

axiom(forall x:ptr, y:ptr, z:ptr :: {In(x,Array1(y,z))} 
				    In(x,Array1(y,z)) <==> 
				    (Obj(x) == Obj(y) && Off(y) <= Off(x) && Off(x) < Off(y) + Off(z)));
*/

axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x,S), Subset(S,T)} In(x,S) && Subset(S,T) ==> In(x,T));
axiom(forall S:[ptr]bool, T:[ptr]bool :: {Subset(S,T)} Subset(S,T) || (exists x:ptr :: In(x,S) && !In(x,T)));
axiom(forall x:ptr, S:[ptr]bool, T:[ptr]bool :: {In(x,S), Disjoint(S,T), In(x,T)} !(In(x,S) && Disjoint(S,T) && In(x,T)));
axiom(forall S:[ptr]bool, T:[ptr]bool :: {Disjoint(S,T)} Disjoint(S,T) || (exists x:ptr :: In(x,S) && In(x,T)));

/*
axiom(forall S:[ptr]bool, T:[ptr]bool :: {Subset(S,T)} Subset(S,T) <==> (forall x:ptr :: In(x,S) ==> In(x,T)));
axiom(forall S:[ptr]bool, T:[ptr]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(T,S) && Subset(S,T));
axiom(forall S:[ptr]bool, T:[ptr]bool :: {Disjoint(S,T)} Disjoint(S,T) <==> (forall x:ptr :: !(In(x,S) && In(x,T))));
axiom(forall S:[ptr]bool, M:[ptr]ptr, p:ptr :: {UniqueDereference(S,M,p)} 
					       UniqueDereference(S,M,p) <==> 
					       (forall x:ptr, y:ptr :: {M[x],M[y]} In(x,S) && In(y,S) && M[x] == M[y] ==> x == y || M[x] == p)); 
*/


function ByteCapacity__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_ByteCapacity__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_ByteCapacity__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_ByteCapacity__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {ByteCapacity__DISKETTE_EXTENSION(x)} home_ByteCapacity__DISKETTE_EXTENSION(ByteCapacity__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_ByteCapacity__DISKETTE_EXTENSION(x)} ByteCapacity__DISKETTE_EXTENSION(home_ByteCapacity__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {ByteCapacity__DISKETTE_EXTENSION(x)} ByteCapacity__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 152));
axiom (forall x:ptr :: {home_ByteCapacity__DISKETTE_EXTENSION(x)} home_ByteCapacity__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 152));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_ByteCapacity__DISKETTE_EXTENSION(S))} In(x, _S_ByteCapacity__DISKETTE_EXTENSION(S)) ==> In(home_ByteCapacity__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_ByteCapacity__DISKETTE_EXTENSION(S))} In(x, _S_home_ByteCapacity__DISKETTE_EXTENSION(S)) ==> In(ByteCapacity__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_ByteCapacity__DISKETTE_EXTENSION(S)} In(x, S) ==> In(ByteCapacity__DISKETTE_EXTENSION(x), _S_ByteCapacity__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_ByteCapacity__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_ByteCapacity__DISKETTE_EXTENSION(x), _S_home_ByteCapacity__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,152), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,152), 1) == home_ByteCapacity__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,152))} MINUS_LEFT_PTR(x, 1, Ptr(null,152)) == home_ByteCapacity__DISKETTE_EXTENSION(x));





function ByteOffset___unnamed_16_39e6661e(ptr) returns (ptr);
function home_ByteOffset___unnamed_16_39e6661e(ptr) returns (ptr);
function _S_ByteOffset___unnamed_16_39e6661e([ptr]bool) returns ([ptr]bool);
function _S_home_ByteOffset___unnamed_16_39e6661e([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {ByteOffset___unnamed_16_39e6661e(x)} home_ByteOffset___unnamed_16_39e6661e(ByteOffset___unnamed_16_39e6661e(x)) == x);
axiom (forall x:ptr :: {home_ByteOffset___unnamed_16_39e6661e(x)} ByteOffset___unnamed_16_39e6661e(home_ByteOffset___unnamed_16_39e6661e(x)) == x);
axiom (forall x:ptr :: {ByteOffset___unnamed_16_39e6661e(x)} ByteOffset___unnamed_16_39e6661e(x) == Ptr(Obj(x), Off(x) + 8));
axiom (forall x:ptr :: {home_ByteOffset___unnamed_16_39e6661e(x)} home_ByteOffset___unnamed_16_39e6661e(x) == Ptr(Obj(x), Off(x) - 8));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_ByteOffset___unnamed_16_39e6661e(S))} In(x, _S_ByteOffset___unnamed_16_39e6661e(S)) ==> In(home_ByteOffset___unnamed_16_39e6661e(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_ByteOffset___unnamed_16_39e6661e(S))} In(x, _S_home_ByteOffset___unnamed_16_39e6661e(S)) ==> In(ByteOffset___unnamed_16_39e6661e(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_ByteOffset___unnamed_16_39e6661e(S)} In(x, S) ==> In(ByteOffset___unnamed_16_39e6661e(x), _S_ByteOffset___unnamed_16_39e6661e(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_ByteOffset___unnamed_16_39e6661e(S)} In(x, S) ==> In(home_ByteOffset___unnamed_16_39e6661e(x), _S_home_ByteOffset___unnamed_16_39e6661e(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,8), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,8), 1) == home_ByteOffset___unnamed_16_39e6661e(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,8))} MINUS_LEFT_PTR(x, 1, Ptr(null,8)) == home_ByteOffset___unnamed_16_39e6661e(x));





function BytesPerSector__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_BytesPerSector__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_BytesPerSector__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_BytesPerSector__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {BytesPerSector__DISKETTE_EXTENSION(x)} home_BytesPerSector__DISKETTE_EXTENSION(BytesPerSector__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_BytesPerSector__DISKETTE_EXTENSION(x)} BytesPerSector__DISKETTE_EXTENSION(home_BytesPerSector__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {BytesPerSector__DISKETTE_EXTENSION(x)} BytesPerSector__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 148));
axiom (forall x:ptr :: {home_BytesPerSector__DISKETTE_EXTENSION(x)} home_BytesPerSector__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 148));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_BytesPerSector__DISKETTE_EXTENSION(S))} In(x, _S_BytesPerSector__DISKETTE_EXTENSION(S)) ==> In(home_BytesPerSector__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_BytesPerSector__DISKETTE_EXTENSION(S))} In(x, _S_home_BytesPerSector__DISKETTE_EXTENSION(S)) ==> In(BytesPerSector__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_BytesPerSector__DISKETTE_EXTENSION(S)} In(x, S) ==> In(BytesPerSector__DISKETTE_EXTENSION(x), _S_BytesPerSector__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_BytesPerSector__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_BytesPerSector__DISKETTE_EXTENSION(x), _S_home_BytesPerSector__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,148), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,148), 1) == home_BytesPerSector__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,148))} MINUS_LEFT_PTR(x, 1, Ptr(null,148)) == home_BytesPerSector__DISKETTE_EXTENSION(x));





function CancelRoutine__IRP(ptr) returns (ptr);
function home_CancelRoutine__IRP(ptr) returns (ptr);
function _S_CancelRoutine__IRP([ptr]bool) returns ([ptr]bool);
function _S_home_CancelRoutine__IRP([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {CancelRoutine__IRP(x)} home_CancelRoutine__IRP(CancelRoutine__IRP(x)) == x);
axiom (forall x:ptr :: {home_CancelRoutine__IRP(x)} CancelRoutine__IRP(home_CancelRoutine__IRP(x)) == x);
axiom (forall x:ptr :: {CancelRoutine__IRP(x)} CancelRoutine__IRP(x) == Ptr(Obj(x), Off(x) + 56));
axiom (forall x:ptr :: {home_CancelRoutine__IRP(x)} home_CancelRoutine__IRP(x) == Ptr(Obj(x), Off(x) - 56));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_CancelRoutine__IRP(S))} In(x, _S_CancelRoutine__IRP(S)) ==> In(home_CancelRoutine__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_CancelRoutine__IRP(S))} In(x, _S_home_CancelRoutine__IRP(S)) ==> In(CancelRoutine__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_CancelRoutine__IRP(S)} In(x, S) ==> In(CancelRoutine__IRP(x), _S_CancelRoutine__IRP(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_CancelRoutine__IRP(S)} In(x, S) ==> In(home_CancelRoutine__IRP(x), _S_home_CancelRoutine__IRP(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,56), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,56), 1) == home_CancelRoutine__IRP(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,56))} MINUS_LEFT_PTR(x, 1, Ptr(null,56)) == home_CancelRoutine__IRP(x));





function Cancel__IRP(ptr) returns (ptr);
function home_Cancel__IRP(ptr) returns (ptr);
function _S_Cancel__IRP([ptr]bool) returns ([ptr]bool);
function _S_home_Cancel__IRP([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Cancel__IRP(x)} home_Cancel__IRP(Cancel__IRP(x)) == x);
axiom (forall x:ptr :: {home_Cancel__IRP(x)} Cancel__IRP(home_Cancel__IRP(x)) == x);
axiom (forall x:ptr :: {Cancel__IRP(x)} Cancel__IRP(x) == Ptr(Obj(x), Off(x) + 36));
axiom (forall x:ptr :: {home_Cancel__IRP(x)} home_Cancel__IRP(x) == Ptr(Obj(x), Off(x) - 36));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Cancel__IRP(S))} In(x, _S_Cancel__IRP(S)) ==> In(home_Cancel__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Cancel__IRP(S))} In(x, _S_home_Cancel__IRP(S)) ==> In(Cancel__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Cancel__IRP(S)} In(x, S) ==> In(Cancel__IRP(x), _S_Cancel__IRP(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Cancel__IRP(S)} In(x, S) ==> In(home_Cancel__IRP(x), _S_home_Cancel__IRP(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,36), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,36), 1) == home_Cancel__IRP(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,36))} MINUS_LEFT_PTR(x, 1, Ptr(null,36)) == home_Cancel__IRP(x));





function Control__IO_STACK_LOCATION(ptr) returns (ptr);
function home_Control__IO_STACK_LOCATION(ptr) returns (ptr);
function _S_Control__IO_STACK_LOCATION([ptr]bool) returns ([ptr]bool);
function _S_home_Control__IO_STACK_LOCATION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Control__IO_STACK_LOCATION(x)} home_Control__IO_STACK_LOCATION(Control__IO_STACK_LOCATION(x)) == x);
axiom (forall x:ptr :: {home_Control__IO_STACK_LOCATION(x)} Control__IO_STACK_LOCATION(home_Control__IO_STACK_LOCATION(x)) == x);
axiom (forall x:ptr :: {Control__IO_STACK_LOCATION(x)} Control__IO_STACK_LOCATION(x) == Ptr(Obj(x), Off(x) + 3));
axiom (forall x:ptr :: {home_Control__IO_STACK_LOCATION(x)} home_Control__IO_STACK_LOCATION(x) == Ptr(Obj(x), Off(x) - 3));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Control__IO_STACK_LOCATION(S))} In(x, _S_Control__IO_STACK_LOCATION(S)) ==> In(home_Control__IO_STACK_LOCATION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Control__IO_STACK_LOCATION(S))} In(x, _S_home_Control__IO_STACK_LOCATION(S)) ==> In(Control__IO_STACK_LOCATION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Control__IO_STACK_LOCATION(S)} In(x, S) ==> In(Control__IO_STACK_LOCATION(x), _S_Control__IO_STACK_LOCATION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Control__IO_STACK_LOCATION(S)} In(x, S) ==> In(home_Control__IO_STACK_LOCATION(x), _S_home_Control__IO_STACK_LOCATION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,3), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,3), 1) == home_Control__IO_STACK_LOCATION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,3))} MINUS_LEFT_PTR(x, 1, Ptr(null,3)) == home_Control__IO_STACK_LOCATION(x));





function CurrentStackLocation___unnamed_4_f80453a0(ptr) returns (ptr);
function home_CurrentStackLocation___unnamed_4_f80453a0(ptr) returns (ptr);
function _S_CurrentStackLocation___unnamed_4_f80453a0([ptr]bool) returns ([ptr]bool);
function _S_home_CurrentStackLocation___unnamed_4_f80453a0([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {CurrentStackLocation___unnamed_4_f80453a0(x)} home_CurrentStackLocation___unnamed_4_f80453a0(CurrentStackLocation___unnamed_4_f80453a0(x)) == x);
axiom (forall x:ptr :: {home_CurrentStackLocation___unnamed_4_f80453a0(x)} CurrentStackLocation___unnamed_4_f80453a0(home_CurrentStackLocation___unnamed_4_f80453a0(x)) == x);
axiom (forall x:ptr :: {CurrentStackLocation___unnamed_4_f80453a0(x)} CurrentStackLocation___unnamed_4_f80453a0(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_CurrentStackLocation___unnamed_4_f80453a0(x)} home_CurrentStackLocation___unnamed_4_f80453a0(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_CurrentStackLocation___unnamed_4_f80453a0(S))} In(x, _S_CurrentStackLocation___unnamed_4_f80453a0(S)) ==> In(home_CurrentStackLocation___unnamed_4_f80453a0(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_CurrentStackLocation___unnamed_4_f80453a0(S))} In(x, _S_home_CurrentStackLocation___unnamed_4_f80453a0(S)) ==> In(CurrentStackLocation___unnamed_4_f80453a0(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_CurrentStackLocation___unnamed_4_f80453a0(S)} In(x, S) ==> In(CurrentStackLocation___unnamed_4_f80453a0(x), _S_CurrentStackLocation___unnamed_4_f80453a0(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_CurrentStackLocation___unnamed_4_f80453a0(S)} In(x, S) ==> In(home_CurrentStackLocation___unnamed_4_f80453a0(x), _S_home_CurrentStackLocation___unnamed_4_f80453a0(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_CurrentStackLocation___unnamed_4_f80453a0(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_CurrentStackLocation___unnamed_4_f80453a0(x));





function DeviceExtension__DEVICE_OBJECT(ptr) returns (ptr);
function home_DeviceExtension__DEVICE_OBJECT(ptr) returns (ptr);
function _S_DeviceExtension__DEVICE_OBJECT([ptr]bool) returns ([ptr]bool);
function _S_home_DeviceExtension__DEVICE_OBJECT([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {DeviceExtension__DEVICE_OBJECT(x)} home_DeviceExtension__DEVICE_OBJECT(DeviceExtension__DEVICE_OBJECT(x)) == x);
axiom (forall x:ptr :: {home_DeviceExtension__DEVICE_OBJECT(x)} DeviceExtension__DEVICE_OBJECT(home_DeviceExtension__DEVICE_OBJECT(x)) == x);
axiom (forall x:ptr :: {DeviceExtension__DEVICE_OBJECT(x)} DeviceExtension__DEVICE_OBJECT(x) == Ptr(Obj(x), Off(x) + 40));
axiom (forall x:ptr :: {home_DeviceExtension__DEVICE_OBJECT(x)} home_DeviceExtension__DEVICE_OBJECT(x) == Ptr(Obj(x), Off(x) - 40));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_DeviceExtension__DEVICE_OBJECT(S))} In(x, _S_DeviceExtension__DEVICE_OBJECT(S)) ==> In(home_DeviceExtension__DEVICE_OBJECT(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_DeviceExtension__DEVICE_OBJECT(S))} In(x, _S_home_DeviceExtension__DEVICE_OBJECT(S)) ==> In(DeviceExtension__DEVICE_OBJECT(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_DeviceExtension__DEVICE_OBJECT(S)} In(x, S) ==> In(DeviceExtension__DEVICE_OBJECT(x), _S_DeviceExtension__DEVICE_OBJECT(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_DeviceExtension__DEVICE_OBJECT(S)} In(x, S) ==> In(home_DeviceExtension__DEVICE_OBJECT(x), _S_home_DeviceExtension__DEVICE_OBJECT(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,40), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,40), 1) == home_DeviceExtension__DEVICE_OBJECT(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,40))} MINUS_LEFT_PTR(x, 1, Ptr(null,40)) == home_DeviceExtension__DEVICE_OBJECT(x));





function DeviceObject__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_DeviceObject__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_DeviceObject__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_DeviceObject__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {DeviceObject__DISKETTE_EXTENSION(x)} home_DeviceObject__DISKETTE_EXTENSION(DeviceObject__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_DeviceObject__DISKETTE_EXTENSION(x)} DeviceObject__DISKETTE_EXTENSION(home_DeviceObject__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {DeviceObject__DISKETTE_EXTENSION(x)} DeviceObject__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 28));
axiom (forall x:ptr :: {home_DeviceObject__DISKETTE_EXTENSION(x)} home_DeviceObject__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 28));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_DeviceObject__DISKETTE_EXTENSION(S))} In(x, _S_DeviceObject__DISKETTE_EXTENSION(S)) ==> In(home_DeviceObject__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_DeviceObject__DISKETTE_EXTENSION(S))} In(x, _S_home_DeviceObject__DISKETTE_EXTENSION(S)) ==> In(DeviceObject__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_DeviceObject__DISKETTE_EXTENSION(S)} In(x, S) ==> In(DeviceObject__DISKETTE_EXTENSION(x), _S_DeviceObject__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_DeviceObject__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_DeviceObject__DISKETTE_EXTENSION(x), _S_home_DeviceObject__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,28), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,28), 1) == home_DeviceObject__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,28))} MINUS_LEFT_PTR(x, 1, Ptr(null,28)) == home_DeviceObject__DISKETTE_EXTENSION(x));





function FlCancelSpinLock__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_FlCancelSpinLock__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_FlCancelSpinLock__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_FlCancelSpinLock__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {FlCancelSpinLock__DISKETTE_EXTENSION(x)} home_FlCancelSpinLock__DISKETTE_EXTENSION(FlCancelSpinLock__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_FlCancelSpinLock__DISKETTE_EXTENSION(x)} FlCancelSpinLock__DISKETTE_EXTENSION(home_FlCancelSpinLock__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {FlCancelSpinLock__DISKETTE_EXTENSION(x)} FlCancelSpinLock__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_FlCancelSpinLock__DISKETTE_EXTENSION(x)} home_FlCancelSpinLock__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_FlCancelSpinLock__DISKETTE_EXTENSION(S))} In(x, _S_FlCancelSpinLock__DISKETTE_EXTENSION(S)) ==> In(home_FlCancelSpinLock__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_FlCancelSpinLock__DISKETTE_EXTENSION(S))} In(x, _S_home_FlCancelSpinLock__DISKETTE_EXTENSION(S)) ==> In(FlCancelSpinLock__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_FlCancelSpinLock__DISKETTE_EXTENSION(S)} In(x, S) ==> In(FlCancelSpinLock__DISKETTE_EXTENSION(x), _S_FlCancelSpinLock__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_FlCancelSpinLock__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_FlCancelSpinLock__DISKETTE_EXTENSION(x), _S_home_FlCancelSpinLock__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_FlCancelSpinLock__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_FlCancelSpinLock__DISKETTE_EXTENSION(x));





function HoldNewReqMutex__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_HoldNewReqMutex__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_HoldNewReqMutex__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_HoldNewReqMutex__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {HoldNewReqMutex__DISKETTE_EXTENSION(x)} home_HoldNewReqMutex__DISKETTE_EXTENSION(HoldNewReqMutex__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_HoldNewReqMutex__DISKETTE_EXTENSION(x)} HoldNewReqMutex__DISKETTE_EXTENSION(home_HoldNewReqMutex__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {HoldNewReqMutex__DISKETTE_EXTENSION(x)} HoldNewReqMutex__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 316));
axiom (forall x:ptr :: {home_HoldNewReqMutex__DISKETTE_EXTENSION(x)} home_HoldNewReqMutex__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 316));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_HoldNewReqMutex__DISKETTE_EXTENSION(S))} In(x, _S_HoldNewReqMutex__DISKETTE_EXTENSION(S)) ==> In(home_HoldNewReqMutex__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_HoldNewReqMutex__DISKETTE_EXTENSION(S))} In(x, _S_home_HoldNewReqMutex__DISKETTE_EXTENSION(S)) ==> In(HoldNewReqMutex__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_HoldNewReqMutex__DISKETTE_EXTENSION(S)} In(x, S) ==> In(HoldNewReqMutex__DISKETTE_EXTENSION(x), _S_HoldNewReqMutex__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_HoldNewReqMutex__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_HoldNewReqMutex__DISKETTE_EXTENSION(x), _S_home_HoldNewReqMutex__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,316), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,316), 1) == home_HoldNewReqMutex__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,316))} MINUS_LEFT_PTR(x, 1, Ptr(null,316)) == home_HoldNewReqMutex__DISKETTE_EXTENSION(x));





function HoldNewRequests__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_HoldNewRequests__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_HoldNewRequests__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_HoldNewRequests__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {HoldNewRequests__DISKETTE_EXTENSION(x)} home_HoldNewRequests__DISKETTE_EXTENSION(HoldNewRequests__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_HoldNewRequests__DISKETTE_EXTENSION(x)} HoldNewRequests__DISKETTE_EXTENSION(home_HoldNewRequests__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {HoldNewRequests__DISKETTE_EXTENSION(x)} HoldNewRequests__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 14));
axiom (forall x:ptr :: {home_HoldNewRequests__DISKETTE_EXTENSION(x)} home_HoldNewRequests__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 14));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_HoldNewRequests__DISKETTE_EXTENSION(S))} In(x, _S_HoldNewRequests__DISKETTE_EXTENSION(S)) ==> In(home_HoldNewRequests__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_HoldNewRequests__DISKETTE_EXTENSION(S))} In(x, _S_home_HoldNewRequests__DISKETTE_EXTENSION(S)) ==> In(HoldNewRequests__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_HoldNewRequests__DISKETTE_EXTENSION(S)} In(x, S) ==> In(HoldNewRequests__DISKETTE_EXTENSION(x), _S_HoldNewRequests__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_HoldNewRequests__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_HoldNewRequests__DISKETTE_EXTENSION(x), _S_home_HoldNewRequests__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,14), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,14), 1) == home_HoldNewRequests__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,14))} MINUS_LEFT_PTR(x, 1, Ptr(null,14)) == home_HoldNewRequests__DISKETTE_EXTENSION(x));





function Information__IO_STATUS_BLOCK(ptr) returns (ptr);
function home_Information__IO_STATUS_BLOCK(ptr) returns (ptr);
function _S_Information__IO_STATUS_BLOCK([ptr]bool) returns ([ptr]bool);
function _S_home_Information__IO_STATUS_BLOCK([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Information__IO_STATUS_BLOCK(x)} home_Information__IO_STATUS_BLOCK(Information__IO_STATUS_BLOCK(x)) == x);
axiom (forall x:ptr :: {home_Information__IO_STATUS_BLOCK(x)} Information__IO_STATUS_BLOCK(home_Information__IO_STATUS_BLOCK(x)) == x);
axiom (forall x:ptr :: {Information__IO_STATUS_BLOCK(x)} Information__IO_STATUS_BLOCK(x) == Ptr(Obj(x), Off(x) + 4));
axiom (forall x:ptr :: {home_Information__IO_STATUS_BLOCK(x)} home_Information__IO_STATUS_BLOCK(x) == Ptr(Obj(x), Off(x) - 4));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Information__IO_STATUS_BLOCK(S))} In(x, _S_Information__IO_STATUS_BLOCK(S)) ==> In(home_Information__IO_STATUS_BLOCK(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Information__IO_STATUS_BLOCK(S))} In(x, _S_home_Information__IO_STATUS_BLOCK(S)) ==> In(Information__IO_STATUS_BLOCK(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Information__IO_STATUS_BLOCK(S)} In(x, S) ==> In(Information__IO_STATUS_BLOCK(x), _S_Information__IO_STATUS_BLOCK(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Information__IO_STATUS_BLOCK(S)} In(x, S) ==> In(home_Information__IO_STATUS_BLOCK(x), _S_home_Information__IO_STATUS_BLOCK(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,4), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,4), 1) == home_Information__IO_STATUS_BLOCK(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,4))} MINUS_LEFT_PTR(x, 1, Ptr(null,4)) == home_Information__IO_STATUS_BLOCK(x));





function IoStatus__IRP(ptr) returns (ptr);
function home_IoStatus__IRP(ptr) returns (ptr);
function _S_IoStatus__IRP([ptr]bool) returns ([ptr]bool);
function _S_home_IoStatus__IRP([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {IoStatus__IRP(x)} home_IoStatus__IRP(IoStatus__IRP(x)) == x);
axiom (forall x:ptr :: {home_IoStatus__IRP(x)} IoStatus__IRP(home_IoStatus__IRP(x)) == x);
axiom (forall x:ptr :: {IoStatus__IRP(x)} IoStatus__IRP(x) == Ptr(Obj(x), Off(x) + 24));
axiom (forall x:ptr :: {home_IoStatus__IRP(x)} home_IoStatus__IRP(x) == Ptr(Obj(x), Off(x) - 24));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_IoStatus__IRP(S))} In(x, _S_IoStatus__IRP(S)) ==> In(home_IoStatus__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_IoStatus__IRP(S))} In(x, _S_home_IoStatus__IRP(S)) ==> In(IoStatus__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_IoStatus__IRP(S)} In(x, S) ==> In(IoStatus__IRP(x), _S_IoStatus__IRP(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_IoStatus__IRP(S)} In(x, S) ==> In(home_IoStatus__IRP(x), _S_home_IoStatus__IRP(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,24), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,24), 1) == home_IoStatus__IRP(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,24))} MINUS_LEFT_PTR(x, 1, Ptr(null,24)) == home_IoStatus__IRP(x));





function IsRemoved__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_IsRemoved__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_IsRemoved__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_IsRemoved__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {IsRemoved__DISKETTE_EXTENSION(x)} home_IsRemoved__DISKETTE_EXTENSION(IsRemoved__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_IsRemoved__DISKETTE_EXTENSION(x)} IsRemoved__DISKETTE_EXTENSION(home_IsRemoved__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {IsRemoved__DISKETTE_EXTENSION(x)} IsRemoved__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 13));
axiom (forall x:ptr :: {home_IsRemoved__DISKETTE_EXTENSION(x)} home_IsRemoved__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 13));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_IsRemoved__DISKETTE_EXTENSION(S))} In(x, _S_IsRemoved__DISKETTE_EXTENSION(S)) ==> In(home_IsRemoved__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_IsRemoved__DISKETTE_EXTENSION(S))} In(x, _S_home_IsRemoved__DISKETTE_EXTENSION(S)) ==> In(IsRemoved__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_IsRemoved__DISKETTE_EXTENSION(S)} In(x, S) ==> In(IsRemoved__DISKETTE_EXTENSION(x), _S_IsRemoved__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_IsRemoved__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_IsRemoved__DISKETTE_EXTENSION(x), _S_home_IsRemoved__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,13), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,13), 1) == home_IsRemoved__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,13))} MINUS_LEFT_PTR(x, 1, Ptr(null,13)) == home_IsRemoved__DISKETTE_EXTENSION(x));





function IsStarted__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_IsStarted__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_IsStarted__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_IsStarted__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {IsStarted__DISKETTE_EXTENSION(x)} home_IsStarted__DISKETTE_EXTENSION(IsStarted__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_IsStarted__DISKETTE_EXTENSION(x)} IsStarted__DISKETTE_EXTENSION(home_IsStarted__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {IsStarted__DISKETTE_EXTENSION(x)} IsStarted__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 12));
axiom (forall x:ptr :: {home_IsStarted__DISKETTE_EXTENSION(x)} home_IsStarted__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 12));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_IsStarted__DISKETTE_EXTENSION(S))} In(x, _S_IsStarted__DISKETTE_EXTENSION(S)) ==> In(home_IsStarted__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_IsStarted__DISKETTE_EXTENSION(S))} In(x, _S_home_IsStarted__DISKETTE_EXTENSION(S)) ==> In(IsStarted__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_IsStarted__DISKETTE_EXTENSION(S)} In(x, S) ==> In(IsStarted__DISKETTE_EXTENSION(x), _S_IsStarted__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_IsStarted__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_IsStarted__DISKETTE_EXTENSION(x), _S_home_IsStarted__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,12), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,12), 1) == home_IsStarted__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,12))} MINUS_LEFT_PTR(x, 1, Ptr(null,12)) == home_IsStarted__DISKETTE_EXTENSION(x));





function Length___unnamed_16_39e6661e(ptr) returns (ptr);
function home_Length___unnamed_16_39e6661e(ptr) returns (ptr);
function _S_Length___unnamed_16_39e6661e([ptr]bool) returns ([ptr]bool);
function _S_home_Length___unnamed_16_39e6661e([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Length___unnamed_16_39e6661e(x)} home_Length___unnamed_16_39e6661e(Length___unnamed_16_39e6661e(x)) == x);
axiom (forall x:ptr :: {home_Length___unnamed_16_39e6661e(x)} Length___unnamed_16_39e6661e(home_Length___unnamed_16_39e6661e(x)) == x);
axiom (forall x:ptr :: {Length___unnamed_16_39e6661e(x)} Length___unnamed_16_39e6661e(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_Length___unnamed_16_39e6661e(x)} home_Length___unnamed_16_39e6661e(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Length___unnamed_16_39e6661e(S))} In(x, _S_Length___unnamed_16_39e6661e(S)) ==> In(home_Length___unnamed_16_39e6661e(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Length___unnamed_16_39e6661e(S))} In(x, _S_home_Length___unnamed_16_39e6661e(S)) ==> In(Length___unnamed_16_39e6661e(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Length___unnamed_16_39e6661e(S)} In(x, S) ==> In(Length___unnamed_16_39e6661e(x), _S_Length___unnamed_16_39e6661e(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Length___unnamed_16_39e6661e(S)} In(x, S) ==> In(home_Length___unnamed_16_39e6661e(x), _S_home_Length___unnamed_16_39e6661e(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_Length___unnamed_16_39e6661e(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_Length___unnamed_16_39e6661e(x));





function ListEntry___unnamed_12_003c1454(ptr) returns (ptr);
function home_ListEntry___unnamed_12_003c1454(ptr) returns (ptr);
function _S_ListEntry___unnamed_12_003c1454([ptr]bool) returns ([ptr]bool);
function _S_home_ListEntry___unnamed_12_003c1454([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {ListEntry___unnamed_12_003c1454(x)} home_ListEntry___unnamed_12_003c1454(ListEntry___unnamed_12_003c1454(x)) == x);
axiom (forall x:ptr :: {home_ListEntry___unnamed_12_003c1454(x)} ListEntry___unnamed_12_003c1454(home_ListEntry___unnamed_12_003c1454(x)) == x);
axiom (forall x:ptr :: {ListEntry___unnamed_12_003c1454(x)} ListEntry___unnamed_12_003c1454(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_ListEntry___unnamed_12_003c1454(x)} home_ListEntry___unnamed_12_003c1454(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_ListEntry___unnamed_12_003c1454(S))} In(x, _S_ListEntry___unnamed_12_003c1454(S)) ==> In(home_ListEntry___unnamed_12_003c1454(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_ListEntry___unnamed_12_003c1454(S))} In(x, _S_home_ListEntry___unnamed_12_003c1454(S)) ==> In(ListEntry___unnamed_12_003c1454(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_ListEntry___unnamed_12_003c1454(S)} In(x, S) ==> In(ListEntry___unnamed_12_003c1454(x), _S_ListEntry___unnamed_12_003c1454(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_ListEntry___unnamed_12_003c1454(S)} In(x, S) ==> In(home_ListEntry___unnamed_12_003c1454(x), _S_home_ListEntry___unnamed_12_003c1454(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_ListEntry___unnamed_12_003c1454(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_ListEntry___unnamed_12_003c1454(x));





function ListSpinLock__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_ListSpinLock__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_ListSpinLock__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_ListSpinLock__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {ListSpinLock__DISKETTE_EXTENSION(x)} home_ListSpinLock__DISKETTE_EXTENSION(ListSpinLock__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_ListSpinLock__DISKETTE_EXTENSION(x)} ListSpinLock__DISKETTE_EXTENSION(home_ListSpinLock__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {ListSpinLock__DISKETTE_EXTENSION(x)} ListSpinLock__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 52));
axiom (forall x:ptr :: {home_ListSpinLock__DISKETTE_EXTENSION(x)} home_ListSpinLock__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 52));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_ListSpinLock__DISKETTE_EXTENSION(S))} In(x, _S_ListSpinLock__DISKETTE_EXTENSION(S)) ==> In(home_ListSpinLock__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_ListSpinLock__DISKETTE_EXTENSION(S))} In(x, _S_home_ListSpinLock__DISKETTE_EXTENSION(S)) ==> In(ListSpinLock__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_ListSpinLock__DISKETTE_EXTENSION(S)} In(x, S) ==> In(ListSpinLock__DISKETTE_EXTENSION(x), _S_ListSpinLock__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_ListSpinLock__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_ListSpinLock__DISKETTE_EXTENSION(x), _S_home_ListSpinLock__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,52), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,52), 1) == home_ListSpinLock__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,52))} MINUS_LEFT_PTR(x, 1, Ptr(null,52)) == home_ListSpinLock__DISKETTE_EXTENSION(x));





function LowPart___unnamed_8_34582070(ptr) returns (ptr);
function home_LowPart___unnamed_8_34582070(ptr) returns (ptr);
function _S_LowPart___unnamed_8_34582070([ptr]bool) returns ([ptr]bool);
function _S_home_LowPart___unnamed_8_34582070([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {LowPart___unnamed_8_34582070(x)} home_LowPart___unnamed_8_34582070(LowPart___unnamed_8_34582070(x)) == x);
axiom (forall x:ptr :: {home_LowPart___unnamed_8_34582070(x)} LowPart___unnamed_8_34582070(home_LowPart___unnamed_8_34582070(x)) == x);
axiom (forall x:ptr :: {LowPart___unnamed_8_34582070(x)} LowPart___unnamed_8_34582070(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_LowPart___unnamed_8_34582070(x)} home_LowPart___unnamed_8_34582070(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_LowPart___unnamed_8_34582070(S))} In(x, _S_LowPart___unnamed_8_34582070(S)) ==> In(home_LowPart___unnamed_8_34582070(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_LowPart___unnamed_8_34582070(S))} In(x, _S_home_LowPart___unnamed_8_34582070(S)) ==> In(LowPart___unnamed_8_34582070(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_LowPart___unnamed_8_34582070(S)} In(x, S) ==> In(LowPart___unnamed_8_34582070(x), _S_LowPart___unnamed_8_34582070(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_LowPart___unnamed_8_34582070(S)} In(x, S) ==> In(home_LowPart___unnamed_8_34582070(x), _S_home_LowPart___unnamed_8_34582070(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_LowPart___unnamed_8_34582070(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_LowPart___unnamed_8_34582070(x));





function MediaType__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_MediaType__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_MediaType__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_MediaType__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {MediaType__DISKETTE_EXTENSION(x)} home_MediaType__DISKETTE_EXTENSION(MediaType__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_MediaType__DISKETTE_EXTENSION(x)} MediaType__DISKETTE_EXTENSION(home_MediaType__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {MediaType__DISKETTE_EXTENSION(x)} MediaType__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 156));
axiom (forall x:ptr :: {home_MediaType__DISKETTE_EXTENSION(x)} home_MediaType__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 156));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_MediaType__DISKETTE_EXTENSION(S))} In(x, _S_MediaType__DISKETTE_EXTENSION(S)) ==> In(home_MediaType__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_MediaType__DISKETTE_EXTENSION(S))} In(x, _S_home_MediaType__DISKETTE_EXTENSION(S)) ==> In(MediaType__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_MediaType__DISKETTE_EXTENSION(S)} In(x, S) ==> In(MediaType__DISKETTE_EXTENSION(x), _S_MediaType__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_MediaType__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_MediaType__DISKETTE_EXTENSION(x), _S_home_MediaType__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,156), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,156), 1) == home_MediaType__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,156))} MINUS_LEFT_PTR(x, 1, Ptr(null,156)) == home_MediaType__DISKETTE_EXTENSION(x));





function NewRequestQueueSpinLock__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_NewRequestQueueSpinLock__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_NewRequestQueueSpinLock__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {NewRequestQueueSpinLock__DISKETTE_EXTENSION(x)} home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(NewRequestQueueSpinLock__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x)} NewRequestQueueSpinLock__DISKETTE_EXTENSION(home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {NewRequestQueueSpinLock__DISKETTE_EXTENSION(x)} NewRequestQueueSpinLock__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 24));
axiom (forall x:ptr :: {home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x)} home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 24));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S))} In(x, _S_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S)) ==> In(home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S))} In(x, _S_home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S)) ==> In(NewRequestQueueSpinLock__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S)} In(x, S) ==> In(NewRequestQueueSpinLock__DISKETTE_EXTENSION(x), _S_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x), _S_home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,24), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,24), 1) == home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,24))} MINUS_LEFT_PTR(x, 1, Ptr(null,24)) == home_NewRequestQueueSpinLock__DISKETTE_EXTENSION(x));





function NewRequestQueue__DISKETTE_EXTENSION(ptr) returns (ptr);
function home_NewRequestQueue__DISKETTE_EXTENSION(ptr) returns (ptr);
function _S_NewRequestQueue__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);
function _S_home_NewRequestQueue__DISKETTE_EXTENSION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {NewRequestQueue__DISKETTE_EXTENSION(x)} home_NewRequestQueue__DISKETTE_EXTENSION(NewRequestQueue__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {home_NewRequestQueue__DISKETTE_EXTENSION(x)} NewRequestQueue__DISKETTE_EXTENSION(home_NewRequestQueue__DISKETTE_EXTENSION(x)) == x);
axiom (forall x:ptr :: {NewRequestQueue__DISKETTE_EXTENSION(x)} NewRequestQueue__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) + 16));
axiom (forall x:ptr :: {home_NewRequestQueue__DISKETTE_EXTENSION(x)} home_NewRequestQueue__DISKETTE_EXTENSION(x) == Ptr(Obj(x), Off(x) - 16));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_NewRequestQueue__DISKETTE_EXTENSION(S))} In(x, _S_NewRequestQueue__DISKETTE_EXTENSION(S)) ==> In(home_NewRequestQueue__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_NewRequestQueue__DISKETTE_EXTENSION(S))} In(x, _S_home_NewRequestQueue__DISKETTE_EXTENSION(S)) ==> In(NewRequestQueue__DISKETTE_EXTENSION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_NewRequestQueue__DISKETTE_EXTENSION(S)} In(x, S) ==> In(NewRequestQueue__DISKETTE_EXTENSION(x), _S_NewRequestQueue__DISKETTE_EXTENSION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_NewRequestQueue__DISKETTE_EXTENSION(S)} In(x, S) ==> In(home_NewRequestQueue__DISKETTE_EXTENSION(x), _S_home_NewRequestQueue__DISKETTE_EXTENSION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,16), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,16), 1) == home_NewRequestQueue__DISKETTE_EXTENSION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,16))} MINUS_LEFT_PTR(x, 1, Ptr(null,16)) == home_NewRequestQueue__DISKETTE_EXTENSION(x));





function Overlay___unnamed_48_c27ef811(ptr) returns (ptr);
function home_Overlay___unnamed_48_c27ef811(ptr) returns (ptr);
function _S_Overlay___unnamed_48_c27ef811([ptr]bool) returns ([ptr]bool);
function _S_home_Overlay___unnamed_48_c27ef811([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Overlay___unnamed_48_c27ef811(x)} home_Overlay___unnamed_48_c27ef811(Overlay___unnamed_48_c27ef811(x)) == x);
axiom (forall x:ptr :: {home_Overlay___unnamed_48_c27ef811(x)} Overlay___unnamed_48_c27ef811(home_Overlay___unnamed_48_c27ef811(x)) == x);
axiom (forall x:ptr :: {Overlay___unnamed_48_c27ef811(x)} Overlay___unnamed_48_c27ef811(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_Overlay___unnamed_48_c27ef811(x)} home_Overlay___unnamed_48_c27ef811(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Overlay___unnamed_48_c27ef811(S))} In(x, _S_Overlay___unnamed_48_c27ef811(S)) ==> In(home_Overlay___unnamed_48_c27ef811(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Overlay___unnamed_48_c27ef811(S))} In(x, _S_home_Overlay___unnamed_48_c27ef811(S)) ==> In(Overlay___unnamed_48_c27ef811(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Overlay___unnamed_48_c27ef811(S)} In(x, S) ==> In(Overlay___unnamed_48_c27ef811(x), _S_Overlay___unnamed_48_c27ef811(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Overlay___unnamed_48_c27ef811(S)} In(x, S) ==> In(home_Overlay___unnamed_48_c27ef811(x), _S_home_Overlay___unnamed_48_c27ef811(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_Overlay___unnamed_48_c27ef811(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_Overlay___unnamed_48_c27ef811(x));





function Parameters__IO_STACK_LOCATION(ptr) returns (ptr);
function home_Parameters__IO_STACK_LOCATION(ptr) returns (ptr);
function _S_Parameters__IO_STACK_LOCATION([ptr]bool) returns ([ptr]bool);
function _S_home_Parameters__IO_STACK_LOCATION([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Parameters__IO_STACK_LOCATION(x)} home_Parameters__IO_STACK_LOCATION(Parameters__IO_STACK_LOCATION(x)) == x);
axiom (forall x:ptr :: {home_Parameters__IO_STACK_LOCATION(x)} Parameters__IO_STACK_LOCATION(home_Parameters__IO_STACK_LOCATION(x)) == x);
axiom (forall x:ptr :: {Parameters__IO_STACK_LOCATION(x)} Parameters__IO_STACK_LOCATION(x) == Ptr(Obj(x), Off(x) + 4));
axiom (forall x:ptr :: {home_Parameters__IO_STACK_LOCATION(x)} home_Parameters__IO_STACK_LOCATION(x) == Ptr(Obj(x), Off(x) - 4));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Parameters__IO_STACK_LOCATION(S))} In(x, _S_Parameters__IO_STACK_LOCATION(S)) ==> In(home_Parameters__IO_STACK_LOCATION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Parameters__IO_STACK_LOCATION(S))} In(x, _S_home_Parameters__IO_STACK_LOCATION(S)) ==> In(Parameters__IO_STACK_LOCATION(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Parameters__IO_STACK_LOCATION(S)} In(x, S) ==> In(Parameters__IO_STACK_LOCATION(x), _S_Parameters__IO_STACK_LOCATION(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Parameters__IO_STACK_LOCATION(S)} In(x, S) ==> In(home_Parameters__IO_STACK_LOCATION(x), _S_home_Parameters__IO_STACK_LOCATION(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,4), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,4), 1) == home_Parameters__IO_STACK_LOCATION(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,4))} MINUS_LEFT_PTR(x, 1, Ptr(null,4)) == home_Parameters__IO_STACK_LOCATION(x));





function Read___unnamed_16_c0f0e7de(ptr) returns (ptr);
function home_Read___unnamed_16_c0f0e7de(ptr) returns (ptr);
function _S_Read___unnamed_16_c0f0e7de([ptr]bool) returns ([ptr]bool);
function _S_home_Read___unnamed_16_c0f0e7de([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Read___unnamed_16_c0f0e7de(x)} home_Read___unnamed_16_c0f0e7de(Read___unnamed_16_c0f0e7de(x)) == x);
axiom (forall x:ptr :: {home_Read___unnamed_16_c0f0e7de(x)} Read___unnamed_16_c0f0e7de(home_Read___unnamed_16_c0f0e7de(x)) == x);
axiom (forall x:ptr :: {Read___unnamed_16_c0f0e7de(x)} Read___unnamed_16_c0f0e7de(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_Read___unnamed_16_c0f0e7de(x)} home_Read___unnamed_16_c0f0e7de(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Read___unnamed_16_c0f0e7de(S))} In(x, _S_Read___unnamed_16_c0f0e7de(S)) ==> In(home_Read___unnamed_16_c0f0e7de(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Read___unnamed_16_c0f0e7de(S))} In(x, _S_home_Read___unnamed_16_c0f0e7de(S)) ==> In(Read___unnamed_16_c0f0e7de(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Read___unnamed_16_c0f0e7de(S)} In(x, S) ==> In(Read___unnamed_16_c0f0e7de(x), _S_Read___unnamed_16_c0f0e7de(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Read___unnamed_16_c0f0e7de(S)} In(x, S) ==> In(home_Read___unnamed_16_c0f0e7de(x), _S_home_Read___unnamed_16_c0f0e7de(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_Read___unnamed_16_c0f0e7de(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_Read___unnamed_16_c0f0e7de(x));





function Status___unnamed_4_c7b3d275(ptr) returns (ptr);
function home_Status___unnamed_4_c7b3d275(ptr) returns (ptr);
function _S_Status___unnamed_4_c7b3d275([ptr]bool) returns ([ptr]bool);
function _S_home_Status___unnamed_4_c7b3d275([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Status___unnamed_4_c7b3d275(x)} home_Status___unnamed_4_c7b3d275(Status___unnamed_4_c7b3d275(x)) == x);
axiom (forall x:ptr :: {home_Status___unnamed_4_c7b3d275(x)} Status___unnamed_4_c7b3d275(home_Status___unnamed_4_c7b3d275(x)) == x);
axiom (forall x:ptr :: {Status___unnamed_4_c7b3d275(x)} Status___unnamed_4_c7b3d275(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home_Status___unnamed_4_c7b3d275(x)} home_Status___unnamed_4_c7b3d275(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Status___unnamed_4_c7b3d275(S))} In(x, _S_Status___unnamed_4_c7b3d275(S)) ==> In(home_Status___unnamed_4_c7b3d275(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Status___unnamed_4_c7b3d275(S))} In(x, _S_home_Status___unnamed_4_c7b3d275(S)) ==> In(Status___unnamed_4_c7b3d275(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Status___unnamed_4_c7b3d275(S)} In(x, S) ==> In(Status___unnamed_4_c7b3d275(x), _S_Status___unnamed_4_c7b3d275(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Status___unnamed_4_c7b3d275(S)} In(x, S) ==> In(home_Status___unnamed_4_c7b3d275(x), _S_home_Status___unnamed_4_c7b3d275(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home_Status___unnamed_4_c7b3d275(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home_Status___unnamed_4_c7b3d275(x));





function Tail__IRP(ptr) returns (ptr);
function home_Tail__IRP(ptr) returns (ptr);
function _S_Tail__IRP([ptr]bool) returns ([ptr]bool);
function _S_home_Tail__IRP([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {Tail__IRP(x)} home_Tail__IRP(Tail__IRP(x)) == x);
axiom (forall x:ptr :: {home_Tail__IRP(x)} Tail__IRP(home_Tail__IRP(x)) == x);
axiom (forall x:ptr :: {Tail__IRP(x)} Tail__IRP(x) == Ptr(Obj(x), Off(x) + 64));
axiom (forall x:ptr :: {home_Tail__IRP(x)} home_Tail__IRP(x) == Ptr(Obj(x), Off(x) - 64));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_Tail__IRP(S))} In(x, _S_Tail__IRP(S)) ==> In(home_Tail__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home_Tail__IRP(S))} In(x, _S_home_Tail__IRP(S)) ==> In(Tail__IRP(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_Tail__IRP(S)} In(x, S) ==> In(Tail__IRP(x), _S_Tail__IRP(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home_Tail__IRP(S)} In(x, S) ==> In(home_Tail__IRP(x), _S_home_Tail__IRP(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,64), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,64), 1) == home_Tail__IRP(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,64))} MINUS_LEFT_PTR(x, 1, Ptr(null,64)) == home_Tail__IRP(x));





function __unnamed_12_003c1454___unnamed_40_6ef75b20(ptr) returns (ptr);
function home___unnamed_12_003c1454___unnamed_40_6ef75b20(ptr) returns (ptr);
function _S___unnamed_12_003c1454___unnamed_40_6ef75b20([ptr]bool) returns ([ptr]bool);
function _S_home___unnamed_12_003c1454___unnamed_40_6ef75b20([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {__unnamed_12_003c1454___unnamed_40_6ef75b20(x)} home___unnamed_12_003c1454___unnamed_40_6ef75b20(__unnamed_12_003c1454___unnamed_40_6ef75b20(x)) == x);
axiom (forall x:ptr :: {home___unnamed_12_003c1454___unnamed_40_6ef75b20(x)} __unnamed_12_003c1454___unnamed_40_6ef75b20(home___unnamed_12_003c1454___unnamed_40_6ef75b20(x)) == x);
axiom (forall x:ptr :: {__unnamed_12_003c1454___unnamed_40_6ef75b20(x)} __unnamed_12_003c1454___unnamed_40_6ef75b20(x) == Ptr(Obj(x), Off(x) + 24));
axiom (forall x:ptr :: {home___unnamed_12_003c1454___unnamed_40_6ef75b20(x)} home___unnamed_12_003c1454___unnamed_40_6ef75b20(x) == Ptr(Obj(x), Off(x) - 24));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S___unnamed_12_003c1454___unnamed_40_6ef75b20(S))} In(x, _S___unnamed_12_003c1454___unnamed_40_6ef75b20(S)) ==> In(home___unnamed_12_003c1454___unnamed_40_6ef75b20(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home___unnamed_12_003c1454___unnamed_40_6ef75b20(S))} In(x, _S_home___unnamed_12_003c1454___unnamed_40_6ef75b20(S)) ==> In(__unnamed_12_003c1454___unnamed_40_6ef75b20(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S___unnamed_12_003c1454___unnamed_40_6ef75b20(S)} In(x, S) ==> In(__unnamed_12_003c1454___unnamed_40_6ef75b20(x), _S___unnamed_12_003c1454___unnamed_40_6ef75b20(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home___unnamed_12_003c1454___unnamed_40_6ef75b20(S)} In(x, S) ==> In(home___unnamed_12_003c1454___unnamed_40_6ef75b20(x), _S_home___unnamed_12_003c1454___unnamed_40_6ef75b20(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,24), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,24), 1) == home___unnamed_12_003c1454___unnamed_40_6ef75b20(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,24))} MINUS_LEFT_PTR(x, 1, Ptr(null,24)) == home___unnamed_12_003c1454___unnamed_40_6ef75b20(x));





function __unnamed_4_c7b3d275__IO_STATUS_BLOCK(ptr) returns (ptr);
function home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(ptr) returns (ptr);
function _S___unnamed_4_c7b3d275__IO_STATUS_BLOCK([ptr]bool) returns ([ptr]bool);
function _S_home___unnamed_4_c7b3d275__IO_STATUS_BLOCK([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {__unnamed_4_c7b3d275__IO_STATUS_BLOCK(x)} home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(x)) == x);
axiom (forall x:ptr :: {home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x)} __unnamed_4_c7b3d275__IO_STATUS_BLOCK(home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x)) == x);
axiom (forall x:ptr :: {__unnamed_4_c7b3d275__IO_STATUS_BLOCK(x)} __unnamed_4_c7b3d275__IO_STATUS_BLOCK(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x)} home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S))} In(x, _S___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S)) ==> In(home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S))} In(x, _S_home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S)) ==> In(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S)} In(x, S) ==> In(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(x), _S___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S)} In(x, S) ==> In(home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x), _S_home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home___unnamed_4_c7b3d275__IO_STATUS_BLOCK(x));





function __unnamed_4_f80453a0___unnamed_12_003c1454(ptr) returns (ptr);
function home___unnamed_4_f80453a0___unnamed_12_003c1454(ptr) returns (ptr);
function _S___unnamed_4_f80453a0___unnamed_12_003c1454([ptr]bool) returns ([ptr]bool);
function _S_home___unnamed_4_f80453a0___unnamed_12_003c1454([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {__unnamed_4_f80453a0___unnamed_12_003c1454(x)} home___unnamed_4_f80453a0___unnamed_12_003c1454(__unnamed_4_f80453a0___unnamed_12_003c1454(x)) == x);
axiom (forall x:ptr :: {home___unnamed_4_f80453a0___unnamed_12_003c1454(x)} __unnamed_4_f80453a0___unnamed_12_003c1454(home___unnamed_4_f80453a0___unnamed_12_003c1454(x)) == x);
axiom (forall x:ptr :: {__unnamed_4_f80453a0___unnamed_12_003c1454(x)} __unnamed_4_f80453a0___unnamed_12_003c1454(x) == Ptr(Obj(x), Off(x) + 8));
axiom (forall x:ptr :: {home___unnamed_4_f80453a0___unnamed_12_003c1454(x)} home___unnamed_4_f80453a0___unnamed_12_003c1454(x) == Ptr(Obj(x), Off(x) - 8));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S___unnamed_4_f80453a0___unnamed_12_003c1454(S))} In(x, _S___unnamed_4_f80453a0___unnamed_12_003c1454(S)) ==> In(home___unnamed_4_f80453a0___unnamed_12_003c1454(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home___unnamed_4_f80453a0___unnamed_12_003c1454(S))} In(x, _S_home___unnamed_4_f80453a0___unnamed_12_003c1454(S)) ==> In(__unnamed_4_f80453a0___unnamed_12_003c1454(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S___unnamed_4_f80453a0___unnamed_12_003c1454(S)} In(x, S) ==> In(__unnamed_4_f80453a0___unnamed_12_003c1454(x), _S___unnamed_4_f80453a0___unnamed_12_003c1454(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home___unnamed_4_f80453a0___unnamed_12_003c1454(S)} In(x, S) ==> In(home___unnamed_4_f80453a0___unnamed_12_003c1454(x), _S_home___unnamed_4_f80453a0___unnamed_12_003c1454(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,8), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,8), 1) == home___unnamed_4_f80453a0___unnamed_12_003c1454(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,8))} MINUS_LEFT_PTR(x, 1, Ptr(null,8)) == home___unnamed_4_f80453a0___unnamed_12_003c1454(x));





function __unnamed_8_34582070__LARGE_INTEGER(ptr) returns (ptr);
function home___unnamed_8_34582070__LARGE_INTEGER(ptr) returns (ptr);
function _S___unnamed_8_34582070__LARGE_INTEGER([ptr]bool) returns ([ptr]bool);
function _S_home___unnamed_8_34582070__LARGE_INTEGER([ptr]bool) returns ([ptr]bool);

axiom (forall x:ptr :: {__unnamed_8_34582070__LARGE_INTEGER(x)} home___unnamed_8_34582070__LARGE_INTEGER(__unnamed_8_34582070__LARGE_INTEGER(x)) == x);
axiom (forall x:ptr :: {home___unnamed_8_34582070__LARGE_INTEGER(x)} __unnamed_8_34582070__LARGE_INTEGER(home___unnamed_8_34582070__LARGE_INTEGER(x)) == x);
axiom (forall x:ptr :: {__unnamed_8_34582070__LARGE_INTEGER(x)} __unnamed_8_34582070__LARGE_INTEGER(x) == Ptr(Obj(x), Off(x) + 0));
axiom (forall x:ptr :: {home___unnamed_8_34582070__LARGE_INTEGER(x)} home___unnamed_8_34582070__LARGE_INTEGER(x) == Ptr(Obj(x), Off(x) - 0));

axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S___unnamed_8_34582070__LARGE_INTEGER(S))} In(x, _S___unnamed_8_34582070__LARGE_INTEGER(S)) ==> In(home___unnamed_8_34582070__LARGE_INTEGER(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, _S_home___unnamed_8_34582070__LARGE_INTEGER(S))} In(x, _S_home___unnamed_8_34582070__LARGE_INTEGER(S)) ==> In(__unnamed_8_34582070__LARGE_INTEGER(x), S));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S___unnamed_8_34582070__LARGE_INTEGER(S)} In(x, S) ==> In(__unnamed_8_34582070__LARGE_INTEGER(x), _S___unnamed_8_34582070__LARGE_INTEGER(S)));
axiom (forall x:ptr, S:[ptr]bool :: {In(x, S), _S_home___unnamed_8_34582070__LARGE_INTEGER(S)} In(x, S) ==> In(home___unnamed_8_34582070__LARGE_INTEGER(x), _S_home___unnamed_8_34582070__LARGE_INTEGER(S)));

axiom (forall x:ptr :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, Ptr(null,0), 1) == home___unnamed_8_34582070__LARGE_INTEGER(x));
axiom (forall x:ptr :: {MINUS_LEFT_PTR(x, 1, Ptr(null,0))} MINUS_LEFT_PTR(x, 1, Ptr(null,0)) == home___unnamed_8_34582070__LARGE_INTEGER(x));



// Axiom for null constraint
//modifying to make the signature match with old BSConstraint that constrains Mem
function BSConstraint
(
  BS:[ptr]bool,
  Mem:[ptr]ptr
) returns (bool);

axiom (
  forall
    BS:[ptr]bool, Mem:[ptr]ptr :: {BSConstraint(BS,Mem)}

  BSConstraint(BS,Mem)
  ==>
  (
    (forall i:int :: {Ptr(null,i)} BS[Ptr(null,i)])
/*
    &&

    (forall a:ptr :: {BS[a]} Element(a))
*/
  )
);
procedure __delBS(a:ptr);
requires(BS[a]);
modifies BS;
ensures(forall x:ptr :: {BS[x]} x == a || (old(BS)[x] <==> BS[x]));
ensures(!BS[a]);

procedure __addBS(a:ptr);
requires(!BS[a]);
modifies BS;
ensures(forall x:ptr :: {BS[x]} x == a || (old(BS)[x] <==> BS[x]));
ensures(BS[a]);

function MINUS_BOTH_PTR_OR_BOTH_INT(a:ptr, b:ptr, size:int) returns (ptr);
axiom(forall a:ptr, b:ptr, size:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)}
(Obj(a) == Obj(b) ==> Obj(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)) == null && size * Off(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)) == Off(a) - Off(b))
&&
(Obj(b) == null && size == 1 ==> Obj(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)) == Obj(a) && Off(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)) == Off(a) - Off(b))
&&
(Obj(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)) == null || Obj(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)) == Obj(a) || Obj(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)) == Obj(b))
);

function MINUS_LEFT_PTR(a:ptr, a_size:int, b:ptr) returns (ptr);
axiom(forall a:ptr, a_size:int, b:ptr :: {MINUS_LEFT_PTR(a,a_size,b)}
(Obj(b) == null ==> Obj(MINUS_LEFT_PTR(a,a_size,b)) == Obj(a) && Off(MINUS_LEFT_PTR(a,a_size,b)) == Off(a) - a_size * Off(b))
&&
(Obj(a) == Obj(b) && a_size == 1 ==> Obj(MINUS_LEFT_PTR(a,a_size,b)) == null && Off(MINUS_LEFT_PTR(a,a_size,b)) == Off(a) - Off(b))
&&
(Obj(MINUS_LEFT_PTR(a,a_size,b)) == null || Obj(MINUS_LEFT_PTR(a,a_size,b)) == Obj(a) || Obj(MINUS_LEFT_PTR(a,a_size,b)) == Obj(b))
);

function PLUS(a:ptr, a_size:int, b:ptr) returns (ptr);
axiom(forall a:ptr, a_size:int, b:ptr :: {PLUS(a,a_size,b)}
(Obj(b) == null ==> Obj(PLUS(a,a_size,b)) == Obj(a) && Off(PLUS(a,a_size,b)) == Off(a) + a_size * Off(b))
&&
(Obj(a) == null && a_size == 1 ==> Obj(PLUS(a,a_size,b)) == Obj(b) && Off(PLUS(a,a_size,b)) == Off(a) + Off(b))
&&
(Obj(PLUS(a,a_size,b)) == null || Obj(PLUS(a,a_size,b)) == Obj(a) || Obj(PLUS(a,a_size,b)) == Obj(b))
);

function MULT(a:ptr, b:ptr) returns (ptr);
axiom(forall a:ptr, b:ptr :: {MULT(a,b)} Obj(MULT(a,b)) == null);

function BINARY_BOTH_INT(a:ptr, b:ptr) returns (ptr);
axiom(forall a:ptr, b:ptr :: {BINARY_BOTH_INT(a,b)} Obj(BINARY_BOTH_INT(a,b)) == null);

function POW2(a:ptr) returns (bool);
axiom POW2(Ptr(null,1));
axiom POW2(Ptr(null,2));
axiom POW2(Ptr(null,4));
axiom POW2(Ptr(null,8));
axiom POW2(Ptr(null,16));
axiom POW2(Ptr(null,32));
axiom POW2(Ptr(null,64));
axiom POW2(Ptr(null,128));
axiom POW2(Ptr(null,256));
axiom POW2(Ptr(null,512));
axiom POW2(Ptr(null,1024));
axiom POW2(Ptr(null,2048));
axiom POW2(Ptr(null,4096));
axiom POW2(Ptr(null,8192));
axiom POW2(Ptr(null,16384));
axiom POW2(Ptr(null,32768));
axiom POW2(Ptr(null,65536));
axiom POW2(Ptr(null,131072));
axiom POW2(Ptr(null,262144));
axiom POW2(Ptr(null,524288));
axiom POW2(Ptr(null,1048576));
axiom POW2(Ptr(null,2097152));
axiom POW2(Ptr(null,4194304));
axiom POW2(Ptr(null,8388608));
axiom POW2(Ptr(null,16777216));
axiom POW2(Ptr(null,33554432));

axiom (forall n:int, m:int :: {Ptr(null,n),POW2(Ptr(null,m))} POW2(Ptr(null,m)) && m < n && n < 2*m ==> !POW2(Ptr(null,n)));   

function choose(a:bool, b:ptr, c:ptr) returns (x:ptr);
axiom(forall a:bool, b:ptr, c:ptr :: {choose(a,b,c)} a ==> choose(a,b,c) == b);
axiom(forall a:bool, b:ptr, c:ptr :: {choose(a,b,c)} !a ==> choose(a,b,c) == c);

function BIT_BAND(a:ptr, b:ptr) returns (x:ptr);
axiom(forall a:ptr, b:ptr :: {BIT_BAND(a,b)} Obj(BIT_BAND(a,b)) == null || Obj(BIT_BAND(a,b)) == Obj(a) || Obj(BIT_BAND(a,b)) == Obj(b));
axiom(forall a:ptr, b:ptr :: {BIT_BAND(a,b)} a == b ==> BIT_BAND(a,b) == a);
axiom(forall a:ptr, b:ptr :: {BIT_BAND(a,b)} POW2(a) && POW2(b) && a != b ==> BIT_BAND(a,b) == Ptr(null,0));
axiom(forall a:ptr, b:ptr :: {BIT_BAND(a,b)} a == Ptr(null,0) || b == Ptr(null,0) ==> BIT_BAND(a,b) == Ptr(null,0));
axiom(forall a:ptr, b:ptr, c:ptr :: {BIT_BAND(BIT_BAND(a,b),c)} BIT_BAND(BIT_BAND(a,b),c) == c <==> BIT_BAND(a,c) == c && BIT_BAND(b,c) == c);

function BIT_BOR(a:ptr, b:ptr) returns (x:ptr);
axiom(forall a:ptr, b:ptr :: {BIT_BOR(a,b)} Obj(BIT_BOR(a,b)) == null || Obj(BIT_BOR(a,b)) == Obj(a) || Obj(BIT_BOR(a,b)) == Obj(b));
axiom(forall a:ptr, b:ptr, c:ptr :: {BIT_BAND(BIT_BOR(a,b),c)} BIT_BAND(a,c) != Ptr(null,0) || BIT_BAND(b,c) != Ptr(null,0) <==> BIT_BAND(BIT_BOR(a,b),c) != Ptr(null,0));
axiom(forall n:int, m:int :: {POW2(Ptr(null,n)), POW2(Ptr(null,m))} n > 0 && POW2(Ptr(null,m)) && m < n && 2*m > n ==>
	Ptr(null, n) == BIT_BOR(Ptr(null, m), Ptr(null, n - m)));


function BIT_BXOR(a:ptr, b:ptr) returns (x:ptr);
axiom(forall a:ptr, b:ptr :: {BIT_BXOR(a,b)} Obj(BIT_BXOR(a,b)) == null || Obj(BIT_BXOR(a,b)) == Obj(a) || Obj(BIT_BXOR(a,b)) == Obj(b));

function BIT_BNOT(a:ptr) returns (ptr);
axiom(forall a:ptr, b:ptr :: {BIT_BAND(a,b)} a == BIT_BNOT(b) || b == BIT_BNOT(a) ==> BIT_BAND(a,b) == Ptr(null,0));
axiom(forall a:ptr, b:ptr :: {BIT_BNOT(BIT_BOR(a,b))}  BIT_BNOT(BIT_BOR(a,b)) == BIT_BAND(BIT_BNOT(a),BIT_BNOT(b)));
axiom(forall a:ptr, b:ptr, c:ptr :: {BIT_BAND(BIT_BAND(a,b),c)} a == BIT_BNOT(c) || b == BIT_BNOT(c) ==> BIT_BAND(BIT_BAND(a,b),c) == Ptr(null,0));
axiom(forall a:ptr, b:ptr, c:ptr :: {BIT_BAND(BIT_BAND(BIT_BNOT(a),b),c)} POW2(c) && POW2(a) && c != a ==>
			(BIT_BAND(b,c) != Ptr(null,0) <==> BIT_BAND(BIT_BAND(BIT_BNOT(a),b),c) != Ptr(null,0)));
axiom(forall a:ptr, b:ptr, c:ptr :: {BIT_BAND(BIT_BAND(a,BIT_BNOT(b)),c)} POW2(c) && POW2(b) && c != b ==>
			(BIT_BAND(a,c) != Ptr(null,0) <==> BIT_BAND(BIT_BAND(a,BIT_BNOT(b)),c) != Ptr(null,0)));


function LIFT(a:bool) returns (ptr);
axiom(forall a:bool :: {LIFT(a)} a <==> LIFT(a) != Ptr(null,0));
axiom(forall a:bool :: {LIFT(a)} Obj(LIFT(a)) == null); // need to show T_char(LIFT(a))

function NOT(a:ptr) returns (ptr);
axiom(forall a:ptr :: {NOT(a)} a == Ptr(null,0) ==> NOT(a) != Ptr(null,0));
axiom(forall a:ptr :: {NOT(a)} a != Ptr(null,0) ==> NOT(a) == Ptr(null,0));

function NULL_CHECK(a:ptr) returns (ptr);
axiom(forall a:ptr :: {NULL_CHECK(a)} a == Ptr(null,0) ==> NULL_CHECK(a) != Ptr(null,0));
axiom(forall a:ptr :: {NULL_CHECK(a)} a != Ptr(null,0) ==> NULL_CHECK(a) == Ptr(null,0));


function FreshObj(alloc:[ref]name, old_alloc:[ref]name, p: ptr) returns (bool);
axiom(forall alloc:[ref]name, old_alloc:[ref]name, p: ptr :: {FreshObj(alloc, old_alloc, p)}
	     FreshObj(alloc, old_alloc, p) <==> alloc[Obj(p)] == ALLOCATED && old_alloc[Obj(p)] == UNALLOCATED
);


procedure nondet_choice() returns (x:ptr);
ensures (Obj(x) == null);

procedure CreateMutexA$12 (a0:ptr, a1:ptr, a2:ptr) returns (new:ptr);
modifies alloc;
ensures (old(alloc)[Obj(new)] == UNALLOCATED && alloc[Obj(new)] == ALLOCATED);
ensures (Size(Obj(new)) == 1);
ensures (Off(new) == 0);
ensures (Obj(new) != null);
ensures (forall i:int :: BS[Ptr(Obj(new), i)]);
ensures (forall i:int :: Obj(Mem[Ptr(Obj(new), i)]) == null);
ensures (forall x_obj:ref :: {alloc[x_obj]} x_obj == Obj(new) || old(alloc)[x_obj] == alloc[x_obj]);
ensures (Mem[new] == Ptr(null,0)); 

procedure WaitForSingleObject$8 (lock :ptr, wait:ptr) returns (status:ptr);
modifies Mem;
ensures (forall x:ptr :: {Mem[x]} x == lock || old(Mem)[x] == Mem[x]);
ensures (old(Mem)[lock] == Ptr(null,0) && Mem[lock] == Ptr(null,1));

procedure ReleaseMutex$4 (lock:ptr) returns (status:ptr);
modifies Mem;
ensures (forall x:ptr :: {Mem[x]} x == lock || old(Mem)[x] == Mem[x]);
ensures (old(Mem)[lock] == Ptr(null,1) && Mem[lock] == Ptr(null,0));



procedure havoc_assert(i:ptr);
requires (i != Ptr(null, 0));

procedure havoc_assume(i:ptr);
ensures (i != Ptr(null, 0));


procedure __HAVOC_free(a:ptr);
modifies alloc;
//requires (alloc[Obj(a)] == ALLOCATED);
//requires (Off(a) == 0);
ensures (alloc[Obj(a)] != UNALLOCATED);
ensures (alloc[Obj(a)] != ALLOCATED);
ensures (forall x_obj:ref :: {alloc[x_obj]} Obj(a) == x_obj || old(alloc)[x_obj] == alloc[x_obj]);

procedure __HAVOC_malloc_heap(obj_size:ptr) returns (new:ptr);
modifies alloc;
ensures (old(alloc)[Obj(new)] == UNALLOCATED && alloc[Obj(new)] == ALLOCATED);
ensures (Size(Obj(new)) == Off(obj_size));
ensures (Off(new) == 0);
ensures (Obj(new) != null);
ensures (IsHeap(Obj(new)));
ensures (forall i:int :: BS[Ptr(Obj(new), i)]);
ensures (forall i:int :: Obj(Mem[Ptr(Obj(new), i)]) == null);
ensures (forall x_obj:ref :: {alloc[x_obj]} x_obj == Obj(new) || old(alloc)[x_obj] == alloc[x_obj]);


procedure __HAVOC_malloc_stack(obj_size:ptr) returns (new:ptr);
modifies alloc;
ensures (old(alloc)[Obj(new)] == UNALLOCATED && alloc[Obj(new)] == ALLOCATED);
ensures (Size(Obj(new)) == Off(obj_size));
ensures (Off(new) == 0);
ensures (Obj(new) != null);
ensures (!IsHeap(Obj(new)));
ensures (forall i:int :: BS[Ptr(Obj(new), i)]);
ensures (forall i:int :: Obj(Mem[Ptr(Obj(new), i)]) == null);
ensures (forall x_obj:ref :: {alloc[x_obj]} x_obj == Obj(new) || old(alloc)[x_obj] == alloc[x_obj]);

procedure _strdup(str:ptr) returns (new:ptr);
modifies alloc;
ensures (old(alloc)[Obj(new)] == UNALLOCATED && alloc[Obj(new)] == ALLOCATED);
ensures (Off(new) == 0);
ensures (Obj(new) != null);
ensures (forall i:int :: BS[Ptr(Obj(new), i)]);
ensures (forall i:int :: Obj(Mem[Ptr(Obj(new), i)]) == null);
ensures (forall x_obj:ref :: {alloc[x_obj]} x_obj == Obj(new) || old(alloc)[x_obj] == alloc[x_obj]);

procedure _xstrcasecmp(a0:ptr, a1:ptr) returns (ret:ptr);

procedure _xstrcmp(a0:ptr, a1:ptr) returns (ret:ptr);
var Mem_ByteCapacity__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_ByteOffset___unnamed_16_39e6661e:[ptr]ptr;
var Mem_BytesPerSector__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_CHAR:[ptr]ptr;
var Mem_CancelRoutine__IRP:[ptr]ptr;
var Mem_Cancel__IRP:[ptr]ptr;
var Mem_Control__IO_STACK_LOCATION:[ptr]ptr;
var Mem_CurrentStackLocation___unnamed_4_f80453a0:[ptr]ptr;
var Mem_DeviceExtension__DEVICE_OBJECT:[ptr]ptr;
var Mem_DeviceObject__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_FUNCTION:[ptr]ptr;
var Mem_FlCancelSpinLock__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_HoldNewReqMutex__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_HoldNewRequests__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_INT4:[ptr]ptr;
var Mem_Information__IO_STATUS_BLOCK:[ptr]ptr;
var Mem_IoStatus__IRP:[ptr]ptr;
var Mem_IsRemoved__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_IsStarted__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_Length___unnamed_16_39e6661e:[ptr]ptr;
var Mem_ListEntry___unnamed_12_003c1454:[ptr]ptr;
var Mem_ListSpinLock__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_LowPart___unnamed_8_34582070:[ptr]ptr;
var Mem_MediaType__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_NewRequestQueue__DISKETTE_EXTENSION:[ptr]ptr;
var Mem_Overlay___unnamed_48_c27ef811:[ptr]ptr;
var Mem_PCHAR:[ptr]ptr;
var Mem_PFUNCTION:[ptr]ptr;
var Mem_PPFUNCTION:[ptr]ptr;
var Mem_PUINT4:[ptr]ptr;
var Mem_PVOID:[ptr]ptr;
var Mem_P_DISKETTE_EXTENSION:[ptr]ptr;
var Mem_P_FAST_MUTEX:[ptr]ptr;
var Mem_P_IO_STACK_LOCATION:[ptr]ptr;
var Mem_P_LIST_ENTRY:[ptr]ptr;
var Mem_Parameters__IO_STACK_LOCATION:[ptr]ptr;
var Mem_Read___unnamed_16_c0f0e7de:[ptr]ptr;
var Mem_Status___unnamed_4_c7b3d275:[ptr]ptr;
var Mem_Tail__IRP:[ptr]ptr;
var Mem_UCHAR:[ptr]ptr;
var Mem_UINT4:[ptr]ptr;
var Mem___unnamed_12_003c1454___unnamed_40_6ef75b20:[ptr]ptr;
var Mem___unnamed_4_c7b3d275__IO_STATUS_BLOCK:[ptr]ptr;
var Mem___unnamed_4_f80453a0___unnamed_12_003c1454:[ptr]ptr;
var Mem___unnamed_8_34582070__LARGE_INTEGER:[ptr]ptr;

var Res_IRQL:[ptr]ptr;
var Res_SPINLOCK:[ptr]ptr;
var Res_SPINLOCK_IRQL:[ptr]ptr;



const unique DriverEntry : ptr;
const unique DriverEntry_ref : ref;
const unique FloppyCancelQueuedRequest : ptr;
const unique FloppyCancelQueuedRequest_ref : ref;
var FloppyDebugLevel : ptr;
var PagingMutex : ptr;
var PagingReferenceCount : ptr;
const {:existential true} $FloppyQueueRequest$pre$0 : bool;
const {:existential true} $FloppyQueueRequest$pre$1 : bool;
const {:existential true} $FloppyQueueRequest$pre$2 : bool;
const {:existential true} $FloppyQueueRequest$pre$3 : bool;
const {:existential true} $FloppyQueueRequest$post$12 : bool;
const {:existential true} $FloppyQueueRequest$post$13 : bool;
const {:existential true} $FloppyQueueRequest$post$14 : bool;
const {:existential true} $FloppyQueueRequest$post$15 : bool;
const {:existential true} $FloppyQueueRequest$mod$16 : bool;
const {:existential true} $FloppyQueueRequest$mod$17 : bool;
const {:existential true} $FloppyQueueRequest$mod$18 : bool;
const {:existential true} $FloppyQueueRequest$mod$19 : bool;
const {:existential true} $FloppyQueueRequest$mod$20 : bool;
const {:existential true} $FloppyQueueRequest$mod$21 : bool;
const {:existential true} $FloppyReadWrite$pre$42 : bool;
const {:existential true} $FloppyReadWrite$pre$43 : bool;
const {:existential true} $FloppyReadWrite$pre$44 : bool;
const {:existential true} $FloppyReadWrite$pre$45 : bool;
const {:existential true} $FloppyReadWrite$pre$46 : bool;
const {:existential true} $FloppyReadWrite$post$57 : bool;
const {:existential true} $FloppyReadWrite$post$58 : bool;
const {:existential true} $FloppyReadWrite$post$59 : bool;
const {:existential true} $FloppyReadWrite$post$60 : bool;
const {:existential true} $FloppyReadWrite$post$61 : bool;
const {:existential true} $FloppyReadWrite$mod$62 : bool;
const {:existential true} $FloppyReadWrite$mod$63 : bool;
const {:existential true} $FloppyReadWrite$mod$64 : bool;
const {:existential true} $FloppyReadWrite$mod$65 : bool;
const {:existential true} $FloppyReadWrite$mod$66 : bool;
const {:existential true} $FloppyReadWrite$mod$67 : bool;


procedure ExAcquireFastMutex ( a0:ptr) ;


procedure ExReleaseFastMutex ( a0:ptr) ;


procedure ExfInterlockedInsertTailList ( a0:ptr, a1:ptr, a2:ptr) returns (ret:ptr);


procedure FlQueueIrpToThread ( Irp$21:ptr, DisketteExtension$11:ptr) returns ( $result.FlQueueIrpToThread$861.0$1$:ptr) ;





procedure IofCompleteRequest ( a0:ptr, a1:ptr) ;


procedure KfAcquireSpinLock ( SpinLock1:ptr) returns ( $result.__prototypewdm_KfAcquireSpinLock$92.0$1$__prototypewdm_KfAcquireSpinLock$4:ptr) ;

//TAG: requires __resource("SPINLOCK", SpinLock) == 0
requires(Res_SPINLOCK[SpinLock1] == Ptr(null, 0));
//TAG: ensures __resource("SPINLOCK", SpinLock) == 1
ensures(Res_SPINLOCK[SpinLock1] == Ptr(null, 1));
//TAG: ensures __resource("SPINLOCK_IRQL", SpinLock) == __return
ensures(Res_SPINLOCK_IRQL[SpinLock1] == $result.__prototypewdm_KfAcquireSpinLock$92.0$1$__prototypewdm_KfAcquireSpinLock$4);
//TAG: ensures __global_resource("IRQL") == 2
ensures(Res_IRQL[Ptr(null,1)] == Ptr(null, 2));
//TAG: ensures __return == __old_global_resource("IRQL")
ensures($result.__prototypewdm_KfAcquireSpinLock$92.0$1$__prototypewdm_KfAcquireSpinLock$4 == old(Res_IRQL)[Ptr(null,1)]);

modifies Res_IRQL;
ensures(forall r:ptr :: {Res_IRQL[r]} (Ptr(null, 1) == r) || Off(old(Res_IRQL)[r]) == Off(Res_IRQL[r]));
free requires ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free requires (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
modifies Res_SPINLOCK;
//TAG: net change in resource SPINLOCK only for: SpinLock
ensures(forall r:ptr :: {Res_SPINLOCK[r]} (SpinLock1 == r) || Off(old(Res_SPINLOCK)[r]) == Off(Res_SPINLOCK[r]));
free requires ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free requires (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));
modifies Res_SPINLOCK_IRQL;
//TAG: net change in resource SPINLOCK_IRQL only for: SpinLock
ensures(forall r:ptr :: {Res_SPINLOCK_IRQL[r]} (SpinLock1 == r) || Off(old(Res_SPINLOCK_IRQL)[r]) == Off(Res_SPINLOCK_IRQL[r]));
free requires ((forall __x:ptr :: {Res_SPINLOCK_IRQL[__x]} Obj(Res_SPINLOCK_IRQL[__x]) == null && Off(Res_SPINLOCK_IRQL[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_SPINLOCK_IRQL[__x]} Obj(Res_SPINLOCK_IRQL[__x]) == null && Off(Res_SPINLOCK_IRQL[__x]) >= 0));
free requires (Res_SPINLOCK_IRQL[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_SPINLOCK_IRQL[Ptr(null,0)] == Ptr(null,0));



procedure KfReleaseSpinLock ( SpinLock$11:ptr, NewIrql1:ptr);

//TAG: requires __global_resource("IRQL") == 2
requires(Res_IRQL[Ptr(null,1)] == Ptr(null, 2));
//TAG: requires __resource("SPINLOCK", SpinLock) == 1
requires(Res_SPINLOCK[SpinLock$11] == Ptr(null, 1));
//TAG: requires __resource("SPINLOCK_IRQL", SpinLock) == NewIrql
requires(Res_SPINLOCK_IRQL[SpinLock$11] == NewIrql1);
//TAG: ensures __resource("SPINLOCK", SpinLock) == 0
ensures(Res_SPINLOCK[SpinLock$11] == Ptr(null, 0));
//TAG: ensures __global_resource("IRQL") == NewIrql
ensures(Res_IRQL[Ptr(null,1)] == NewIrql1);

modifies Res_IRQL;
ensures(forall r:ptr :: {Res_IRQL[r]} (Ptr(null, 1) == r) || Off(old(Res_IRQL)[r]) == Off(Res_IRQL[r]));
free requires ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free requires (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
modifies Res_SPINLOCK;
//TAG: net change in resource SPINLOCK only for: SpinLock
ensures(forall r:ptr :: {Res_SPINLOCK[r]} (SpinLock$11 == r) || Off(old(Res_SPINLOCK)[r]) == Off(Res_SPINLOCK[r]));
free requires ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free requires (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));



procedure MmPageEntireDriver ( a0:ptr) returns (ret:ptr);


procedure MmResetDriverPaging ( a0:ptr) ;


procedure  FloppyQueueRequest ( DisketteExtension1:ptr, Irp1:ptr) returns ( $result.FloppyQueueRequest$5780.0$1$:ptr) 

//TAG: requires $FloppyQueueRequest$pre$0 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)DeviceExtension)->ListSpinLock) == 0)
requires($FloppyQueueRequest$pre$0 || ((true) ==> (Res_SPINLOCK[ListSpinLock__DISKETTE_EXTENSION(DisketteExtension1)] == Ptr(null, 0))));
//TAG: requires $FloppyQueueRequest$pre$1 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)DeviceExtension)->FlCancelSpinLock) == 0)
requires($FloppyQueueRequest$pre$1 || ((true) ==> (Res_SPINLOCK[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension1)] == Ptr(null, 0))));
//TAG: requires $FloppyQueueRequest$pre$2 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)DeviceExtension)->NewRequestQueueSpinLock) == 0)
requires($FloppyQueueRequest$pre$2 || ((true) ==> (Res_SPINLOCK[NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension1)] == Ptr(null, 0))));
//TAG: requires $FloppyQueueRequest$pre$3 || (1 ==> ((DISKETTE_EXTENSION *)DeviceExtension)->DeviceObject->DeviceExtension == DeviceExtension)
requires($FloppyQueueRequest$pre$3 || ((true) ==> (Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(Mem_DeviceObject__DISKETTE_EXTENSION[DeviceObject__DISKETTE_EXTENSION(DisketteExtension1)])] == DisketteExtension1)));
//TAG: ensures $FloppyQueueRequest$post$12 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)DeviceExtension)->ListSpinLock) == 0)
ensures($FloppyQueueRequest$post$12 || ((true) ==> (Res_SPINLOCK[ListSpinLock__DISKETTE_EXTENSION(DisketteExtension1)] == Ptr(null, 0))));
//TAG: ensures $FloppyQueueRequest$post$13 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)DeviceExtension)->FlCancelSpinLock) == 0)
ensures($FloppyQueueRequest$post$13 || ((true) ==> (Res_SPINLOCK[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension1)] == Ptr(null, 0))));
//TAG: ensures $FloppyQueueRequest$post$14 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)DeviceExtension)->NewRequestQueueSpinLock) == 0)
ensures($FloppyQueueRequest$post$14 || ((true) ==> (Res_SPINLOCK[NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension1)] == Ptr(null, 0))));
//TAG: ensures $FloppyQueueRequest$post$15 || (1 ==> ((DISKETTE_EXTENSION *)DeviceExtension)->DeviceObject->DeviceExtension == DeviceExtension)
ensures($FloppyQueueRequest$post$15 || ((true) ==> (Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(Mem_DeviceObject__DISKETTE_EXTENSION[DeviceObject__DISKETTE_EXTENSION(DisketteExtension1)])] == DisketteExtension1)));
modifies alloc;
free ensures(forall f:ref :: {alloc[f]} old(alloc)[f] != UNALLOCATED ==> alloc[f] == old(alloc)[f]);

modifies Res_IRQL;
//TAG: no net change in resource IRQL
ensures(forall r:ptr :: {Res_IRQL[r]} Off(old(Res_IRQL)[r]) == Off(Res_IRQL[r]));
free requires ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free requires (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
modifies Res_SPINLOCK;
//TAG: net change in resource SPINLOCK only for: &DeviceExtension->ListSpinLock, &DeviceExtension->FlCancelSpinLock, &DeviceExtension->NewRequestQueueSpinLock
ensures(forall r:ptr :: {Res_SPINLOCK[r]} (!$FloppyQueueRequest$mod$16 && ListSpinLock__DISKETTE_EXTENSION(DisketteExtension1) == r) || (!$FloppyQueueRequest$mod$18 && FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension1) == r) || (!$FloppyQueueRequest$mod$20 && NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension1) == r) || Off(old(Res_SPINLOCK)[r]) == Off(Res_SPINLOCK[r]));
free requires ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free requires (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));
modifies Res_SPINLOCK_IRQL;
//TAG: net change in resource SPINLOCK_IRQL only for: &DeviceExtension->ListSpinLock, &DeviceExtension->FlCancelSpinLock, &DeviceExtension->NewRequestQueueSpinLock
ensures(forall r:ptr :: {Res_SPINLOCK_IRQL[r]} (!$FloppyQueueRequest$mod$17 && ListSpinLock__DISKETTE_EXTENSION(DisketteExtension1) == r) || (!$FloppyQueueRequest$mod$19 && FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension1) == r) || (!$FloppyQueueRequest$mod$21 && NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension1) == r) || Off(old(Res_SPINLOCK_IRQL)[r]) == Off(Res_SPINLOCK_IRQL[r]));
free requires ((forall __x:ptr :: {Res_SPINLOCK_IRQL[__x]} Obj(Res_SPINLOCK_IRQL[__x]) == null && Off(Res_SPINLOCK_IRQL[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_SPINLOCK_IRQL[__x]} Obj(Res_SPINLOCK_IRQL[__x]) == null && Off(Res_SPINLOCK_IRQL[__x]) >= 0));
free requires (Res_SPINLOCK_IRQL[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_SPINLOCK_IRQL[Ptr(null,0)] == Ptr(null,0));
modifies Mem_Control__IO_STACK_LOCATION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_Control__IO_STACK_LOCATION[m]} Mem_Control__IO_STACK_LOCATION[m] == old(Mem_Control__IO_STACK_LOCATION)[m]);
free ensures(Mem_Control__IO_STACK_LOCATION[Ptr(null,0)] == old(Mem_Control__IO_STACK_LOCATION)[Ptr(null,0)]);
modifies Mem_FUNCTION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_FUNCTION[m]} Mem_FUNCTION[m] == old(Mem_FUNCTION)[m]);
free ensures(Mem_FUNCTION[Ptr(null,0)] == old(Mem_FUNCTION)[Ptr(null,0)]);
modifies Mem_FlCancelSpinLock__DISKETTE_EXTENSION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m]} Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m] == old(Mem_FlCancelSpinLock__DISKETTE_EXTENSION)[m]);
free ensures(Mem_FlCancelSpinLock__DISKETTE_EXTENSION[Ptr(null,0)] == old(Mem_FlCancelSpinLock__DISKETTE_EXTENSION)[Ptr(null,0)]);
modifies Mem_Information__IO_STATUS_BLOCK;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_Information__IO_STATUS_BLOCK[m]} Mem_Information__IO_STATUS_BLOCK[m] == old(Mem_Information__IO_STATUS_BLOCK)[m]);
free ensures(Mem_Information__IO_STATUS_BLOCK[Ptr(null,0)] == old(Mem_Information__IO_STATUS_BLOCK)[Ptr(null,0)]);
modifies Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m]} Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m] == old(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION)[m]);
free ensures(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[Ptr(null,0)] == old(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION)[Ptr(null,0)]);
modifies Mem_Status___unnamed_4_c7b3d275;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_Status___unnamed_4_c7b3d275[m]} Mem_Status___unnamed_4_c7b3d275[m] == old(Mem_Status___unnamed_4_c7b3d275)[m]);
free ensures(Mem_Status___unnamed_4_c7b3d275[Ptr(null,0)] == old(Mem_Status___unnamed_4_c7b3d275)[Ptr(null,0)]);
modifies Mem_UINT4;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_UINT4[m]} Mem_UINT4[m] == old(Mem_UINT4)[m]);
free ensures(Mem_UINT4[Ptr(null,0)] == old(Mem_UINT4)[Ptr(null,0)]);

{
var havoc_stringTemp:ptr;
var condVal:ptr;
var DisketteExtension : ptr;
var Irp : ptr;
var $RtlAssert.arg.1$3$ : ptr;
var $RtlAssert.arg.2$2$ : ptr;
var $_InterlockedExchange.arg.1$7$ : ptr;
var $_InterlockedExchange.arg.1$9$ : ptr;
var $_InterlockedExchange.arg.2$6$ : ptr;
var $ntStatus$4$5806.24$ : ptr;
var $oldIrql$3$5805.24$ : ptr;
var $result.ExfInterlockedInsertTailList$5854.36$11$ : ptr;
var $result.KfAcquireSpinLock$5825.4$4$ : ptr;
var $result.MmPageEntireDriver$5842.8$10$ : ptr;
var $result._InterlockedExchange$5826.4$5$ : ptr;
var $result._InterlockedExchange$5831.26$8$ : ptr;
var tempBoogie0:ptr;
var tempBoogie1:ptr;
var tempBoogie2:ptr;
var tempBoogie3:ptr;
var tempBoogie4:ptr;
var tempBoogie5:ptr;
var tempBoogie6:ptr;
var tempBoogie7:ptr;
var tempBoogie8:ptr;
var tempBoogie9:ptr;
var tempBoogie10:ptr;
var tempBoogie11:ptr;
var tempBoogie12:ptr;
var tempBoogie13:ptr;
var tempBoogie14:ptr;
var tempBoogie15:ptr;
var tempBoogie16:ptr;
var tempBoogie17:ptr;
var tempBoogie18:ptr;
var tempBoogie19:ptr;


start:

assume (alloc[Obj(DisketteExtension1)] != UNALLOCATED);
assume (alloc[Obj(Irp1)] != UNALLOCATED);
DisketteExtension := Ptr(null, 0);
Irp := Ptr(null, 0);
$RtlAssert.arg.1$3$ := Ptr(null, 0);
$RtlAssert.arg.2$2$ := Ptr(null, 0);
$_InterlockedExchange.arg.1$7$ := Ptr(null, 0);
$_InterlockedExchange.arg.1$9$ := Ptr(null, 0);
$_InterlockedExchange.arg.2$6$ := Ptr(null, 0);
$ntStatus$4$5806.24$ := Ptr(null, 0);
$oldIrql$3$5805.24$ := Ptr(null, 0);
$result.ExfInterlockedInsertTailList$5854.36$11$ := Ptr(null, 0);
$result.KfAcquireSpinLock$5825.4$4$ := Ptr(null, 0);
$result.MmPageEntireDriver$5842.8$10$ := Ptr(null, 0);
$result._InterlockedExchange$5826.4$5$ := Ptr(null, 0);
$result._InterlockedExchange$5831.26$8$ := Ptr(null, 0);
DisketteExtension := DisketteExtension1;
Irp := Irp1;
$result.FloppyQueueRequest$5780.0$1$ := Ptr(null,0);
goto label_3;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5864)
label_1:
assume (forall m:ptr :: {Mem_Control__IO_STACK_LOCATION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_Control__IO_STACK_LOCATION[m] == old(Mem_Control__IO_STACK_LOCATION)[m]);
assume (forall m:ptr :: {Mem_FUNCTION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_FUNCTION[m] == old(Mem_FUNCTION)[m]);
assume (forall m:ptr :: {Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m] == old(Mem_FlCancelSpinLock__DISKETTE_EXTENSION)[m]);
assume (forall m:ptr :: {Mem_Information__IO_STATUS_BLOCK[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_Information__IO_STATUS_BLOCK[m] == old(Mem_Information__IO_STATUS_BLOCK)[m]);
assume (forall m:ptr :: {Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m] == old(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION)[m]);
assume (forall m:ptr :: {Mem_Status___unnamed_4_c7b3d275[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_Status___unnamed_4_c7b3d275[m] == old(Mem_Status___unnamed_4_c7b3d275)[m]);
assume (forall m:ptr :: {Mem_UINT4[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_UINT4[m] == old(Mem_UINT4)[m]);
return;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5864)
label_2:
assume false;
return;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5805)
label_3:
goto label_4;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5806)
label_4:
goto label_5;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5811)
label_5:
call ExAcquireFastMutex (Mem_P_FAST_MUTEX[PagingMutex]);
goto label_8;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5811)
label_8:
tempBoogie0 := Ptr(Obj(Mem_UINT4[PagingReferenceCount]), Off(Mem_UINT4[PagingReferenceCount]) + 1 * 1) ;
Mem_UINT4[PagingReferenceCount] := tempBoogie0;
goto label_8_true , label_8_false ;


label_8_true :
assume (Mem_UINT4[PagingReferenceCount] == Ptr(null, 1));
goto label_12;


label_8_false :
assume !(Mem_UINT4[PagingReferenceCount] == Ptr(null, 1));
goto label_9;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5811)
label_9:
call ExReleaseFastMutex (Mem_P_FAST_MUTEX[PagingMutex]);
goto label_15;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5811)
label_12:
call MmResetDriverPaging (DriverEntry);
goto label_9;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5816)
label_15:
goto label_15_true , label_15_false ;


label_15_true :
assume (Mem_HoldNewRequests__DISKETTE_EXTENSION[HoldNewRequests__DISKETTE_EXTENSION(DisketteExtension)] != Ptr(null,0));
goto label_17;


label_15_false :
assume (Mem_HoldNewRequests__DISKETTE_EXTENSION[HoldNewRequests__DISKETTE_EXTENSION(DisketteExtension)] == Ptr(null,0));
goto label_16;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5816)
label_16:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$RtlAssert.arg.2$2$ := havoc_stringTemp ;
goto label_61;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5825)
label_17:
assume (Mem_FlCancelSpinLock__DISKETTE_EXTENSION[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)] == Mem_UINT4[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)]);
call $result.KfAcquireSpinLock$5825.4$4$ := KfAcquireSpinLock (FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension));
Mem_FlCancelSpinLock__DISKETTE_EXTENSION[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)] := Mem_UINT4[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)];
goto label_20;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5825)
label_20:
$oldIrql$3$5805.24$ := $result.KfAcquireSpinLock$5825.4$4$ ;
goto label_21;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5826)
label_21:
$_InterlockedExchange.arg.2$6$ := FloppyCancelQueuedRequest ;
goto label_22;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5826)
label_22:
$_InterlockedExchange.arg.1$7$ := CancelRoutine__IRP(Irp) ;
goto label_23;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5826)
label_23:
// ignoring intrinsic intrinsic._InterlockedExchange
havoc $result._InterlockedExchange$5826.4$5$;
goto label_26;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5831)
label_26:
goto label_26_true , label_26_false ;


label_26_true :
assume (Mem_Cancel__IRP[Cancel__IRP(Irp)] != Ptr(null,0));
goto label_28;


label_26_false :
assume (Mem_Cancel__IRP[Cancel__IRP(Irp)] == Ptr(null,0));
goto label_27;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5850)
label_27:
Mem_Status___unnamed_4_c7b3d275[Status___unnamed_4_c7b3d275(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(IoStatus__IRP(Irp)))] := Ptr(null, 259) ;
goto label_53;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5831)
label_28:
$_InterlockedExchange.arg.1$9$ := CancelRoutine__IRP(Irp) ;
goto label_29;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5831)
label_29:
// ignoring intrinsic intrinsic._InterlockedExchange
havoc $result._InterlockedExchange$5831.26$8$;
goto label_32;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5831)
label_32:
goto label_32_true , label_32_false ;


label_32_true :
assume ($result._InterlockedExchange$5831.26$8$ != Ptr(null,0));
goto label_33;


label_32_false :
assume ($result._InterlockedExchange$5831.26$8$ == Ptr(null,0));
goto label_27;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5836)
label_33:
Mem_Status___unnamed_4_c7b3d275[Status___unnamed_4_c7b3d275(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(IoStatus__IRP(Irp)))] := Ptr(null, -1073741536) ;
goto label_34;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5837)
label_34:
Mem_Information__IO_STATUS_BLOCK[Information__IO_STATUS_BLOCK(IoStatus__IRP(Irp))] := Ptr(null, 0) ;
goto label_35;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5839)
label_35:
assume (Mem_FlCancelSpinLock__DISKETTE_EXTENSION[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)] == Mem_UINT4[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)]);
call KfReleaseSpinLock (FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension), $oldIrql$3$5805.24$);
Mem_FlCancelSpinLock__DISKETTE_EXTENSION[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)] := Mem_UINT4[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)];
goto label_38;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5840)
label_38:
call IofCompleteRequest (Irp, Ptr(null, 0));
goto label_41;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5842)
label_41:
call ExAcquireFastMutex (Mem_P_FAST_MUTEX[PagingMutex]);
goto label_44;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5842)
label_44:
tempBoogie0 := Ptr(Obj(Mem_UINT4[PagingReferenceCount]), Off(Mem_UINT4[PagingReferenceCount]) - 1) ;
Mem_UINT4[PagingReferenceCount] := tempBoogie0;
goto label_44_true , label_44_false ;


label_44_true :
assume (Mem_UINT4[PagingReferenceCount] != Ptr(null,0));
goto label_48;


label_44_false :
assume (Mem_UINT4[PagingReferenceCount] == Ptr(null,0));
goto label_45;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5842)
label_45:
call $result.MmPageEntireDriver$5842.8$10$ := MmPageEntireDriver (DriverEntry);
goto label_48;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5842)
label_48:
call ExReleaseFastMutex (Mem_P_FAST_MUTEX[PagingMutex]);
goto label_51;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5844)
label_51:
$ntStatus$4$5806.24$ := Ptr(null, -1073741536) ;
goto label_52;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5863)
label_52:
$result.FloppyQueueRequest$5780.0$1$ := $ntStatus$4$5806.24$ ;
goto label_1;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5852)
label_53:
tempBoogie0 := BIT_BOR(Mem_Control__IO_STACK_LOCATION[Control__IO_STACK_LOCATION(Mem_CurrentStackLocation___unnamed_4_f80453a0[CurrentStackLocation___unnamed_4_f80453a0(__unnamed_4_f80453a0___unnamed_12_003c1454(__unnamed_12_003c1454___unnamed_40_6ef75b20(Overlay___unnamed_48_c27ef811(Tail__IRP(Irp)))))])], Ptr(null, 1)) ;
Mem_Control__IO_STACK_LOCATION[Control__IO_STACK_LOCATION(Mem_CurrentStackLocation___unnamed_4_f80453a0[CurrentStackLocation___unnamed_4_f80453a0(__unnamed_4_f80453a0___unnamed_12_003c1454(__unnamed_12_003c1454___unnamed_40_6ef75b20(Overlay___unnamed_48_c27ef811(Tail__IRP(Irp)))))])] := tempBoogie0 ;
goto label_54;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5854)
label_54:
assume (Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension)] == Mem_UINT4[NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension)]);
call $result.ExfInterlockedInsertTailList$5854.36$11$ := ExfInterlockedInsertTailList (NewRequestQueue__DISKETTE_EXTENSION(DisketteExtension), ListEntry___unnamed_12_003c1454(__unnamed_12_003c1454___unnamed_40_6ef75b20(Overlay___unnamed_48_c27ef811(Tail__IRP(Irp)))), NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension));
Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension)] := Mem_UINT4[NewRequestQueueSpinLock__DISKETTE_EXTENSION(DisketteExtension)];
goto label_57;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5858)
label_57:
assume (Mem_FlCancelSpinLock__DISKETTE_EXTENSION[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)] == Mem_UINT4[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)]);
call KfReleaseSpinLock (FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension), $oldIrql$3$5805.24$);
Mem_FlCancelSpinLock__DISKETTE_EXTENSION[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)] := Mem_UINT4[FlCancelSpinLock__DISKETTE_EXTENSION(DisketteExtension)];
goto label_60;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5860)
label_60:
$ntStatus$4$5806.24$ := Ptr(null, 259) ;
goto label_52;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5816)
label_61:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$RtlAssert.arg.1$3$ := havoc_stringTemp ;
goto label_62;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(5816)
label_62:
// skip RtlAssert
goto label_17;

}



procedure  FloppyReadWrite ( DeviceObject1:ptr, Irp$11:ptr) returns ( $result.FloppyReadWrite$2203.0$1$:ptr) 

//TAG: requires $FloppyReadWrite$pre$42 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->ListSpinLock) == 0)
requires($FloppyReadWrite$pre$42 || ((true) ==> (Res_SPINLOCK[ListSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == Ptr(null, 0))));
//TAG: requires $FloppyReadWrite$pre$43 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->FlCancelSpinLock) == 0)
requires($FloppyReadWrite$pre$43 || ((true) ==> (Res_SPINLOCK[FlCancelSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == Ptr(null, 0))));
//TAG: requires $FloppyReadWrite$pre$44 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->NewRequestQueueSpinLock) == 0)
requires($FloppyReadWrite$pre$44 || ((true) ==> (Res_SPINLOCK[NewRequestQueueSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == Ptr(null, 0))));
//TAG: requires $FloppyReadWrite$pre$45 || (1 ==> ((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->DeviceObject->DeviceExtension == (DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))
requires($FloppyReadWrite$pre$45 || ((true) ==> (Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(Mem_DeviceObject__DISKETTE_EXTENSION[DeviceObject__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])])] == Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])));
//TAG: requires $FloppyReadWrite$pre$46 || (((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->DeviceObject == DeviceObject)
requires($FloppyReadWrite$pre$46 || (Mem_DeviceObject__DISKETTE_EXTENSION[DeviceObject__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == DeviceObject1));
//TAG: ensures $FloppyReadWrite$post$57 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->ListSpinLock) == 0)
ensures($FloppyReadWrite$post$57 || ((true) ==> (Res_SPINLOCK[ListSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == Ptr(null, 0))));
//TAG: ensures $FloppyReadWrite$post$58 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->FlCancelSpinLock) == 0)
ensures($FloppyReadWrite$post$58 || ((true) ==> (Res_SPINLOCK[FlCancelSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == Ptr(null, 0))));
//TAG: ensures $FloppyReadWrite$post$59 || (1 ==> __resource("SPINLOCK", &((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->NewRequestQueueSpinLock) == 0)
ensures($FloppyReadWrite$post$59 || ((true) ==> (Res_SPINLOCK[NewRequestQueueSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == Ptr(null, 0))));
//TAG: ensures $FloppyReadWrite$post$60 || (1 ==> ((DISKETTE_EXTENSION *)(DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->DeviceObject->DeviceExtension == (DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))
ensures($FloppyReadWrite$post$60 || ((true) ==> (Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(Mem_DeviceObject__DISKETTE_EXTENSION[DeviceObject__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])])] == Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])));
//TAG: ensures $FloppyReadWrite$post$61 || (((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->DeviceObject == DeviceObject)
ensures($FloppyReadWrite$post$61 || (Mem_DeviceObject__DISKETTE_EXTENSION[DeviceObject__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)])] == DeviceObject1));
modifies alloc;
free ensures(forall f:ref :: {alloc[f]} old(alloc)[f] != UNALLOCATED ==> alloc[f] == old(alloc)[f]);

modifies Res_IRQL;
//TAG: no net change in resource IRQL
ensures(forall r:ptr :: {Res_IRQL[r]} Off(old(Res_IRQL)[r]) == Off(Res_IRQL[r]));
free requires ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_IRQL[__x]} Obj(Res_IRQL[__x]) == null && Off(Res_IRQL[__x]) >= 0));
free requires (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_IRQL[Ptr(null,0)] == Ptr(null,0));
modifies Res_SPINLOCK;
//TAG: net change in resource SPINLOCK only for: &((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->ListSpinLock, &((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->FlCancelSpinLock, &((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->NewRequestQueueSpinLock
ensures(forall r:ptr :: {Res_SPINLOCK[r]} (!$FloppyReadWrite$mod$62 && ListSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)]) == r) || (!$FloppyReadWrite$mod$64 && FlCancelSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)]) == r) || (!$FloppyReadWrite$mod$66 && NewRequestQueueSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)]) == r) || Off(old(Res_SPINLOCK)[r]) == Off(Res_SPINLOCK[r]));
free requires ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_SPINLOCK[__x]} Obj(Res_SPINLOCK[__x]) == null && Off(Res_SPINLOCK[__x]) >= 0));
free requires (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_SPINLOCK[Ptr(null,0)] == Ptr(null,0));
modifies Res_SPINLOCK_IRQL;
//TAG: net change in resource SPINLOCK_IRQL only for: &((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->ListSpinLock, &((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->FlCancelSpinLock, &((DISKETTE_EXTENSION *)(DeviceObject->DeviceExtension))->NewRequestQueueSpinLock
ensures(forall r:ptr :: {Res_SPINLOCK_IRQL[r]} (!$FloppyReadWrite$mod$63 && ListSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)]) == r) || (!$FloppyReadWrite$mod$65 && FlCancelSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)]) == r) || (!$FloppyReadWrite$mod$67 && NewRequestQueueSpinLock__DISKETTE_EXTENSION(Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject1)]) == r) || Off(old(Res_SPINLOCK_IRQL)[r]) == Off(Res_SPINLOCK_IRQL[r]));
free requires ((forall __x:ptr :: {Res_SPINLOCK_IRQL[__x]} Obj(Res_SPINLOCK_IRQL[__x]) == null && Off(Res_SPINLOCK_IRQL[__x]) >= 0));
free ensures ((forall __x:ptr :: {Res_SPINLOCK_IRQL[__x]} Obj(Res_SPINLOCK_IRQL[__x]) == null && Off(Res_SPINLOCK_IRQL[__x]) >= 0));
free requires (Res_SPINLOCK_IRQL[Ptr(null,0)] == Ptr(null,0));
free ensures (Res_SPINLOCK_IRQL[Ptr(null,0)] == Ptr(null,0));
modifies Mem_Control__IO_STACK_LOCATION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_Control__IO_STACK_LOCATION[m]} Mem_Control__IO_STACK_LOCATION[m] == old(Mem_Control__IO_STACK_LOCATION)[m]);
free ensures(Mem_Control__IO_STACK_LOCATION[Ptr(null,0)] == old(Mem_Control__IO_STACK_LOCATION)[Ptr(null,0)]);
modifies Mem_FUNCTION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_FUNCTION[m]} Mem_FUNCTION[m] == old(Mem_FUNCTION)[m]);
free ensures(Mem_FUNCTION[Ptr(null,0)] == old(Mem_FUNCTION)[Ptr(null,0)]);
modifies Mem_FlCancelSpinLock__DISKETTE_EXTENSION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m]} Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m] == old(Mem_FlCancelSpinLock__DISKETTE_EXTENSION)[m]);
free ensures(Mem_FlCancelSpinLock__DISKETTE_EXTENSION[Ptr(null,0)] == old(Mem_FlCancelSpinLock__DISKETTE_EXTENSION)[Ptr(null,0)]);
modifies Mem_Information__IO_STATUS_BLOCK;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_Information__IO_STATUS_BLOCK[m]} Mem_Information__IO_STATUS_BLOCK[m] == old(Mem_Information__IO_STATUS_BLOCK)[m]);
free ensures(Mem_Information__IO_STATUS_BLOCK[Ptr(null,0)] == old(Mem_Information__IO_STATUS_BLOCK)[Ptr(null,0)]);
modifies Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m]} Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m] == old(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION)[m]);
free ensures(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[Ptr(null,0)] == old(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION)[Ptr(null,0)]);
modifies Mem_Status___unnamed_4_c7b3d275;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_Status___unnamed_4_c7b3d275[m]} Mem_Status___unnamed_4_c7b3d275[m] == old(Mem_Status___unnamed_4_c7b3d275)[m]);
free ensures(Mem_Status___unnamed_4_c7b3d275[Ptr(null,0)] == old(Mem_Status___unnamed_4_c7b3d275)[Ptr(null,0)]);
modifies Mem_UINT4;
//TAG: no updated memory locations
free ensures(forall m:ptr :: {Mem_UINT4[m]} Mem_UINT4[m] == old(Mem_UINT4)[m]);
free ensures(Mem_UINT4[Ptr(null,0)] == old(Mem_UINT4)[Ptr(null,0)]);

{
var havoc_stringTemp:ptr;
var condVal:ptr;
var $DbgPrint.arg.1$10$ : ptr;
var $DbgPrint.arg.1$13$ : ptr;
var $DbgPrint.arg.1$15$ : ptr;
var $DbgPrint.arg.1$3$ : ptr;
var $DbgPrint.arg.1$6$ : ptr;
var $DbgPrint.arg.1$8$ : ptr;
var DeviceObject : ptr;
var Irp$1 : ptr;
var $disketteExtension$5$2232.24$ : ptr;
var $irpSp$3$2230.23$ : ptr;
var $ntStatus$4$2231.13$ : ptr;
var $result.DbgPrint$2234.4$2$ : ptr;
var $result.DbgPrint$2278.0$5$ : ptr;
var $result.DbgPrint$2280.0$7$ : ptr;
var $result.DbgPrint$2305.0$9$ : ptr;
var $result.DbgPrint$2317.0$12$ : ptr;
var $result.DbgPrint$2327.0$14$ : ptr;
var $result.FlQueueIrpToThread$2308.41$11$ : ptr;
var $result.FloppyQueueRequest$2247.37$4$ : ptr;
var tempBoogie0:ptr;
var tempBoogie1:ptr;
var tempBoogie2:ptr;
var tempBoogie3:ptr;
var tempBoogie4:ptr;
var tempBoogie5:ptr;
var tempBoogie6:ptr;
var tempBoogie7:ptr;
var tempBoogie8:ptr;
var tempBoogie9:ptr;
var tempBoogie10:ptr;
var tempBoogie11:ptr;
var tempBoogie12:ptr;
var tempBoogie13:ptr;
var tempBoogie14:ptr;
var tempBoogie15:ptr;
var tempBoogie16:ptr;
var tempBoogie17:ptr;
var tempBoogie18:ptr;
var tempBoogie19:ptr;


start:

assume (alloc[Obj(DeviceObject1)] != UNALLOCATED);
assume (alloc[Obj(Irp$11)] != UNALLOCATED);
$DbgPrint.arg.1$10$ := Ptr(null, 0);
$DbgPrint.arg.1$13$ := Ptr(null, 0);
$DbgPrint.arg.1$15$ := Ptr(null, 0);
$DbgPrint.arg.1$3$ := Ptr(null, 0);
$DbgPrint.arg.1$6$ := Ptr(null, 0);
$DbgPrint.arg.1$8$ := Ptr(null, 0);
DeviceObject := Ptr(null, 0);
Irp$1 := Ptr(null, 0);
$disketteExtension$5$2232.24$ := Ptr(null, 0);
$irpSp$3$2230.23$ := Ptr(null, 0);
$ntStatus$4$2231.13$ := Ptr(null, 0);
$result.DbgPrint$2234.4$2$ := Ptr(null, 0);
$result.DbgPrint$2278.0$5$ := Ptr(null, 0);
$result.DbgPrint$2280.0$7$ := Ptr(null, 0);
$result.DbgPrint$2305.0$9$ := Ptr(null, 0);
$result.DbgPrint$2317.0$12$ := Ptr(null, 0);
$result.DbgPrint$2327.0$14$ := Ptr(null, 0);
$result.FlQueueIrpToThread$2308.41$11$ := Ptr(null, 0);
$result.FloppyQueueRequest$2247.37$4$ := Ptr(null, 0);
DeviceObject := DeviceObject1;
Irp$1 := Irp$11;
$result.FloppyReadWrite$2203.0$1$ := Ptr(null,0);
goto label_3;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2334)
label_1:
assume (forall m:ptr :: {Mem_Control__IO_STACK_LOCATION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_Control__IO_STACK_LOCATION[m] == old(Mem_Control__IO_STACK_LOCATION)[m]);
assume (forall m:ptr :: {Mem_FUNCTION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_FUNCTION[m] == old(Mem_FUNCTION)[m]);
assume (forall m:ptr :: {Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_FlCancelSpinLock__DISKETTE_EXTENSION[m] == old(Mem_FlCancelSpinLock__DISKETTE_EXTENSION)[m]);
assume (forall m:ptr :: {Mem_Information__IO_STATUS_BLOCK[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_Information__IO_STATUS_BLOCK[m] == old(Mem_Information__IO_STATUS_BLOCK)[m]);
assume (forall m:ptr :: {Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION[m] == old(Mem_NewRequestQueueSpinLock__DISKETTE_EXTENSION)[m]);
assume (forall m:ptr :: {Mem_Status___unnamed_4_c7b3d275[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_Status___unnamed_4_c7b3d275[m] == old(Mem_Status___unnamed_4_c7b3d275)[m]);
assume (forall m:ptr :: {Mem_UINT4[m]} alloc[Obj(m)] != ALLOCATED && old(alloc)[Obj(m)] != ALLOCATED ==> Mem_UINT4[m] == old(Mem_UINT4)[m]);
return;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2334)
label_2:
assume false;
return;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2230)
label_3:
goto label_4;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2231)
label_4:
goto label_5;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2232)
label_5:
goto label_6;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2234)
label_6:
goto label_6_true , label_6_false ;


label_6_true :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 8)) != Ptr(null,0));
goto label_8;


label_6_false :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 8)) == Ptr(null,0));
goto label_7;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2236)
label_7:
$disketteExtension$5$2232.24$ := Mem_DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(DeviceObject)] ;
goto label_12;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2234)
label_8:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$DbgPrint.arg.1$3$ := havoc_stringTemp ;
goto label_9;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2234)
label_9:
havoc $result.DbgPrint$2234.4$2$;
// skip DbgPrint
goto label_7;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2238)
label_12:
$irpSp$3$2230.23$ := Mem_CurrentStackLocation___unnamed_4_f80453a0[CurrentStackLocation___unnamed_4_f80453a0(__unnamed_4_f80453a0___unnamed_12_003c1454(__unnamed_12_003c1454___unnamed_40_6ef75b20(Overlay___unnamed_48_c27ef811(Tail__IRP(Irp$1)))))] ;
goto label_13;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2244)
label_13:
call ExAcquireFastMutex (HoldNewReqMutex__DISKETTE_EXTENSION($disketteExtension$5$2232.24$));
goto label_16;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2245)
label_16:
goto label_16_true , label_16_false ;


label_16_true :
assume (Mem_HoldNewRequests__DISKETTE_EXTENSION[HoldNewRequests__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] != Ptr(null,0));
goto label_18;


label_16_false :
assume (Mem_HoldNewRequests__DISKETTE_EXTENSION[HoldNewRequests__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] == Ptr(null,0));
goto label_17;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2257)
label_17:
goto label_17_true , label_17_false ;


label_17_true :
assume (Mem_IsRemoved__DISKETTE_EXTENSION[IsRemoved__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] != Ptr(null,0));
goto label_27;


label_17_false :
assume (Mem_IsRemoved__DISKETTE_EXTENSION[IsRemoved__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] == Ptr(null,0));
goto label_26;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2247)
label_18:
call $result.FloppyQueueRequest$2247.37$4$ := FloppyQueueRequest ($disketteExtension$5$2232.24$, Irp$1);
goto label_21;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2247)
label_21:
$ntStatus$4$2231.13$ := $result.FloppyQueueRequest$2247.37$4$ ;
goto label_22;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2249)
label_22:
call ExReleaseFastMutex (HoldNewReqMutex__DISKETTE_EXTENSION($disketteExtension$5$2232.24$));
goto label_25;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2250)
label_25:
$result.FloppyReadWrite$2203.0$1$ := $ntStatus$4$2231.13$ ;
goto label_1;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2257)
label_26:
goto label_26_true , label_26_false ;


label_26_true :
assume (Mem_IsStarted__DISKETTE_EXTENSION[IsStarted__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] != Ptr(null,0));
goto label_39;


label_26_false :
assume (Mem_IsStarted__DISKETTE_EXTENSION[IsStarted__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] == Ptr(null,0));
goto label_27;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2259)
label_27:
call ExReleaseFastMutex (HoldNewReqMutex__DISKETTE_EXTENSION($disketteExtension$5$2232.24$));
goto label_30;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2261)
label_30:
goto label_30_true , label_30_false ;


label_30_true :
assume (Mem_IsRemoved__DISKETTE_EXTENSION[IsRemoved__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] != Ptr(null,0));
goto label_32;


label_30_false :
assume (Mem_IsRemoved__DISKETTE_EXTENSION[IsRemoved__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)] == Ptr(null,0));
goto label_31;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2264)
label_31:
$ntStatus$4$2231.13$ := Ptr(null, -1073741823) ;
goto label_33;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2262)
label_32:
$ntStatus$4$2231.13$ := Ptr(null, -1073741738) ;
goto label_33;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2266)
label_33:
Mem_Information__IO_STATUS_BLOCK[Information__IO_STATUS_BLOCK(IoStatus__IRP(Irp$1))] := Ptr(null, 0) ;
goto label_34;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2267)
label_34:
Mem_Status___unnamed_4_c7b3d275[Status___unnamed_4_c7b3d275(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(IoStatus__IRP(Irp$1)))] := $ntStatus$4$2231.13$ ;
goto label_35;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2268)
label_35:
call IofCompleteRequest (Irp$1, Ptr(null, 0));
goto label_38;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2269)
label_38:
$result.FloppyReadWrite$2203.0$1$ := $ntStatus$4$2231.13$ ;
goto label_1;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2272)
label_39:
assume (null == Obj(Mem_MediaType__DISKETTE_EXTENSION[MediaType__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]));
goto label_39_true , label_39_false ;


label_39_true :
assume (0 < Off(Mem_MediaType__DISKETTE_EXTENSION[MediaType__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]));
goto label_41;


label_39_false :
assume !(0 < Off(Mem_MediaType__DISKETTE_EXTENSION[MediaType__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]));
goto label_40;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2299)
label_40:
goto label_40_true , label_40_false ;


label_40_true :
assume (Mem_Length___unnamed_16_39e6661e[Length___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))] != Ptr(null,0));
goto label_69;


label_40_false :
assume (Mem_Length___unnamed_16_39e6661e[Length___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))] == Ptr(null,0));
goto label_68;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2274)
label_41:
assume (Obj(Mem_ByteCapacity__DISKETTE_EXTENSION[ByteCapacity__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]) == Obj(PLUS(Mem_LowPart___unnamed_8_34582070[LowPart___unnamed_8_34582070(__unnamed_8_34582070__LARGE_INTEGER(ByteOffset___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))))], 1, Mem_Length___unnamed_16_39e6661e[Length___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))])));
goto label_41_true , label_41_false ;


label_41_true :
assume (Off(Mem_ByteCapacity__DISKETTE_EXTENSION[ByteCapacity__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]) < Off(PLUS(Mem_LowPart___unnamed_8_34582070[LowPart___unnamed_8_34582070(__unnamed_8_34582070__LARGE_INTEGER(ByteOffset___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))))], 1, Mem_Length___unnamed_16_39e6661e[Length___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))])));
goto label_43;


label_41_false :
assume !(Off(Mem_ByteCapacity__DISKETTE_EXTENSION[ByteCapacity__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]) < Off(PLUS(Mem_LowPart___unnamed_8_34582070[LowPart___unnamed_8_34582070(__unnamed_8_34582070__LARGE_INTEGER(ByteOffset___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))))], 1, Mem_Length___unnamed_16_39e6661e[Length___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))])));
goto label_42;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2275)
label_42:
goto label_42_true , label_42_false ;


label_42_true :
assume (BIT_BAND(Mem_Length___unnamed_16_39e6661e[Length___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))], Ptr(Obj(Mem_BytesPerSector__DISKETTE_EXTENSION[BytesPerSector__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]), Off(Mem_BytesPerSector__DISKETTE_EXTENSION[BytesPerSector__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]) - 1)) != Ptr(null,0));
goto label_43;


label_42_false :
assume (BIT_BAND(Mem_Length___unnamed_16_39e6661e[Length___unnamed_16_39e6661e(Read___unnamed_16_c0f0e7de(Parameters__IO_STACK_LOCATION($irpSp$3$2230.23$)))], Ptr(Obj(Mem_BytesPerSector__DISKETTE_EXTENSION[BytesPerSector__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]), Off(Mem_BytesPerSector__DISKETTE_EXTENSION[BytesPerSector__DISKETTE_EXTENSION($disketteExtension$5$2232.24$)]) - 1)) == Ptr(null,0));
goto label_40;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2278)
label_43:
goto label_43_true , label_43_false ;


label_43_true :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 1)) != Ptr(null,0));
goto label_45;


label_43_false :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 1)) == Ptr(null,0));
goto label_44;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2280)
label_44:
goto label_44_true , label_44_false ;


label_44_true :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 2)) != Ptr(null,0));
goto label_50;


label_44_false :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 2)) == Ptr(null,0));
goto label_49;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2278)
label_45:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$DbgPrint.arg.1$6$ := havoc_stringTemp ;
goto label_46;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2278)
label_46:
havoc $result.DbgPrint$2278.0$5$;
// skip DbgPrint
goto label_44;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2290)
label_49:
$ntStatus$4$2231.13$ := Ptr(null, -1073741811) ;
goto label_54;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2280)
label_50:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$DbgPrint.arg.1$8$ := havoc_stringTemp ;
goto label_51;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2280)
label_51:
havoc $result.DbgPrint$2280.0$7$;
// skip DbgPrint
goto label_49;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2323)
label_54:
call ExReleaseFastMutex (HoldNewReqMutex__DISKETTE_EXTENSION($disketteExtension$5$2232.24$));
goto label_57;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2325)
label_57:
goto label_57_true , label_57_false ;


label_57_true :
assume ($ntStatus$4$2231.13$ != Ptr(null, 259));
goto label_59;


label_57_false :
assume !($ntStatus$4$2231.13$ != Ptr(null, 259));
goto label_58;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2333)
label_58:
$result.FloppyReadWrite$2203.0$1$ := $ntStatus$4$2231.13$ ;
goto label_1;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2326)
label_59:
Mem_Status___unnamed_4_c7b3d275[Status___unnamed_4_c7b3d275(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(IoStatus__IRP(Irp$1)))] := $ntStatus$4$2231.13$ ;
goto label_60;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2327)
label_60:
goto label_60_true , label_60_false ;


label_60_true :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 1)) != Ptr(null,0));
goto label_64;


label_60_false :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 1)) == Ptr(null,0));
goto label_61;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2330)
label_61:
call IofCompleteRequest (Irp$1, Ptr(null, 0));
goto label_58;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2327)
label_64:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$DbgPrint.arg.1$15$ := havoc_stringTemp ;
goto label_65;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2327)
label_65:
havoc $result.DbgPrint$2327.0$14$;
// skip DbgPrint
goto label_61;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2315)
label_68:
Mem_Information__IO_STATUS_BLOCK[Information__IO_STATUS_BLOCK(IoStatus__IRP(Irp$1))] := Ptr(null, 0) ;
goto label_78;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2305)
label_69:
goto label_69_true , label_69_false ;


label_69_true :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 16)) != Ptr(null,0));
goto label_73;


label_69_false :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 16)) == Ptr(null,0));
goto label_70;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2308)
label_70:
call $result.FlQueueIrpToThread$2308.41$11$ := FlQueueIrpToThread (Irp$1, $disketteExtension$5$2232.24$);
goto label_77;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2305)
label_73:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$DbgPrint.arg.1$10$ := havoc_stringTemp ;
goto label_74;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2305)
label_74:
havoc $result.DbgPrint$2305.0$9$;
// skip DbgPrint
goto label_70;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2308)
label_77:
$ntStatus$4$2231.13$ := $result.FlQueueIrpToThread$2308.41$11$ ;
goto label_54;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2316)
label_78:
Mem_Status___unnamed_4_c7b3d275[Status___unnamed_4_c7b3d275(__unnamed_4_c7b3d275__IO_STATUS_BLOCK(IoStatus__IRP(Irp$1)))] := Ptr(null, 0) ;
goto label_79;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2317)
label_79:
goto label_79_true , label_79_false ;


label_79_true :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 1)) != Ptr(null,0));
goto label_81;


label_79_false :
assume (BIT_BAND(Mem_UINT4[FloppyDebugLevel], Ptr(null, 1)) == Ptr(null,0));
goto label_80;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2319)
label_80:
$ntStatus$4$2231.13$ := Ptr(null, 0) ;
goto label_54;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2317)
label_81:
call havoc_stringTemp := __HAVOC_malloc_stack(Ptr(null,1));
$DbgPrint.arg.1$13$ := havoc_stringTemp ;
goto label_82;


// c:\nt\drivers\storage\fdc\flpydisk\floppy.c(2317)
label_82:
havoc $result.DbgPrint$2317.0$12$;
// skip DbgPrint
goto label_80;

}

