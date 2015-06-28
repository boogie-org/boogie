// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


function size<alpha>(x : alpha) returns (int);

axiom (forall x:int :: size(x) == 0);
axiom (forall<alpha> x:alpha :: size(x) >= 0);

axiom (forall m:[int]int, x:int :: size(m) >= m[x]);
axiom (forall m:<a>[a]int :: size(m) == 13);

type Field a;

function fieldValue<a>(ref, Field a) returns (a);

const intField : Field int;
const refField : Field ref;
const obj : ref;
const someInt : int;

axiom someInt == fieldValue(obj, intField);
axiom someInt == fieldValue(fieldValue(obj, refField), intField);

axiom someInt == fieldValue(obj, fieldValue(obj, refField)); // error: wrong argument type

axiom (forall<a> f : Field a ::
           (exists x:a :: fieldValue(obj, f) == x));

axiom (forall<beta, alpha> a:alpha, b:beta ::
              a == b ==> (exists c:alpha :: c == b));
axiom (forall<a> f : Field a ::
           (exists<b> x:b :: fieldValue(obj, f) == x));
axiom (forall<a> f : Field a ::
           (exists x:int :: fieldValue(obj, f) == x));

function lessThan<a>(x : a, y : a) returns (bool);

axiom (forall x:int, y:int :: x < y ==> lessThan(x, y));
axiom lessThan(false, true);

axiom lessThan(5, true);                          // error: incompatible arguments
axiom (forall<a,b> x:a, y:b :: lessThan(x, y));   // error: incompatible arguments

function lessThan2<a,b>(x : a, y : b) returns (bool);

axiom (forall<a> x:a, y:a :: lessThan(x,y) == lessThan2(x,y));
axiom (forall<a> x:a :: (exists m:a :: (forall y:a :: lessThan2(m, y))));

axiom (exists<a,b> x:a, y:b :: lessThan2(x, y) == lessThan2(y, x));

axiom (exists<a,b> x:<c>[Field c]a, y:<d>[Field d]b :: x == y);
axiom (exists<a> x:<c>[Field c]a, y:<d>[Field d]int :: x == y);
axiom (exists<a> x:<c>[Field c]int, y:<d>[Field d]a :: x == y);
axiom (exists<a> x:<c>[Field c]a, y:<d>[Field d]d :: x == y);   // error: not unifiable

type ref;
