
type {:datatype} DotNetType;

/*\
 *  Subtype Axioms
\*/
function $Subtype(DotNetType, DotNetType) : bool;
// reflexive
axiom (forall t: DotNetType :: $Subtype(t, t));
// anti-symmetric
axiom (forall t0: DotNetType, t1: DotNetType :: { $Subtype(t0, t1), $Subtype(t1, t0) } $Subtype(t0, t1) && $Subtype(t1, t0) ==> t0 == t1);
// transitive
axiom (forall t0: DotNetType, t1: DotNetType, t2: DotNetType :: { $Subtype(t0, t1), $Subtype(t1, t2) } $Subtype(t0, t1) && $Subtype(t1, t2) ==> $Subtype(t0, t2));

/*\
 *  Type Declarations
\*/
// class System.Object { ... }
function {:constructor} System.Object() : DotNetType;

// class B : System.Object { ... }
function {:constructor} B() : DotNetType;
axiom $Subtype(B(), System.Object());

// class GenericType1<T> : System.Object { ... }
function {:constructor} GenericType1(T:DotNetType) : DotNetType;
axiom (forall t : DotNetType :: $Subtype(GenericType1(t), System.Object()));

// class C : GenericType1<object>
function {:constructor} C() : DotNetType;
axiom $Subtype(C(), GenericType1(System.Object()));

// class D<U> : GenericType1<U>
function {:constructor} D(U:DotNetType) : DotNetType;
axiom (forall u : DotNetType :: $Subtype(D(u), GenericType1(u)));

// class GenericType2<T,U> : System.Object { ... }
function {:constructor} GenericType2(T:DotNetType, U:DotNetType) : DotNetType;
axiom (forall t : DotNetType, u : DotNetType :: $Subtype(GenericType2(t,u), System.Object()));

procedure foo(t : DotNetType) 
{
  assert System.Object() != GenericType1(t);
  assert System.Object() != B();
}

procedure bar(t : DotNetType, u : DotNetType) 
  requires t != u;
{
  assert System.Object() != GenericType1(t);
  assert System.Object() != B();
  assert GenericType1(t) != GenericType1(u);
}

