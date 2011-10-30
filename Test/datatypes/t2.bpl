
type {:datatype} DotNetType;

// class System.Object { ... }
function {:constructor} System.Object() : DotNetType;

// class NominalType2 : System.Object { ... }
function {:constructor} NominalType2() : DotNetType;
axiom $Subtype(NominalType2(), System.Object());

// class GenericType1<T> : System.Object { ... }
function {:constructor} GenericType1(T:DotNetType) : DotNetType;
axiom (forall t : DotNetType :: $Subtype(GenericType1(t), System.Object()));

function $Subtype(DotNetType, DotNetType) : bool;
// reflexive
axiom (forall t: DotNetType :: $Subtype(t, t));
// anti-symmetric
axiom (forall t0: DotNetType, t1: DotNetType :: { $Subtype(t0, t1), $Subtype(t1, t0) } $Subtype(t0, t1) && $Subtype(t1, t0) ==> t0 == t1);
// transitive
axiom (forall t0: DotNetType, t1: DotNetType, t2: DotNetType :: { $Subtype(t0, t1), $Subtype(t1, t2) } $Subtype(t0, t1) && $Subtype(t1, t2) ==> $Subtype(t0, t2));

procedure foo(t : DotNetType) 
{
  assert System.Object() != GenericType1(t);
  assert System.Object() != NominalType2();
}

procedure bar(t : DotNetType, u : DotNetType) 
  requires t != u;
{
  assert System.Object() != GenericType1(t);
  assert System.Object() != NominalType2();
  assert GenericType1(t) != GenericType1(u);
}

