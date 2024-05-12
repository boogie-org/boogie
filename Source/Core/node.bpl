datatype Node<K,T> { Node(next: Option K, val: T) }

function Between<K,T>(f: [K]Node K T, x: Option K, y: Option K, z: Option K): bool;
function Avoiding<K,T>(f: [K]Node K T, x: Option K, y: Option K, z: Option K): bool;
function {:inline} BetweenSet<K,T>(f:[K]Node K T, x: Option K, z: Option K): [K]bool
{
  (lambda y: K :: Between(f, x, Some(y), z))
}

// reflexive
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K :: Between(f, x, x, x));

// step
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: K :: 
  {f[x]} 
  Between(f, Some(x), f[x]->next, f[x]->next));

// reach
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: K, y: Option K :: 
  {f[x], Between(f, Some(x), y, y)} 
  Between(f, Some(x), y, y) ==> Some(x) == y || Between(f, Some(x), f[x]->next, y));

// cycle
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: K, y: Option K :: 
  {f[x], Between(f, Some(x), y, y)} 
  f[x]->next == Some(x) && Between(f, Some(x), y, y) ==> Some(x) == y);

// sandwich
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K :: 
  {Between(f, x, y, x)} 
  Between(f, x, y, x) ==> x == y);

// order1
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K, z: Option K :: 
  {Between(f, x, y, y), Between(f, x, z, z)} 
  Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K, z: Option K :: 
  {Between(f, x, y, z)} 
  Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K, z: Option K :: 
  {Between(f, x, y, y), Between(f, y, z, z)} 
  Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K, z: Option K, w: Option K :: 
  {Between(f, x, y, z), Between(f, y, w, z)} 
  Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K, z: Option K, w: Option K :: 
  {Between(f, x, y, z), Between(f, x, w, y)} 
  Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, u: Option K, x: Option K :: 
  {Between(f, u, x, x)} 
  Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K, z: Option K :: 
  {Avoiding(f, x, y, z)} 
  Avoiding(f, x, y, z) <==> Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z)));
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, x: Option K, y: Option K, z: Option K :: 
  {Between(f, x, y, z)} 
  Between(f, x, y, z) <==> Avoiding(f, x, y, z) && Avoiding(f, x, z, z));

// update
axiom {:ctor "Node"} (forall<K,T> f: [K]Node K T, u: Option K, v: Option K, x: Option K, p: K, q: Node K T :: 
  {Avoiding(f[p := q], u, v, x)} 
  Avoiding(f[p := q], u, v, x) <==>
    (Avoiding(f, u, v, Some(p)) && Avoiding(f, u, v, x)) || 
    (Avoiding(f, u, Some(p), x) && Some(p) != x && Avoiding(f, q->next, v, Some(p)) && Avoiding(f, q->next, v, x))
);
