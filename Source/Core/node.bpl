datatype Node<T> { Node(next: Option Loc, val: T) }

function Between<T>(f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc): bool;
function Avoiding<T>(f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc): bool;
function {:inline} BetweenSet<T>(f:[One Loc]Node T, x: Option Loc, z: Option Loc): [Loc]bool
{
  (lambda y: Loc :: Between(f, x, Some(y), z))
}

// reflexive
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc :: Between(f, x, x, x));

// step
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Loc ::
  {f[One(x)]}
  Between(f, Some(x), f[One(x)]->next, f[One(x)]->next));

// reach
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Loc, y: Option Loc ::
  {f[One(x)], Between(f, Some(x), y, y)}
  Between(f, Some(x), y, y) ==> Some(x) == y || Between(f, Some(x), f[One(x)]->next, y));

// cycle
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Loc, y: Option Loc ::
  {f[One(x)], Between(f, Some(x), y, y)}
  f[One(x)]->next == Some(x) && Between(f, Some(x), y, y) ==> Some(x) == y);

// sandwich
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc ::
  {Between(f, x, y, x)}
  Between(f, x, y, x) ==> x == y);

// order1
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc ::
  {Between(f, x, y, y), Between(f, x, z, z)}
  Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc ::
  {Between(f, x, y, z)}
  Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc ::
  {Between(f, x, y, y), Between(f, y, z, z)}
  Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc, w: Option Loc ::
  {Between(f, x, y, z), Between(f, y, w, z)}
  Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc, w: Option Loc ::
  {Between(f, x, y, z), Between(f, x, w, y)}
  Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, u: Option Loc, x: Option Loc ::
  {Between(f, u, x, x)}
  Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc ::
  {Avoiding(f, x, y, z)}
  Avoiding(f, x, y, z) <==> Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z)));
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, x: Option Loc, y: Option Loc, z: Option Loc ::
  {Between(f, x, y, z)}
  Between(f, x, y, z) <==> Avoiding(f, x, y, z) && Avoiding(f, x, z, z));

// update
axiom {:ctor "Node"} (forall<T> f: [One Loc]Node T, u: Option Loc, v: Option Loc, x: Option Loc, p: Loc, q: Node T ::
  {Avoiding(f[One(p) := q], u, v, x)}
  Avoiding(f[One(p) := q], u, v, x) <==>
    (Avoiding(f, u, v, Some(p)) && Avoiding(f, u, v, x)) || 
    (Avoiding(f, u, Some(p), x) && Some(p) != x && Avoiding(f, q->next, v, Some(p)) && Avoiding(f, q->next, v, x))
);
