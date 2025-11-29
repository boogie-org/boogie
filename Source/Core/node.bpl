datatype Node<T> { Node(next: Option (Loc (Node T)), val: T) }
type LocNode T = Loc (Node T);

function Between<T>(f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T))): bool;
function Avoiding<T>(f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T))): bool;
function {:inline} BetweenSet<T>(f:[One (Loc (Node T))]Node T, x: Option (Loc (Node T)), z: Option (Loc (Node T))): [Loc (Node T)]bool
{
  (lambda y: Loc (Node T) :: Between(f, x, Some(y), z))
}

// reflexive
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)) :: Between(f, x, x, x));

// step
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Loc (Node T) ::
  {f[One(x)]}
  Between(f, Some(x), f[One(x)]->next, f[One(x)]->next));

// reach
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Loc (Node T), y: Option (Loc (Node T)) ::
  {f[One(x)], Between(f, Some(x), y, y)}
  Between(f, Some(x), y, y) ==> Some(x) == y || Between(f, Some(x), f[One(x)]->next, y));

// cycle
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Loc (Node T), y: Option (Loc (Node T)) ::
  {f[One(x)], Between(f, Some(x), y, y)}
  f[One(x)]->next == Some(x) && Between(f, Some(x), y, y) ==> Some(x) == y);

// sandwich
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)) ::
  {Between(f, x, y, x)}
  Between(f, x, y, x) ==> x == y);

// order1
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T)) ::
  {Between(f, x, y, y), Between(f, x, z, z)}
  Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T)) ::
  {Between(f, x, y, z)}
  Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T)) ::
  {Between(f, x, y, y), Between(f, y, z, z)}
  Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T)), w: Option (Loc (Node T)) ::
  {Between(f, x, y, z), Between(f, y, w, z)}
  Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T)), w: Option (Loc (Node T)) ::
  {Between(f, x, y, z), Between(f, x, w, y)}
  Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, u: Option (Loc (Node T)), x: Option (Loc (Node T)) ::
  {Between(f, u, x, x)}
  Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T)) ::
  {Avoiding(f, x, y, z)}
  Avoiding(f, x, y, z) <==> Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z)));
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, x: Option (Loc (Node T)), y: Option (Loc (Node T)), z: Option (Loc (Node T)) ::
  {Between(f, x, y, z)}
  Between(f, x, y, z) <==> Avoiding(f, x, y, z) && Avoiding(f, x, z, z));

// update
axiom {:ctor "Node"} (forall<T> f: [One (Loc (Node T))]Node T, u: Option (Loc (Node T)), v: Option (Loc (Node T)), x: Option (Loc (Node T)), p: Loc (Node T), q: Node T ::
  {Avoiding(f[One(p) := q], u, v, x)}
  Avoiding(f[One(p) := q], u, v, x) <==>
    (Avoiding(f, u, v, Some(p)) && Avoiding(f, u, v, x)) || 
    (Avoiding(f, u, Some(p), x) && Some(p) != x && Avoiding(f, q->next, v, Some(p)) && Avoiding(f, q->next, v, x))
);
