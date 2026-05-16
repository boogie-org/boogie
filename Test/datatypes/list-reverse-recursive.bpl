// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
  Linked list with nested permissions, translated from the NPL example in
  "Nested Permissions for Disjointness Reasoning" (Section 2).

  NPL definition:
    struct List { data: int, next: Option<Loc<List>>, lin lheap: Map<Loc<List>, List> }

  Each node owns its subtree's permissions in its lheap. Global disjointness
  (enforced by linearity) implies the structure is acyclic.

  Civl translation uses the erasure semantics (Section 5): all nested lheaps
  are merged into a single flat linear map. A "List" value bundles a head
  pointer with linear ownership of all reachable nodes. The linear type system
  enforces that no two List values share nodes, preserving the NPL invariant.
*/

/// VecRev: reverse of a vector, characterised by its length and index axioms,
/// plus the reverse-of-append identity needed for the ReverseHelper invariant.
function VecRev<T>(v: Vec T): Vec T;
axiom (forall<T> v: Vec T :: Vec_Len(VecRev(v)) == Vec_Len(v));
axiom (forall<T> v: Vec T, i: int ::
  {Vec_Nth(VecRev(v), i)}
  0 <= i && i < Vec_Len(v) ==> Vec_Nth(VecRev(v), i) == Vec_Nth(v, Vec_Len(v) - 1 - i));
// rev([a1,...,an,x]) == [x] ++ rev([a1,...,an])
axiom (forall<T> v: Vec T, x: T ::
  {VecRev(Vec_Append(v, x))}
  VecRev(Vec_Append(v, x)) == Vec_Concat(Vec_Append(Vec_Empty(), x), VecRev(v)));

/// Vec algebra lemma: splits the first element of B out of Vec_Concat(A, B)
/// into the tail of A.  Same trick as the iterative version uses.
pure procedure VecConcatAppendLemma<T>(A: Vec T, v: T, B: Vec T)
ensures Vec_Concat(A, Vec_Concat(Vec_Append(Vec_Empty(), v), B)) == Vec_Concat(Vec_Append(A, v), B);
{ }

datatype List { List(head: Option Loc, nodes: Map (One Loc) (Node int)) }

// WF: lists are non-empty, the head node is in the map, and all reachable
// nodes are in the map (so the structure is self-contained).
function {:inline} WF(l: List): bool {
  l->head is Some &&
  Map_Contains(l->nodes, One(l->head->t)) &&
  Reachable(l->nodes, l->head, None()) &&
  InDomain(l->nodes, l->head)
}

/// IsReversalOf: the sequence abstraction of l_out is the reverse of l_in's.
/// Uses StackAbs from node.bpl, which maps a linked list to a Vec with the
/// tail element at index 0 and the head element at index len-1.
function {:inline} IsReversalOf(l_out: List, l_in: List): bool {
  StackAbs(l_out->head, l_out->nodes) == VecRev(StackAbs(l_in->head, l_in->nodes))
}

/// Singleton: allocate a one-element list holding d.
pure procedure Singleton(d: int) returns ({:linear} l: List)
ensures WF(l);
ensures Map_At(l->nodes, One(l->head->t))->val == d;
ensures Map_At(l->nodes, One(l->head->t))->next == None();
{
  var nodes: Map (One Loc) (Node int);
  var loc_p: One Loc;

  call nodes := Map_MakeEmpty();
  call loc_p := Loc_New();
  call Map_Put(nodes, loc_p, Node(None(), d));
  l := List(Some(loc_p->val), nodes);
}

/// Cons: prepend d to an existing well-formed list tl.
/// The head of tl becomes the next pointer of the new node.
pure procedure Cons(d: int, {:linear_in} tl: List) returns ({:linear} l: List)
requires WF(tl);
ensures WF(l);
ensures Map_At(l->nodes, One(l->head->t))->val == d;
ensures Map_At(l->nodes, One(l->head->t))->next == tl->head;
{
  var tl_head: Option Loc;
  var nodes: Map (One Loc) (Node int);
  var loc_p: One Loc;

  List(tl_head, nodes) := tl;
  call loc_p := Loc_New();
  call Map_Put(nodes, loc_p, Node(tl_head, d));
  l := List(Some(loc_p->val), nodes);
}

/// ReverseHelper: tail-recursive in-place reversal.
///
/// The reversed prefix (prev_head, prev_nodes) and the unprocessed input list
/// l_in are kept in two SEPARATE linear maps.  Civl's linear type system
/// enforces their disjointness automatically — no explicit disjointness
/// invariant is needed.  Each call removes the head from l_in, inserts it into
/// prev_nodes with its next pointer rewritten to prev_head, then either
/// bottoms out (forward suffix empty) or recurses on the rest.
pure procedure {:vcs_split_on_every_assert} ReverseHelper(
    {:linear_in} l_in: List,
    prev_head: Option Loc,
    {:linear_in} prev_nodes: Map (One Loc) (Node int))
    returns (new_head: Loc, {:linear} l_out: List)
requires WF(l_in);
requires Reachable(prev_nodes, prev_head, None());
requires InDomain(prev_nodes, prev_head);
ensures WF(l_out);
ensures l_out->head == Some(new_head);
// StackAbs invariant: result's abstraction == reversed prefix ++ VecRev(input).
ensures StackAbs(l_out->head, l_out->nodes) ==
        Vec_Concat(StackAbs(prev_head, prev_nodes),
                   VecRev(StackAbs(l_in->head, l_in->nodes)));
{
  var head: Option Loc;
  var l_in_nodes: Map (One Loc) (Node int);
  var p_nodes: Map (One Loc) (Node int);
  var loc_p: One Loc;
  var hd_node: Node int;
  var tail: List;

  // Destructure both linear inputs into mutable locals.
  List(head, l_in_nodes) := l_in;
  p_nodes := prev_nodes;

  loc_p := One(head->t);
  call hd_node := Map_Get(l_in_nodes, loc_p);
  call Map_Put(p_nodes, loc_p, Node(prev_head, hd_node->val));

  // Lemma calls — these establish the StackAbs facts we need, on the
  // post-Map_Get/post-Map_Put values of l_in_nodes and p_nodes.

  // (1) StackAbs(l_in->head, l_in->nodes) = Vec_Append(StackAbs(hd_node->next, l_in->nodes), V).
  call StackAbsLemma(l_in->head, l_in->nodes);

  // (2) StackAbs(hd_node->next, l_in_nodes) = StackAbs(hd_node->next, l_in->nodes).
  //     l_in_nodes is l_in->nodes minus head->t; hd_node->next's chain doesn't visit head->t.
  call StackFrameLemma(hd_node->next, l_in_nodes, l_in->nodes);

  // (3) StackAbs(prev_head, prev_nodes) = StackAbs(prev_head, p_nodes).
  //     p_nodes is prev_nodes plus the fresh head->t entry; prev_head's path doesn't visit it.
  call StackFrameLemma(prev_head, prev_nodes, p_nodes);

  // (4) StackAbs(Some(head->t), p_nodes) = Vec_Append(StackAbs(prev_head, p_nodes), V).
  call StackAbsLemma(Some(head->t), p_nodes);

  if (hd_node->next == None()) {
    // Base: l_in_nodes is empty (l_in's chain was just {head->t}).
    new_head := head->t;
    l_out := List(Some(head->t), p_nodes);

    // StackAbs(None(), l_in->nodes) = Vec_Empty().
    call StackAbsLemma(None(), l_in->nodes);
    // Vec algebra: Vec_Append(A, V) == Vec_Concat(A, Vec_Concat([V], Vec_Empty())).
    call VecConcatAppendLemma(StackAbs(prev_head, prev_nodes), hd_node->val, Vec_Empty());
  } else {
    // Inductive: recurse on the unprocessed suffix.
    tail := List(hd_node->next, l_in_nodes);
    call new_head, l_out := ReverseHelper(tail, Some(head->t), p_nodes);

    // From the recursive ensures (with prev_head_inner = Some(head->t),
    // prev_nodes_inner = p_nodes at call):
    //   StackAbs(l_out->head, l_out->nodes)
    //     = Vec_Concat(StackAbs(Some(head->t), p_nodes),
    //                  VecRev(StackAbs(hd_node->next, l_in_nodes_at_call))).
    // Substituting (4), (3), (2), (1) above gives the goal via VecConcatAppendLemma.
    call VecConcatAppendLemma(StackAbs(prev_head, prev_nodes),
                              hd_node->val,
                              VecRev(StackAbs(hd_node->next, l_in->nodes)));
  }
}

/// Reverse (in-place): reverse the list by rewriting next pointers.
/// The same set of Loc values is reused — no allocation occurs.
/// The original tail becomes the new head.
/// Verified: l_out is the reversal of l_in in the StackAbs sense.
pure procedure Reverse({:linear_in} l_in: List) returns ({:linear} l_out: List)
requires WF(l_in);
ensures WF(l_out);
ensures IsReversalOf(l_out, l_in);
{
  var new_head: Loc;
  var empty_nodes: Map (One Loc) (Node int);

  call empty_nodes := Map_MakeEmpty();
  call new_head, l_out := ReverseHelper(l_in, None(), empty_nodes);

  // From ReverseHelper, with prev_head = None() and prev_nodes = empty:
  //   StackAbs(l_out->head, l_out->nodes)
  //     == Vec_Concat(StackAbs(None(), empty), VecRev(StackAbs(l_in->head, l_in->nodes)))
  // StackAbsLemma(None(), empty) gives StackAbs(None(), empty) == Vec_Empty(),
  // so the concat simplifies to VecRev(StackAbs(l_in->head, l_in->nodes)).
  call StackAbsLemma(None(), empty_nodes);
}
