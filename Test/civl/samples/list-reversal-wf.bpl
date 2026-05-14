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

datatype List { List(head: Option Loc, nodes: Map (One Loc) (Node int)) }

// WF: lists are non-empty, the head node is in the map, and all reachable
// nodes are in the map (so the structure is self-contained).
function {:inline} WF(l: List): bool {
  l->head is Some &&
  Map_Contains(l->nodes, One(l->head->t)) &&
  Reachable(l->nodes, l->head, None()) &&
  InDomain(l->nodes, l->head)
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
/// Takes {:linear_in} l_in so that destructuring gives a LOCAL `nodes` variable,
/// which is required for Map_Get/Map_Put to type-check (parameters cannot be
/// used as linear paths to primitives — only local variables can).
///
/// Each call: rewrites the head node's next pointer to prev_head (the
/// already-reversed prefix), then recurses on List(old_next, nodes).
/// Returns (new_head, bag-of-reversed-nodes); new_head is the original tail.
/// No new Loc is allocated: l_out->nodes->dom == l_in->nodes->dom.
pure procedure {:vcs_split_on_every_assert} ReverseHelper({:linear_in} l_in: List,
                              prev_head: Option Loc)
    returns (new_head: Loc, {:linear} l_out: List)
requires WF(l_in);
requires InDomain(l_in->nodes, prev_head);
ensures l_out->nodes->dom == l_in->nodes->dom;
ensures Map_Contains(l_out->nodes, One(new_head));
ensures Reachable(l_out->nodes, Some(new_head), prev_head);
ensures InDomain(l_out->nodes, Some(new_head));
// Frame: nodes not on the original forward path from l_in->head to None() are unchanged.
ensures (forall x: Loc ::
    !Between(l_in->nodes->val, l_in->head, Some(x), None())
    ==> Map_At(l_out->nodes, One(x)) == Map_At(l_in->nodes, One(x)));
{
  var head: Option Loc;
  var nodes: Map (One Loc) (Node int);
  var loc_p: One Loc;
  var hd_node: Node int;
  var tail: List;
  var new_head_inner: Loc;
  var l_out_inner: List;
  var inner_head: Option Loc;
  var inner_nodes: Map (One Loc) (Node int);

  // Destructure l_in: nodes is now a local variable.
  List(head, nodes) := l_in;
  loc_p := One(head->t);
  call hd_node := Map_Get(nodes, loc_p);
  // Redirect this node's next pointer to the already-reversed prefix.
  call Map_Put(nodes, loc_p, Node(prev_head, hd_node->val));

  if (hd_node->next == None()) {
    // This was the original tail; it becomes the new head of the reversed list.
    new_head := head->t;
    l_out := List(head, nodes);
  } else {
    // head->t points to prev_head now; hd_node->next starts the unreversed suffix.
    // head->t is not on the forward path from hd_node->next (acyclicity of original list),
    // so the recursive call will not modify it (frame condition).
    tail := List(hd_node->next, nodes);
    assert !Between(nodes->val, hd_node->next, Some(head->t), None());
    call new_head_inner, l_out_inner := ReverseHelper(tail, Some(head->t));
    List(inner_head, inner_nodes) := l_out_inner;
    // Frame: head->t was not on the forward path, so it's unchanged by the recursive call.
    assert Map_At(inner_nodes, One(head->t))->next == prev_head;
    // Step axiom: from Some(head->t), one step reaches prev_head.
    assert Between(inner_nodes->val, Some(head->t), prev_head, prev_head);
    new_head := new_head_inner;
    l_out := List(head, inner_nodes);
  }
}

/// Reverse (in-place): reverse the list by rewriting next pointers.
/// The same set of Loc values is reused — no allocation occurs.
/// The original tail becomes the new head.
pure procedure Reverse({:linear_in} l_in: List) returns ({:linear} l_out: List)
requires WF(l_in);
ensures WF(l_out);
ensures l_out->nodes->dom == l_in->nodes->dom;
{
  var new_head: Loc;
  var helper_out: List;
  var helper_head: Option Loc;
  var result_nodes: Map (One Loc) (Node int);

  call new_head, helper_out := ReverseHelper(l_in, None());
  List(helper_head, result_nodes) := helper_out;
  l_out := List(Some(new_head), result_nodes);
}
