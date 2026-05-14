function VecRev<T>(v: Vec T): Vec T;
axiom (forall<T> v: Vec T :: Vec_Len(VecRev(v)) == Vec_Len(v));
axiom (forall<T> v: Vec T, i: int ::
  {Vec_Nth(VecRev(v), i)}
  0 <= i && i < Vec_Len(v) ==> Vec_Nth(VecRev(v), i) == Vec_Nth(v, Vec_Len(v) - 1 - i));
axiom (forall<T> v: Vec T, x: T ::
  {VecRev(Vec_Append(v, x))}
  VecRev(Vec_Append(v, x)) == Vec_Concat(Vec_Append(Vec_Empty(), x), VecRev(v)));

datatype List { List(head: Option Loc, nodes: Map (One Loc) (Node int)) }

function {:inline} IsReversalOf(l_out: List, l_in: List): bool {
  StackAbs(l_out->head, l_out->nodes) == VecRev(StackAbs(l_in->head, l_in->nodes))
}

function {:inline} WF(l: List): bool {
  l->head is Some &&
  Map_Contains(l->nodes, One(l->head->t)) &&
  Reachable(l->nodes, l->head, None()) &&
  InDomain(l->nodes, l->head)
}

// Vec algebra lemma: splits the first element of B out of Vec_Concat(A, B) into
// the tail of A.
pure procedure VecConcatAppendLemma<T>(A: Vec T, v: T, B: Vec T)
ensures Vec_Concat(A, Vec_Concat(Vec_Append(Vec_Empty(), v), B)) == Vec_Concat(Vec_Append(A, v), B);
{ }

// ReverseStepLemma: one iteration of Reverse preserves the StackAbs invariant.
//
// Called BEFORE the destructive Map_Get/Map_Put.  All parameters are
// non-linear, so the lemma can freely consult the OLD maps while predicting
// the NEW maps via Map_Remove / Map_Update.  The ensures clause is phrased so
// that after the body's mutations (which produce exactly these expressions),
// Z3 can match the new variable values against the lemma's conclusion.
pure procedure ReverseStepLemma(
    in_h: Option Loc, in_n: Map (One Loc) (Node int),
    rem_h: Option Loc, rem_n: Map (One Loc) (Node int),
    acc_h: Option Loc, acc_n: Map (One Loc) (Node int))
requires rem_h is Some;
requires Map_Contains(rem_n, One(rem_h->t));
requires Reachable(rem_n, rem_h, None());
requires InDomain(rem_n, rem_h);
requires Reachable(acc_n, acc_h, None());
requires InDomain(acc_n, acc_h);
requires !Map_Contains(acc_n, One(rem_h->t));
requires VecRev(StackAbs(in_h, in_n)) ==
         Vec_Concat(StackAbs(acc_h, acc_n), VecRev(StackAbs(rem_h, rem_n)));
ensures VecRev(StackAbs(in_h, in_n)) ==
        Vec_Concat(
          StackAbs(rem_h, Map_Update(acc_n, One(rem_h->t),
                                     Node(acc_h, Map_At(rem_n, One(rem_h->t))->val))),
          VecRev(StackAbs(Map_At(rem_n, One(rem_h->t))->next,
                          Map_Remove(rem_n, One(rem_h->t)))));
{
  // Unfold StackAbs(rem_h, rem_n) on the old remaining list.
  call StackAbsLemma(rem_h, rem_n);

  // Unfold StackAbs(rem_h, new_acc_n) on the new accumulator at its new head.
  // Map_At(new_acc_n, One(rem_h->t)) = Node(acc_h, v), so this yields
  //   Vec_Append(StackAbs(acc_h, new_acc_n), v).
  call StackAbsLemma(rem_h,
                     Map_Update(acc_n, One(rem_h->t),
                                Node(acc_h, Map_At(rem_n, One(rem_h->t))->val)));

  // Frame: extending acc_n with the fresh entry One(rem_h->t) does not affect
  // StackAbs starting from acc_h.
  call StackFrameLemma(acc_h, acc_n,
                       Map_Update(acc_n, One(rem_h->t),
                                  Node(acc_h, Map_At(rem_n, One(rem_h->t))->val)));

  // Frame: removing One(rem_h->t) from rem_n does not affect StackAbs starting
  // from the next node (it isn't on the rest of the chain).
  call StackFrameLemma(Map_At(rem_n, One(rem_h->t))->next,
                       Map_Remove(rem_n, One(rem_h->t)),
                       rem_n);

  // Vec algebra to re-associate the concat with the new element.
  call VecConcatAppendLemma(StackAbs(acc_h, acc_n),
                            Map_At(rem_n, One(rem_h->t))->val,
                            VecRev(StackAbs(Map_At(rem_n, One(rem_h->t))->next,
                                            Map_Remove(rem_n, One(rem_h->t)))));
}

pure procedure {:vcs_split_on_every_assert} Reverse({:linear_in} l_in: List) returns ({:linear} l_out: List)
requires WF(l_in);
ensures WF(l_out);
ensures IsReversalOf(l_out, l_in);
{
  var l_rem_head: Option Loc;
  var l_rem_nodes: Map (One Loc) (Node int);
  var l_acc_head: Option Loc;
  var l_acc_nodes: Map (One Loc) (Node int);
  var one_loc: One Loc;
  var curr_node: Node int;
  var old_next: Option Loc;

  List(l_rem_head, l_rem_nodes) := l_in;
  call l_acc_nodes := Map_MakeEmpty();
  l_acc_head := None();

  // Establish initial StackAbs of the empty accumulator.
  call StackAbsLemma(None(), l_acc_nodes);

  while (l_rem_head != None())
    invariant l_rem_head is Some ==> Map_Contains(l_rem_nodes, One(l_rem_head->t));
    invariant l_rem_head is Some ==> Reachable(l_rem_nodes, l_rem_head, None());
    invariant InDomain(l_rem_nodes, l_rem_head);
    invariant InDomain(l_acc_nodes, l_acc_head);
    invariant Reachable(l_acc_nodes, l_acc_head, None());
    invariant l_acc_head is Some ==> Map_Contains(l_acc_nodes, One(l_acc_head->t));
    invariant l_rem_head is None ==> l_acc_head is Some;
    invariant Set_IsDisjoint(l_rem_nodes->dom, l_acc_nodes->dom);
    invariant VecRev(StackAbs(l_in->head, l_in->nodes)) ==
        Vec_Concat(StackAbs(l_acc_head, l_acc_nodes), VecRev(StackAbs(l_rem_head, l_rem_nodes)));
  {
    one_loc := One(l_rem_head->t);

    // Prove the invariant for the next state in terms of the current state.
    // After the mutations below, the new l_acc_nodes equals
    //   Map_Update(l_acc_nodes_old, one_loc, Node(l_acc_head_old, v))
    // and the new l_rem_nodes equals Map_Remove(l_rem_nodes_old, one_loc), so
    // the ensures of ReverseStepLemma matches the post-state shape.
    call ReverseStepLemma(l_in->head, l_in->nodes,
                          l_rem_head, l_rem_nodes,
                          l_acc_head, l_acc_nodes);

    call curr_node := Map_Get(l_rem_nodes, one_loc);
    old_next := curr_node->next;
    call Map_Put(l_acc_nodes, one_loc, Node(l_acc_head, curr_node->val));
    l_acc_head := l_rem_head;
    l_rem_head := old_next;
  }

  call StackAbsLemma(None(), l_rem_nodes);
  l_out := List(l_acc_head, l_acc_nodes);
}
