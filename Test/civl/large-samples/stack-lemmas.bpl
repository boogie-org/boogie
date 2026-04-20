// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

implementation StackAbsCompute<V>(start: Option Loc, nodes: Map (One Loc) (Node V), nodes': Map (One Loc) (Node V)) returns (absStack: Vec V)
{
  var loc_n: Option Loc;
  var n: Node V;

  if (start == None()) {
      absStack := Vec_Empty();
  } else {
      loc_n := start;
      assert Map_Contains(nodes, One(loc_n->t));
      n := Map_At(nodes, One(loc_n->t));
      // Use well-founded list reachability to prove that recursion will terminate:
      // start@caller --> start@callee --> None()
      assert Between(nodes->val, loc_n, n->next, None());
      call absStack := StackAbsCompute(n->next, nodes, nodes');
      absStack := Vec_Append(absStack, n->val);
  }
}

implementation StackAbsLemma<V>(start: Option Loc, nodes: Map (One Loc) (Node V))
{
  var absStack: Vec V;
  call absStack := StackAbsCompute(start, nodes, nodes);
}

implementation StackFrameLemma<V>(start: Option Loc, nodes: Map (One Loc) (Node V), nodes': Map (One Loc) (Node V))
{
  var absStack: Vec V;
  call absStack := StackAbsCompute(start, nodes, nodes');
}