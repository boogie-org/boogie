// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// Stack abstraction
pure procedure StackAbsCompute<V>(start: Option Loc, nodes: Map (One Loc) (Node V), nodes': Map (One Loc) (Node V))
  returns (absStack: Vec V)
requires Set_IsSubset(nodes->dom, nodes'->dom);
requires MapIte(nodes->dom, nodes->val, MapConst(Default())) ==
         MapIte(nodes->dom, nodes'->val, MapConst(Default()));
requires InDomain(nodes, start);
ensures absStack == StackAbsDef(start, nodes);
ensures absStack == StackAbsDef(start, nodes');
free ensures absStack == StackAbs(start, nodes);
free ensures absStack == StackAbs(start, nodes');
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

/// Set abstraction
pure procedure SetAbsCompute<V>(start: Option Loc, nodes: Map (One Loc) (Node V), nodes': Map (One Loc) (Node V))
  returns (absSet: [V]bool)
requires Set_IsSubset(nodes->dom, nodes'->dom);
requires MapIte(nodes->dom, nodes->val, MapConst(Default())) ==
         MapIte(nodes->dom, nodes'->val, MapConst(Default()));
requires InDomain(nodes, start);
ensures absSet == SetAbsDef(start, nodes);
ensures absSet == SetAbsDef(start, nodes');
free ensures absSet == SetAbs(start, nodes);
free ensures absSet == SetAbs(start, nodes');
{
  var loc_n: Option Loc;
  var n: Node V;

  if (start == None()) {
      absSet := Set_Empty();
  } else {
      loc_n := start;
      assert Map_Contains(nodes, One(loc_n->t));
      n := Map_At(nodes, One(loc_n->t));
      // Use well-founded list reachability to prove that recursion will terminate:
      // start@caller --> start@callee --> None()
      assert Between(nodes->val, loc_n, n->next, None());
      call absSet := SetAbsCompute(n->next, nodes, nodes');
      absSet := Set_Add(absSet, n->val);
  }
}

implementation SetAbsLemma<V>(start: Option Loc, nodes: Map (One Loc) (Node V))
{
  var absSet: [V]bool;
  call absSet := SetAbsCompute(start, nodes, nodes);
}

implementation SetFrameLemma<V>(start: Option Loc, nodes: Map (One Loc) (Node V), nodes': Map (One Loc) (Node V))
{
  var absSet: [V]bool;
  call absSet := SetAbsCompute(start, nodes, nodes');
}

/// Queue abstraction
pure procedure QueueAbsCompute<V>(in_queue: Vec V, start: Option Loc, nodes: Map (One Loc) (Node V), nodes': Map (One Loc) (Node V))
  returns (out_queue: Vec V)
requires Set_IsSubset(nodes->dom, nodes'->dom);
requires MapIte(nodes->dom, nodes->val, MapConst(Default())) ==
         MapIte(nodes->dom, nodes'->val, MapConst(Default()));
requires InDomain(nodes, start);
ensures out_queue == QueueAbsDef(in_queue, start, nodes);
ensures out_queue == QueueAbsDef(in_queue, start, nodes');
free ensures out_queue == QueueAbs(in_queue, start, nodes);
free ensures out_queue == QueueAbs(in_queue, start, nodes');
{
  var loc_n: Option Loc;
  var n: Node V;

  if (start == None()) {
      out_queue := in_queue;
  } else {
      loc_n := start;
      assert Map_Contains(nodes, One(loc_n->t));
      n := Map_At(nodes, One(loc_n->t));
      // Use well-founded list reachability to prove that recursion will terminate:
      // start@caller --> start@callee --> None()
      assert Between(nodes->val, loc_n, n->next, None());
      out_queue := Vec_Append(in_queue, n->val);
      call out_queue := QueueAbsCompute(out_queue, n->next, nodes, nodes');
  }
}

implementation QueueAbsLemma<V>(in_queue: Vec V, start: Option Loc, nodes: Map (One Loc) (Node V))
{
  var absQueue: Vec V;
  call absQueue := QueueAbsCompute(in_queue, start, nodes, nodes);
}

implementation QueueFrameLemma<V>(in_queue: Vec V, start: Option Loc, nodes: Map (One Loc) (Node V), nodes': Map (One Loc) (Node V))
{
  var absQueue: Vec V;
  call absQueue := QueueAbsCompute(in_queue, start, nodes, nodes');
}
