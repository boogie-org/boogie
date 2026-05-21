// RUN: %parallel-boogie -lib:base -lib:node -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Michael & Scott non-blocking concurrent queue (Figure 1 of
// "Simple, Fast, and Practical Non-Blocking and Blocking
//  Concurrent Queue Algorithms" by Michael and Scott, PODC 1996).
//
// The queue is represented as a singly-linked list with a sentinel
// (dummy) node. Head always points to the dummy node; its value is
// meaningless. Tail points to the last node, but is allowed to lag
// behind by at most one node (the "helping" protocol).

type X; // queue element type

datatype MSQueue { MSQueue(head: Loc, tail: Loc, nodes: Map (One Loc) (Node X), tags: UnitMap (One (Tag Unit))) }

var {:layer 0, 1} {:linear} queue: MSQueue;

yield invariant {:layer 1} QueueInv();
preserves Map_Contains(queue->nodes, One(queue->head));
preserves Map_Contains(queue->nodes, One(queue->tail));
preserves Between(queue->nodes->val, Some(queue->head), Some(queue->tail), None());
preserves (forall loc: Loc :: Map_Contains(queue->nodes, One(loc)) ==> InDomain(queue->nodes, Some(loc)));
preserves (forall loc: Loc :: Between(queue->nodes->val, Some(queue->tail), Some(loc), None()) ==> Map_Contains(queue->tags, One (Tag(loc, Unit()))));

yield invariant {:layer 1} TagInv({:linear} tag_opt: Option (One (Tag Unit)));
preserves tag_opt is None || (var loc := tag_opt->t->val->loc; Map_Contains(queue->nodes, One(loc)) && Map_At(queue->nodes, One(loc))->next == None());
preserves tag_opt is None || 
          (var loc := tag_opt->t->val->loc; 
            (forall loc': Loc:: Map_Contains(queue->nodes, One(loc')) && Between(queue->nodes->val, Some(loc'), Some(loc), None()) ==> loc' == loc));

yield invariant {:layer 1} ReachesTail(a: Loc);
preserves Map_Contains(queue->nodes, One(a));
preserves Between(queue->nodes->val, Some(a), Some(queue->tail), None());

yield invariant {:layer 1} Reaches(a: Loc, b: Loc);
preserves Map_Contains(queue->nodes, One(a));
preserves Between(queue->nodes->val, Some(a), Some(b), None());

yield invariant {:layer 1} NextStable(a: Loc, next: Option Loc);
preserves next == None() || (Map_Contains(queue->nodes, One(a)) && queue->nodes->val[One(a)]->next == next);

yield procedure {:layer 1} Enqueue(v: X)
preserves call QueueInv();
{
  var one_loc_n: One Loc;
  var tag: One (Tag Unit);
  var tag_opt: Option (One (Tag Unit));

  call one_loc_n, tag := Tag_New();
  tag_opt := Some(tag);
  call AllocNode(one_loc_n, Node(None(), v));
  while (tag_opt is Some)
  invariant {:yields} true;
  invariant call QueueInv();
  invariant call TagInv(tag_opt);
  {
    call tag_opt := EnqueueHelper(tag_opt);
  }
}

yield procedure {:layer 1} {:vcs_split_on_every_assert} EnqueueHelper({:linear_in} tag_opt: Option (One (Tag Unit)))
returns ({:linear} tag_opt': Option (One (Tag Unit)))
requires {:layer 1} tag_opt is Some;
requires call TagInv(tag_opt);
ensures call TagInv(tag_opt');
preserves call QueueInv();
{
  var t, t': Loc;
  var next: Option Loc;
  var success, dummy: bool;
  var loc: Loc;
  var tag: One (Tag Unit);

  tag_opt' := tag_opt;
  call t := ReadTail();
  call QueueInv() | TagInv(tag_opt') | ReachesTail(t);
  call next := ReadNext(t);
  call QueueInv() | TagInv(tag_opt') | ReachesTail(t) | NextStable(t, next);
  call t' := ReadTail();
  call QueueInv() | TagInv(tag_opt') | ReachesTail(t) | NextStable(t, next);
  if (t != t') { return; }
  if (next is None) {
    loc := tag_opt'->t->val->loc;
    call success := CASTailNext(t, loc);
    if (success) {
      Some(tag) := tag_opt';
      call AddTag(tag);
      tag_opt' := None();
      call QueueInv() | Reaches(t, loc);
      call dummy := CASTail(t, loc);
    }
  } else {
    call dummy := CASTail(t, next->t);
  }
}

yield procedure {:layer 1} {:vcs_split_on_every_assert} Dequeue() returns (value: Option X)
preserves call QueueInv();
{
  var h, h': Loc;
  var t: Loc;
  var next: Option Loc;
  var dummy, success: bool;
  var x: X;

  while (true)
  invariant {:yields} true;
  invariant call QueueInv();
  {
    call h := ReadHead();
    call QueueInv() | ReachesTail(h);
    call t := ReadTail();
    call QueueInv() | Reaches(h, t) | ReachesTail(t);
    call next := ReadNext(h);
    call QueueInv() | Reaches(h, t) | ReachesTail(t) | NextStable(h, next);
    call h' := ReadHead();
    call QueueInv() | Reaches(h, t) | ReachesTail(t) | NextStable(h, next);
    if (h == h') {
      if (h == t) {
        if (next is None) {
          value := None();
          return;
        }
        call dummy := CASTail(t, next->t);
      } else {
        call x := ReadValue(next->t);
        call QueueInv() | Reaches(h, t) | ReachesTail(t) | NextStable(h, next);
        call success := CASHead(h, next->t);
        if (success) {
          value := Some(x);
          return;
        }
      }
    }
  }
}

/// ////////////////////////////////////////////////////////////////
/// Layer-0 primitives. Each refines an atomic action at layer 1.
/// ////////////////////////////////////////////////////////////////

yield procedure {:layer 0} ReadHead() returns (h: Loc);
refines atomic action {:layer 1} _
{
  h := queue->head;
}

yield procedure {:layer 0} ReadTail() returns (t: Loc);
refines atomic action {:layer 1} _
{
  t := queue->tail;
}

yield procedure {:layer 0} ReadNext(loc_n: Loc) returns (next: Option Loc);
refines atomic action {:layer 1} _
{
  var node: Node X;

  call node := Path_Load(queue->nodes->val[One(loc_n)]);
  next := node->next;
}

yield procedure {:layer 0} ReadValue(loc_n: Loc) returns (value: X);
refines atomic action {:layer 1} _
{
  var node: Node X;

  call node := Path_Load(queue->nodes->val[One(loc_n)]);
  value := node->val;
}

yield procedure {:layer 0} CASHead(expected: Loc, new_head: Loc) returns (success: bool);
refines atomic action {:layer 1} _
{
  var h: Loc;

  h := queue->head;
  if (h == expected) {
    queue->head := new_head;
    success := true;
  } else {
    success := false;
  }
}

yield procedure {:layer 0} CASTail(expected: Loc, new_tail: Loc) returns (success: bool);
refines atomic action {:layer 1} _
{
  var t: Loc;

  t := queue->tail;
  if (t == expected) {
    queue->tail := new_tail;
    success := true;
  } else {
    success := false;
  }
}

yield procedure {:layer 0} CASTailNext(t: Loc, loc: Loc) returns (success: bool);
refines atomic action {:layer 1} _
{
  var one_loc: One Loc;
  var old_next: Option Loc;

  success := false;
  one_loc := One(t);
  call old_next := Path_Load(queue->nodes->val[one_loc]->next);
  if (old_next == None()) {
    call Path_Store(queue->nodes->val[one_loc]->next, Some(loc));
    success := true;
  }
}

yield procedure {:layer 0} AddTag({:linear_in} tag: One (Tag Unit));
refines left action {:layer 1} _
{
  call One_Put(queue->tags, tag);
}

yield procedure {:layer 0} AllocNode({:linear_in} one_loc_n: One Loc, node: Node X);
refines atomic action {:layer 1} _
{
  call Map_Put(queue->nodes, one_loc_n, node);
}
