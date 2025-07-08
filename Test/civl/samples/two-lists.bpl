// RUN: %parallel-boogie -lib:base -lib:node -vcsSplitOnEveryAssert "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Queue<T> { Queue(head: Loc, tail: Loc, {:linear} nodes: Map Loc (Node Loc T)) }

var {:linear} {:layer 0, 1} queues: Map Loc (Queue int);
var {:linear} {:layer 0, 1} pos: One (TaggedLoc Unit);
var {:linear} {:layer 0, 1} neg: One (TaggedLoc Unit);

function {:inline} IsAcyclic(q: Queue int): bool
{
    Between(q->nodes->val, Some(q->head), Some(q->tail), None())
}

function {:inline} QueueElems(q: Queue int): [Loc]bool 
{
    BetweenSet(q->nodes->val, Some(q->head), Some(q->tail))
}

yield invariant {:layer 1} PosInv();
invariant Map_Contains(queues, pos->val->loc);
invariant (var q := Map_At(queues, pos->val->loc); IsAcyclic(q) &&
            (forall loc_n: Loc:: QueueElems(q)[loc_n] ==>
                Map_Contains(q->nodes, loc_n) &&
                (loc_n == q->tail || (var node := Map_At(q->nodes, loc_n); node->val > 0))));

yield invariant {:layer 1} NegInv();
invariant Map_Contains(queues, neg->val->loc);
invariant (var q := Map_At(queues, neg->val->loc); IsAcyclic(q) &&
            (forall loc_n: Loc:: QueueElems(q)[loc_n] ==>
                Map_Contains(q->nodes, loc_n) &&
                (loc_n == q->tail || (var node := Map_At(q->nodes, loc_n); node->val < 0))));


yield procedure {:layer 1} Producer(i: int)
preserves call PosInv();
preserves call NegInv();
{
    var loc: Loc;

    assert {:layer 1} pos->val->loc != neg->val->loc;
    if (i == 0) {
        return;
    }
    if (i > 0) {
        call loc := ReadPos();
    } else {
        call loc := ReadNeg();
    }
    call Enqueue(loc, i);
}

yield procedure {:layer 1} PosConsumer()
preserves call PosInv();
{
    var loc: Loc;
    var i: int;

    call loc := ReadPos();
    call i := Dequeue(loc);
    assert {:layer 1} i > 0;
}

yield procedure {:layer 1} NegConsumer()
preserves call NegInv();
{
    var loc: Loc;
    var i: int;

    call loc := ReadNeg();
    call i := Dequeue(loc);
    assert {:layer 1} i < 0;
}

// Primitives

yield procedure {:layer 0} ReadPos() returns (loc: Loc);
refines both action {:layer 1} _ {
    loc := pos->val->loc;
}

yield procedure {:layer 0} ReadNeg() returns (loc: Loc);
refines both action {:layer 1} _ {
    loc := neg->val->loc;
}

yield procedure {:layer 0} Enqueue(loc_q: Loc, i: int);
refines action {:layer 1} _
{
    var {:linear} one_loc_q: One Loc;
    var {:linear} queue: Queue int;
    var head, tail: Loc;
    var {:linear} nodes: Map Loc (Node Loc int);
    var {:linear} one_loc_n, new_one_loc_n: One Loc;
    var node: Node Loc int;

    call one_loc_q, queue := Map_Get(queues, loc_q);
    Queue(head, tail, nodes) := queue;

    call new_one_loc_n := Loc_New();
    call Map_Put(nodes, new_one_loc_n, Node(None(), 0));

    call one_loc_n, node := Map_Get(nodes, tail);
    node := Node(Some(new_one_loc_n->val), i);
    call Map_Put(nodes, one_loc_n, node);

    queue := Queue(head, new_one_loc_n->val, nodes);
    call Map_Put(queues, one_loc_q, queue);
}

yield procedure {:layer 0} Dequeue(loc_q: Loc) returns (i: int);
refines action {:layer 1} _
{
    var {:linear} one_loc_q: One Loc;
    var {:linear} queue: Queue int;
    var head, tail: Loc;
    var {:linear} nodes: Map Loc (Node Loc int);
    var {:linear} one_loc_n: One Loc;
    var node: Node Loc int;
    var next: Option Loc;

    call one_loc_q, queue := Map_Get(queues, loc_q);
    Queue(head, tail, nodes) := queue;

    assume head != tail;
    call one_loc_n, node := Map_Get(nodes, head);
    Node(next, i) := node;

    assert next is Some;
    queue := Queue(next->t, tail, nodes);
    call Map_Put(queues, one_loc_q, queue);
}
