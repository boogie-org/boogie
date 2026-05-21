// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Queue<V> { Queue(head: Loc, tail: Loc, nodes: Map (One (Loc)) (Node V)) }

/*
We want to model queues, a pool of (Queue int) values, and two indices pos and neg
into that pool such that: (1) the domain of pool is linear, and
(2) the indices pos and neg are distinct by virtue of being linear.
We cannot model pos and neg as One Loc because those values
are already earmarked for the domain of queues.
Instead, we model each of pos and neg as a One (Tag Unit) value,
which allows us to achieve both goals.
*/
var {:linear} {:layer 0, 1} queues: Map (One Loc) (Queue int);
var {:linear} {:layer 0, 1} pos: One (Tag Unit);
var {:linear} {:layer 0, 1} neg: One (Tag Unit);

function {:inline} IsAcyclic(q: Queue int): bool
{
    Between(q->nodes->val, Some(q->head), Some(q->tail), None())
}

function {:inline} QueueElems(q: Queue int): [Loc]bool
{
    BetweenSet(q->nodes->val, Some(q->head), Some(q->tail))
}

yield invariant {:layer 1} PosInv();
preserves Map_Contains(queues, One(pos->val->loc));
preserves (var q := Map_At(queues, One(pos->val->loc)); IsAcyclic(q) &&
            (forall loc_n: Loc:: QueueElems(q)[loc_n] ==>
                Map_Contains(q->nodes, One(loc_n)) &&
                (loc_n == q->tail || (var node := Map_At(q->nodes, One(loc_n)); node->val > 0))));

yield invariant {:layer 1} NegInv();
preserves Map_Contains(queues, One(neg->val->loc));
preserves (var q := Map_At(queues, One(neg->val->loc)); IsAcyclic(q) &&
            (forall loc_n: Loc:: QueueElems(q)[loc_n] ==>
                Map_Contains(q->nodes, One(loc_n)) &&
                (loc_n == q->tail || (var node := Map_At(q->nodes, One(loc_n)); node->val < 0))));


yield procedure {:layer 1} {:vcs_split_on_every_assert} Producer(i: int)
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
    var one_loc_q: One Loc;
    var queue: Queue int;
    var head, tail: Loc;
    var nodes: Map (One (Loc)) (Node int);
    var one_loc_n, new_one_loc_n: One (Loc);
    var node: Node int;

    one_loc_q := One(loc_q);
    call queue := Map_Get(queues, one_loc_q);
    Queue(head, tail, nodes) := queue;

    call new_one_loc_n := Loc_New();
    call Map_Put(nodes, new_one_loc_n, Node(None(), 0));

    one_loc_n := One(tail);
    call node := Map_Get(nodes, one_loc_n);
    node := Node(Some(new_one_loc_n->val), i);
    call Map_Put(nodes, one_loc_n, node);

    queue := Queue(head, new_one_loc_n->val, nodes);
    call Map_Put(queues, one_loc_q, queue);
}

yield procedure {:layer 0} Dequeue(loc_q: Loc) returns (i: int);
refines action {:layer 1} _
{
    var one_loc_q: One Loc;
    var queue: Queue int;
    var head, tail: Loc;
    var nodes: Map (One (Loc)) (Node int);
    var one_loc_n: One (Loc);
    var node: Node int;
    var next: Option (Loc);

    one_loc_q := One(loc_q);
    call queue := Map_Get(queues, one_loc_q);
    Queue(head, tail, nodes) := queue;

    assume head != tail;
    one_loc_n := One(head);
    call node := Map_Get(nodes, one_loc_n);
    Node(next, i) := node;

    assert next is Some;
    queue := Queue(next->t, tail, nodes);
    call Map_Put(queues, one_loc_q, queue);
}
