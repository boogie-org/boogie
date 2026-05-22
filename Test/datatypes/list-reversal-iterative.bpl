// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
  Iterative list reversal.

  Two linear lists are maintained: `input` shrinks, `output` grows. Each loop
  iteration pops the head node off `input` and prepends it to `output`, moving
  ownership of the node between the two linear `nodes` maps.
*/

datatype List { List(head: Option Loc, nodes: Map (One Loc) (Node int)) }

function {:inline} WF(l: List): bool {
  l->head is Some ==> InDomain(l->nodes, l->head)
}

pure procedure Reverse({:linear_in} l_in: List) returns ({:linear} l_out: List)
requires WF(l_in);
ensures WF(l_out);
{
  var input: List;
  var input_head: Option Loc;
  var input_nodes: Map (One Loc) (Node int);
  var output_head: Option Loc;
  var output_nodes: Map (One Loc) (Node int);
  var loc_p: One Loc;
  var hd_node: Node int;

  // Start with an empty output list and the full input.
  input := l_in;
  call output_nodes := Map_MakeEmpty();
  l_out := List(None(), output_nodes);

  while (input->head is Some)
  invariant WF(input);
  invariant WF(l_out);
  {
    // Pop the head node off `input`.
    List(input_head, input_nodes) := input;
    loc_p := One(input_head->t);
    call hd_node := Map_Get(input_nodes, loc_p);

    // Prepend it to `output`: its new next pointer is the current output head.
    List(output_head, output_nodes) := l_out;
    call Map_Put(output_nodes, loc_p, Node(output_head, hd_node->val));

    // Advance: input's head becomes the popped node's old next pointer;
    //         output's head becomes the just-prepended node.
    input := List(hd_node->next, input_nodes);
    l_out := List(Some(loc_p->val), output_nodes);
  }
}
