// RUN: %parallel-boogie -lib:base -lib:node "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
  Recursive list reversal (two-list style).

  Same shape as the iterative version: maintain `input` (shrinking) and
  `output` (growing). Each step pops the head node off `input` and prepends
  it to `output`, moving ownership of the node between the two linear `nodes`
  maps. The loop is replaced by a tail-recursive helper.
*/

datatype List { List(head: Option Loc, nodes: Map (One Loc) (Node int)) }

function {:inline} WF(l: List): bool {
  l->head is Some ==> InDomain(l->nodes, l->head)
}

/// ReverseHelper: tail-recursive step. Move one node from `input` to `output`,
/// then recurse. When `input` is empty, return `output`.
pure procedure ReverseHelper({:linear_in} input: List, {:linear_in} output: List)
    returns ({:linear} l_out: List)
requires WF(input);
requires WF(output);
ensures WF(l_out);
{
  var input_head: Option Loc;
  var input_nodes: Map (One Loc) (Node int);
  var output_head: Option Loc;
  var output_nodes: Map (One Loc) (Node int);
  var loc_p: One Loc;
  var hd_node: Node int;
  var new_input: List;
  var new_output: List;

  if (input->head is None) {
    l_out := output;
  } else {
    // Pop the head node off `input`.
    List(input_head, input_nodes) := input;
    loc_p := One(input_head->t);
    call hd_node := Map_Get(input_nodes, loc_p);

    // Prepend it to `output`: its new next pointer is the current output head.
    List(output_head, output_nodes) := output;
    call Map_Put(output_nodes, loc_p, Node(output_head, hd_node->val));

    // Advance: input's head becomes the popped node's old next pointer;
    //         output's head becomes the just-prepended node.
    new_input := List(hd_node->next, input_nodes);
    new_output := List(Some(loc_p->val), output_nodes);

    call l_out := ReverseHelper(new_input, new_output);
  }
}

pure procedure Reverse({:linear_in} l_in: List) returns ({:linear} l_out: List)
requires WF(l_in);
ensures WF(l_out);
{
  var empty_output: List;
  var empty_nodes: Map (One Loc) (Node int);

  call empty_nodes := Map_MakeEmpty();
  empty_output := List(None(), empty_nodes);

  call l_out := ReverseHelper(l_in, empty_output);
}
