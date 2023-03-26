// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type Method;

type Invoc;

// Sequences of invocations
type SeqInvoc;
function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

// Sets of invocations
type SetInvoc;
function Set_ofSeq(q: SeqInvoc) returns (s: SetInvoc);


var {:layer 1,2} lin: SeqInvoc;
var {:layer 1,2} vis: [Invoc]SetInvoc;

type Key;

// ---------- Primitives for manipulating logical/abstract state

link action {:layer 1} intro_readLin() returns (s: SetInvoc)
{
  s := Set_ofSeq(lin);
}

link action {:layer 1} intro_write_vis(n: Invoc, s: SetInvoc)
  modifies vis;
{
  vis[n] := s;
}

link action {:layer 1} intro_writeLin(n: Invoc)
  modifies lin;
{
  lin := Seq_append(lin, n);
}

// ---------- Specification program:

action {:layer 2} pop_atomic(this: Invoc) returns (k: Key)
  modifies lin, vis;
{
  var my_vis: SetInvoc;
  lin := Seq_append(lin, this);
  assume my_vis == Set_ofSeq(lin);
  // buggy transition relation computation due to assume after assignment to lin which
  // creates difference between lin and old(lin)
  vis[this] := my_vis;
}

// ---------- Implementation:

yield procedure {:layer 1} pop(this: Invoc)
  returns (k: Key) refines pop_atomic
{
  var {:layer 1} my_vis: SetInvoc;

  call intro_writeLin(this);
  call my_vis := intro_readLin();
  call intro_write_vis(this, my_vis);
  assert {:layer 1} my_vis == Set_ofSeq(lin);  // Despite this assertion passing
}
