// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
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

type Ref;
type Key;

// ---------- Primitives for manipulating logical/abstract state

procedure {:layer 1} intro_readLin() returns (s: SetInvoc)
  ensures {:layer 1} s == Set_ofSeq(lin);
{
  s := Set_ofSeq(lin);
}

procedure {:layer 1} intro_write_vis(n: Invoc, s: SetInvoc)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

procedure {:layer 1} intro_writeLin(n: Invoc)
  ensures {:layer 1} lin == Seq_append(old(lin), n);
  modifies lin;
{
  lin := Seq_append(lin, n);
}

// ---------- Specification program:

procedure {:atomic} {:layer 2} pop_atomic(this: Invoc) returns (k: Key)
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

procedure {:yields} {:layer 1} {:refines "pop_atomic"} pop(this: Invoc)
  returns (k: Key)
{
  var {:layer 1} my_vis: SetInvoc;

  yield;

  call intro_writeLin(this);
  call my_vis := intro_readLin();
  call intro_write_vis(this, my_vis);
  assert {:layer 1} my_vis == Set_ofSeq(lin);  // Despite this assertion passing

  yield;
}
