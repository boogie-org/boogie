// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function RightOpen (n: int) : [int]bool;
function RightClosed (n: int) : [int]bool;
axiom (forall x: int, y: int :: RightOpen(x)[y] <==> y < x);
axiom (forall x: int, y: int :: RightClosed(x)[y] <==> y <= x);

type {:linear "tid"} X;
const nil: X;
var {:layer 0,1} t: int;       // next ticket to issue
var {:layer 0,2} s: int;       // current ticket permitted to critical section
var {:layer 0,2} cs: X;        // current thread in critical section
var {:layer 0,2} T: [int]bool; // set of issued tickets

// ###########################################################################
// Invariants

function {:inline} Inv1 (tickets: [int]bool, ticket: int): (bool)
{
  tickets == RightOpen(ticket)
}

function {:inline} Inv2 (tickets: [int]bool, ticket: int, lock: X): (bool)
{
  if (lock == nil) then tickets == RightOpen(ticket)
                   else tickets == RightClosed(ticket)
}

// ###########################################################################
// Yield invariants

yield invariant {:layer 2} YieldSpec ({:linear "tid"} tid: X);
invariant tid != nil && cs == tid;

yield invariant {:layer 1} Yield1 ();
invariant Inv1(T, t);

yield invariant {:layer 2} Yield2 ();
invariant Inv2(T, s, cs);

// ###########################################################################
// Main program

yield procedure {:layer 2} main ({:linear_in "tid"} xls':[X]bool)
requires {:layer 2} xls' == MapConst(true);
{
  var {:linear "tid"} tid: X;
  var {:linear "tid"} xls: [X]bool;

  call InitAbstract(xls');
  xls := xls';

  while (*)
  invariant {:yields} true;
  invariant call Yield1();
  invariant call Yield2();
  {
    par xls, tid := Allocate(xls) | Yield1() | Yield2();
    async call Customer(tid);
  }
}

yield procedure {:layer 2} Allocate ({:linear_in "tid"} xls':[X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X)
ensures {:layer 1,2} xl != nil;
{
  call xls, xl := AllocateLow(xls');
}

yield procedure {:layer 2} Customer ({:linear_in "tid"} tid: X)
requires call Yield1();
requires call Yield2();
requires {:layer 2} tid != nil;
{
  while (*)
  invariant {:yields} true;
  invariant call Yield1();
  invariant call Yield2();
  {
    call Enter(tid);
    par Yield1() | Yield2() | YieldSpec(tid);
    call Leave(tid);
  }
}

yield procedure {:layer 2} Enter ({:linear "tid"} tid: X)
preserves call Yield1();
preserves call Yield2();
ensures   call YieldSpec(tid);
requires {:layer 2} tid != nil;
{
  var m: int;

  call m := GetTicketAbstract(tid);
  call WaitAndEnter(tid, m);
}

// ###########################################################################
// Abstractions of primitive atomic actions

// Note how GetTicketAbstract becomes a right mover

action {:layer 2} AtomicInitAbstract ({:linear "tid"} xls:[X]bool)
modifies cs, s, T;
{ assert xls == MapConst(true); cs := nil; s := 0; T := RightOpen(0); }

yield procedure {:layer 1} InitAbstract ({:linear "tid"} xls:[X]bool) refines AtomicInitAbstract
ensures call Yield1();
{
  call Init(xls);
}

-> action {:layer 2} AtomicGetTicketAbstract ({:linear "tid"} tid: X) returns (m: int)
modifies T;
{ assume !T[m]; T[m] := true; }

yield procedure {:layer 1} GetTicketAbstract ({:linear "tid"} tid: X) returns (m: int) refines AtomicGetTicketAbstract
preserves call Yield1();
{
  call m := GetTicket(tid);
}

// ###########################################################################
// Primitive atomic actions

action {:layer 1} AtomicInit ({:linear "tid"} xls:[X]bool)
modifies cs, t, s, T;
{ assert xls == MapConst(true); cs := nil; t := 0; s := 0; T := RightOpen(0); }

yield procedure {:layer 0} Init ({:linear "tid"} xls:[X]bool) refines AtomicInit;

action {:layer 1} AtomicGetTicket ({:linear "tid"} tid: X) returns (m: int)
modifies t, T;
{ m := t; t := t + 1; T[m] := true; }

yield procedure {:layer 0} GetTicket ({:linear "tid"} tid: X) returns (m: int) refines AtomicGetTicket;

action {:layer 1,2} AtomicWaitAndEnter ({:linear "tid"} tid: X, m:int)
modifies cs;
{ assume m == s; cs := tid; }

yield procedure {:layer 0} WaitAndEnter ({:linear "tid"} tid: X, m:int) refines AtomicWaitAndEnter;

action {:layer 1,2} AtomicLeave ({:linear "tid"} tid: X)
modifies cs, s;
{ assert cs == tid; s := s + 1; cs := nil; }

yield procedure {:layer 0} Leave ({:linear "tid"} tid: X) refines AtomicLeave;

action {:layer 1,2} AtomicAllocateLow ({:linear_in "tid"} xls':[X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X)
{ assume xl != nil && xls'[xl]; xls := xls'[xl := false]; }

yield procedure {:layer 0} AllocateLow ({:linear_in "tid"} xls':[X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X) refines AtomicAllocateLow;
