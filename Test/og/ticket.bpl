// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function RightOpen(n: int) : [int]bool;
function RightClosed(n: int) : [int]bool;
axiom (forall x: int, y: int :: RightOpen(x)[y] <==> y < x);
axiom (forall x: int, y: int :: RightClosed(x)[y] <==> y <= x);

type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var {:phase 2} t: int;
var {:phase 2} s: int;
var {:phase 2} cs: X;
var {:phase 2} T: [int]bool;

function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:inline} {:linear "tid"} TidCollector(x: X) : [X]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [X]bool) : [X]bool
{
  x
}

function {:inline} Inv1(tickets: [int]bool, ticket: int): (bool)
{
    tickets == RightOpen(ticket)
}

function {:inline} Inv2(tickets: [int]bool, ticket: int, lock: X): (bool)
{
    if (lock == nil) then tickets == RightOpen(ticket) else tickets == RightClosed(ticket)
}

procedure Allocate({:linear_in "tid"} xls':[X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X);
ensures {:phase 1} {:phase 2} xl != nil;

procedure {:yields} {:phase 2} main({:linear_in "tid"} xls':[X]bool)
requires {:phase 2} xls' == mapconstbool(true);
{
    var {:linear "tid"} tid: X;
    var {:linear "tid"} xls: [X]bool;

    yield;

    call Init(xls');
    xls := xls';

    par Yield1() | Yield2();

    while (*)
    invariant {:phase 1} Inv1(T, t);
    invariant {:phase 2} Inv2(T, s, cs);
    {
        call xls, tid := Allocate(xls);
        async call Customer(tid);
    	par Yield1() | Yield2();
    }
    par Yield1() | Yield2();
}

procedure {:yields} {:phase 2} Customer({:linear_in "tid"} tid: X)
requires {:phase 1} Inv1(T, t);
requires {:phase 2} tid != nil && Inv2(T, s, cs);
{
    par Yield1() | Yield2();    
    while (*) 
    invariant {:phase 1} Inv1(T, t);
    invariant {:phase 2} Inv2(T, s, cs);
    {
        call Enter(tid);
        par Yield1() | Yield2() | YieldSpec(tid);
    	call Leave(tid);
        par Yield1() | Yield2();
    }
    par Yield1() | Yield2();
}

procedure {:yields} {:phase 2} Enter({:linear "tid"} tid: X)
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T,t);
requires {:phase 2} tid != nil && Inv2(T, s, cs);
ensures {:phase 2} Inv2(T, s, cs) && cs == tid;
{
    var m: int;

    par Yield1() | Yield2();
    call m := GetTicketAbstract(tid);
    par Yield1();
    call WaitAndEnter(tid, m);
    par Yield1() | Yield2() | YieldSpec(tid);
}

procedure {:yields} {:phase 1,2} GetTicketAbstract({:linear "tid"} tid: X) returns (m: int)
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T, t);
ensures {:right} |{ A: havoc m, t; assume !T[m]; T[m] := true; return true; }|;
{
    par Yield1();
    call m := GetTicket(tid);
    par Yield1();
}

procedure {:yields} {:phase 2} YieldSpec({:linear "tid"} tid: X)
requires {:phase 2} tid != nil && cs == tid;
ensures {:phase 2} cs == tid;
{
    yield;
    assert {:phase 2} tid != nil && cs == tid;
}

procedure {:yields} {:phase 2} Yield2()
requires {:phase 2} Inv2(T, s, cs);
ensures {:phase 2} Inv2(T, s, cs);
{
    yield;
    assert {:phase 2} Inv2(T, s, cs);
}

procedure {:yields} {:phase 1} Yield1()
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T,t);
{
    yield;
    assert {:phase 1} Inv1(T,t);
}

procedure {:yields} {:phase 0,2} Init({:linear "tid"} xls:[X]bool);
ensures {:atomic} |{ A: assert xls == mapconstbool(true); cs := nil; t := 0; s := 0; T := RightOpen(0); return true; }|;

procedure {:yields} {:phase 0,1} GetTicket({:linear "tid"} tid: X) returns (m: int);
ensures {:atomic} |{ A: m := t; t := t + 1; T[m] := true; return true; }|;

procedure {:yields} {:phase 0,2} WaitAndEnter({:linear "tid"} tid: X, m:int);
ensures {:atomic} |{ A: assume m <= s; cs := tid; return true; }|;

procedure {:yields} {:phase 0,2} Leave({:linear "tid"} tid: X);
ensures {:atomic} |{ A: s := s + 1; cs := nil; return true; }|;

