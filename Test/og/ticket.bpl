// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory %s > %t
// RUN: %diff %s.expect %t
function RightOpen(n: int) : [int]bool;
function RightClosed(n: int) : [int]bool;
axiom (forall x: int, y: int :: RightOpen(x)[y] <==> y < x);
axiom (forall x: int, y: int :: RightClosed(x)[y] <==> y <= x);

type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var {:phase 3} t: int;
var {:phase 3} s: int;
var {:phase 3} cs: X;
var {:phase 3} T: [int]bool;

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

procedure Allocate({:linear "tid"} xls':[X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X);
ensures {:phase 1} {:phase 2} xl != nil;

procedure {:yields} {:phase 3} main({:linear "tid"} xls':[X]bool)
requires {:phase 3} xls' == mapconstbool(true);
{
    var {:linear "tid"} tid: X;
    var {:linear "tid"} xls: [X]bool;

    yield;

    call xls := Init(xls');

    par Yield1() | Yield2() | Yield();

    while (*)
    invariant {:phase 1} Inv1(T, t);
    invariant {:phase 2} Inv2(T, s, cs);
    {
	par Yield1() | Yield2() | Yield();
        call xls, tid := Allocate(xls);
        async call Customer(tid);
    	par Yield1() | Yield2() | Yield();

    }
}

procedure {:yields} {:phase 3} Customer({:linear "tid"} tid': X)
requires {:phase 1} Inv1(T, t);
requires {:phase 2} tid' != nil && Inv2(T, s, cs);
requires {:phase 3} true;
{
    var {:linear "tid"} tid: X;
    tid := tid';
    
    par Yield1() | Yield2() | Yield();    
    while (*) 
    invariant {:phase 1} Inv1(T, t);
    invariant {:phase 2} tid != nil && Inv2(T, s, cs);
    {
        par Yield1() | Yield2() | Yield();
        call tid := Enter(tid);
        par Yield1() | Yield2();
    	call tid := Leave(tid);
        par Yield1() | Yield2() | Yield();
    }
}

procedure {:yields} {:phase 2,3} Enter({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T,t);
requires {:phase 2} tid' != nil && Inv2(T, s, cs);
ensures {:phase 2} tid != nil && Inv2(T, s, cs);
ensures {:right} |{ A: tid := tid'; havoc t, T; assume tid != nil && cs == nil; cs := tid; return true; }|;
{
    var m: int;

    par Yield1() | Yield2();
    tid := tid';
    call tid, m := GetTicketAbstract(tid);
    par Yield1();
    call tid := WaitAndEnter(tid, m);
    par Yield1() | Yield2();
}

procedure {:yields} {:phase 1,2} GetTicketAbstract({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, m: int)
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T, t);
ensures {:right} |{ A: tid := tid'; havoc m, t; assume !T[m]; T[m] := true; return true; }|;
{
    par Yield1();
    tid := tid';
    call tid, m := GetTicket(tid);
    par Yield1();
}

procedure {:yields} {:phase 3} Yield()
{
    yield;
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

procedure {:yields} {:phase 0,3} Init({:linear "tid"} xls':[X]bool) returns ({:linear "tid"} xls:[X]bool);
ensures {:atomic} |{ A: assert xls' == mapconstbool(true); xls := xls'; cs := nil; t := 0; s := 0; T := RightOpen(0); return true; }|;

procedure {:yields} {:phase 0,1} GetTicket({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, m: int);
ensures {:atomic} |{ A: tid := tid'; m := t; t := t + 1; T[m] := true; return true; }|;

procedure {:yields} {:phase 0,2} WaitAndEnter({:linear "tid"} tid': X, m:int) returns ({:linear "tid"} tid: X);
ensures {:atomic} |{ A: tid := tid'; assume m <= s; cs := tid; return true; }|;

procedure {:yields} {:phase 0,3} Leave({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X);
ensures {:atomic} |{ A: assert cs == tid'; assert tid' != nil; tid := tid'; s := s + 1; cs := nil; return true; }|;

