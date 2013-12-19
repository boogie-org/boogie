function RightOpen(n: int) : [int]bool;
function RightClosed(n: int) : [int]bool;

type X;
function {:builtin "MapConst"} mapconstbool(bool): [X]bool;
const nil: X;
var {:qed} t: int;
var {:qed} s: int;
var {:qed} cs: X;
var {:qed} T: [int]bool;

procedure Allocate({:linear "tid"} xls':[X]bool) returns ({:linear "tid"} xls: [X]bool, {:linear "tid"} xl: X);
ensures xl != nil;

function Inv1(tickets: [int]bool, ticket: int): (bool)
{
    tickets == RightOpen(ticket)
}

function Inv2(tickets: [int]bool, ticket: int, lock: X): (bool)
{
    if (lock == nil) then tickets == RightOpen(ticket) else tickets == RightClosed(ticket)
}

procedure {:yields} {:entrypoint} main({:linear "tid"} xls':[X]bool)
requires xls' == mapconstbool(true);
{
    var {:linear "tid"} tid: X;
    var {:linear "tid"} xls: [X]bool;

    call xls := Init(xls');

    while (*)
    invariant {:phase 1} Inv1(T, t);
    invariant {:phase 2} Inv2(T, s, cs);
    {
        call xls, tid := Allocate(xls);
        async call Customer(tid);
    }
}

procedure {:yields} {:stable} Customer({:linear "tid"} tid': X)
requires {:phase 1} Inv1(T, t);
requires {:phase 2} tid' != nil && Inv2(T, s, cs);
{
    var {:linear "tid"} tid: X;
    tid := tid';

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

procedure {:yields} Enter({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X)
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T,t);
requires {:phase 2} tid' != nil && Inv2(T, s, cs);
ensures {:phase 2} tid != nil && Inv2(T, s, cs);
ensures {:right 2} |{ A: tid := tid'; havoc t, T; assume tid != nil && cs == nil; cs := tid; return true; }|;
{
    var m: int;
    tid := tid';

    par Yield1() | Yield2();
    call tid, m := GetTicketAbstract(tid);
    par Yield1();
    call tid := WaitAndEnter(tid, m);
    par Yield1() | Yield2();
}

procedure {:yields} GetTicketAbstract({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, m: int)
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T, t);
ensures {:right 1} |{ A: tid := tid'; havoc m, t; assume !T[m]; T[m] := true; return true; }|;
{
    tid := tid';

    par Yield1();
    call tid, m := GetTicket(tid);
    par Yield1();
}

procedure {:yields} {:stable} Yield()
{
}

procedure {:yields} {:stable} Yield2()
requires {:phase 2} Inv2(T, s, cs);
ensures {:phase 2} Inv2(T, s, cs);
ensures {:both 2} |{ A: return true; }|;
{
}

procedure {:yields} {:stable} Yield1()
requires {:phase 1} Inv1(T, t);
ensures {:phase 1} Inv1(T,t);
ensures {:both 1} |{ A: return true; }|;
{
}

procedure {:yields} Init({:linear "tid"} xls':[X]bool) returns ({:linear "tid"} xls:[X]bool);
ensures {:both 0} |{ A: assert xls' == mapconstbool(true); xls := xls'; cs := nil; t := 0; s := 0; T := RightOpen(0); return true; }|;

procedure {:yields} GetTicket({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X, m: int);
ensures {:atomic 0} |{ A: tid := tid'; m := t; t := t + 1; T[m] := true; return true; }|;

procedure {:yields} WaitAndEnter({:linear "tid"} tid': X, m:int) returns ({:linear "tid"} tid: X);
ensures {:atomic 0} |{ A: tid := tid'; assume m <= s; cs := tid; return true; }|;

procedure {:yields} Leave({:linear "tid"} tid': X) returns ({:linear "tid"} tid: X);
ensures {:atomic 0} |{ A: assert cs == tid'; assert tid' != nil; tid := tid'; s := s + 1; cs := nil; return true; }|;

