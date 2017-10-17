function {:builtin "MapConst"} MapConstBool(bool): [int]bool;
function {:inline} {:linear "tid"} TidCollector(x: int) : [int]bool
{
  MapConstBool(false)[x := true]
}

type{:datatype} Pid;
function{:constructor} Client(id:int):Pid;
function{:constructor} Server(id:int):Pid;
function{:constructor} Master(id:int):Pid;

type{:datatype} Msg;
function{:constructor} Request(cid:int):Msg;
function{:constructor} None():Msg;
function{:constructor} Task():Msg;
function{:constructor} Ack(cid:int):Msg;

const unique DEFAULT: int;
const unique CREATED: int;
const unique PROCESSED: int;
const unique FINISHED: int;

var status:[int]int;

procedure {:atomic}  {:layer 5} atomic_main({:linear "tid"} id: int, n: int)
modifies status;
{
    var newStatus:[int]int;
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    assume (forall i: int :: 0 <= i && i < n ==> newStatus[i] == FINISHED);
    assume (forall i: int :: (0 <= i && i < n) || newStatus[i] == status[i]);    
    status := newStatus;
//    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

procedure {:left}  {:layer 4} atomic_server({:linear "tid"} id: int, sid: int, n: int)
modifies status;
{
    var newStatus:[int]int;
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    assume (forall i: int :: 0 <= i && i < n ==> newStatus[i] == CREATED);
    assume (forall i: int :: (0 <= i && i < n) || newStatus[i] == status[i]);
    status := newStatus;
//    status := (lambda j: int :: if (0 <= j && j < n) then CREATED else status[j]);
}

procedure {:left}  {:layer 4} atomic_client({:linear "tid"} id: int, sid: int, mid: int, n: int)
modifies status;
{
    var newStatus:[int]int;
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == CREATED);
    assume (forall i: int :: 0 <= i && i < n ==> newStatus[i] == PROCESSED);
    assume (forall i: int :: (0 <= i && i < n) || newStatus[i] == status[i]);
    status := newStatus;
//    status := (lambda j: int :: if (0 <= j && j < n) then PROCESSED else status[j]);
}

procedure {:left}  {:layer 4} atomic_master({:linear "tid"} id: int, mid: int, n: int)
modifies status;
{
    var newStatus:[int]int;
    assert id == c;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == PROCESSED);
    assume (forall i: int :: 0 <= i && i < n ==> newStatus[i] == FINISHED);
    assume (forall i: int :: (0 <= i && i < n) || newStatus[i] == status[i]);
    status := newStatus;
//    status := (lambda j: int :: if (0 <= j && j < n) then FINISHED else status[j]);
}

const c: int;

procedure {:yields} {:layer 4} {:refines "atomic_main"} main({:linear "tid"} id: int, n: int)
{
    var i: int;
    var m: Msg;
    var sid: int;
    var mid: int;
    var cid: int;

    yield;
    call server3(id, 0, n);
    call client3(id, 0, 0, n);
    call master3(id, 0, n);
    yield;
}

procedure {:yields} {:layer 3} {:refines "atomic_server"} server3({:linear "tid"} id: int, sid: int, n: int)
{
    var i: int;
    yield;
    i := 0;
    while (i < n)
    invariant {:terminates} {:layer 2,3} true;
    {
        async call server2(sid, i);
        i := i + 1;
    }
    yield;
}

procedure {:left} {:layer 3} atomic_server2(sid: int, i: int)
modifies status;
{
    assert status[i] == DEFAULT;
    status[i] := CREATED;
}
procedure {:yields} {:layer 2} {:refines "atomic_server2"} server2(sid: int, i: int);

procedure {:yields} {:layer 3} {:refines "atomic_client"} client3({:linear "tid"} id: int, sid: int, mid: int, n: int)
{
    yield;
    call client2(sid, mid, n);
    yield;
}

procedure {:atomic} {:layer 3} atomic_client2(sid: int, mid: int, n: int)
modifies status;
{
    var newStatus:[int]int;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == CREATED);
    assume (forall i: int :: 0 <= i && i < n ==> newStatus[i] == PROCESSED);
    assume (forall i: int :: (0 <= i && i < n) || newStatus[i] == status[i]);
    status := newStatus;
}
procedure {:yields} {:layer 2} {:refines "atomic_client2"} client2(sid: int, mid: int, n: int);

procedure {:yields} {:layer 3} {:refines "atomic_master"} master3({:linear "tid"} id: int, mid: int, n: int)
{
    yield;
    call master2(mid, n);
    yield;
}

procedure {:atomic} {:layer 3} atomic_master2(mid: int, n: int)
modifies status;
{
    var newStatus:[int]int;
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == PROCESSED);
    assume (forall i: int :: 0 <= i && i < n ==> newStatus[i] == FINISHED);
    assume (forall i: int :: (0 <= i && i < n) || newStatus[i] == status[i]);
    status := newStatus;
}
procedure {:yields} {:layer 2} {:refines "atomic_master2"} master2(mid: int, n: int);

/*
procedure {:inline} CreateTask(cid: int)
{
    assert status[cid] == DEFAULT;
    status[cid] := CREATED;
}

procedure {:inline} ProcessTask(cid: int)
{
    assert status[cid] == CREATED;
    status[cid] := PROCESSED;
}

procedure {:inline} FinishTask(cid: int)
{
    assert status[cid] == PROCESSED;
    status[cid] := FINISHED;
}

procedure Send(id: int, m: Msg);
procedure ServerReceive(sid: int) returns (m: Msg);
procedure ClientReceive(cid: int) returns (m: Msg);
procedure MasterReceive(mid: int) returns (m: Msg);

procedure server(sid: int, n: int)
{
    var i: int;
    var m: Msg;
    i := 0;
    while (i < n) {
        call m := ServerReceive(sid);
	assert is#Request(m);
	call CreateTask(cid#Request(m)); // DEFAULT -> CREATED	
	call Send(cid#Request(m), Task());
	i := i + 1;
    }
}

procedure client(cid: int, sid: int, mid: int)
{
    var m: Msg;
    call Send(sid, Request(cid));
    call m := ClientReceive(cid);
    assert is#Task(m);
    call ProcessTask(cid); // CREATED -> PROCESSED
    call Send(mid, Ack(cid));
}

procedure master(mid: int, n: int) {
    var m: Msg;
    var i: int;
    i := 0;
    while (i < n) { 
        call m := MasterReceive(mid);
	assert is#Ack(m);
	call FinishTask(cid#Ack(m)); // PROCESSED -> FINISHED
	i := i + 1;
    }
}
*/