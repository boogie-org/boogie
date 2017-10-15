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

procedure AllocTid() returns (id: int);

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
procedure ServerReceive() returns (m: Msg);
procedure ClientReceive() returns (m: Msg);
procedure MasterReceive() returns (m: Msg);

procedure main(sid: int, n: int)
{
    var i: int;
    var m: Msg;
    var mid: int;
    var cid: int;
    
    call mid := AllocTid();
    async call master(mid, n);
    i := 0;
    while (i < n) {
    	call cid := AllocTid();
        async call client(cid, sid, mid);
	i := i + 1;
    }
    i := 0;
    while (i < n) {
        call m := ServerReceive();
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
    call m := ClientReceive();
    assert is#Task(m);
    call ProcessTask(cid); // CREATED -> PROCESSED
    call Send(mid, Ack(cid));
}

procedure master(mid: int, n: int) {
    var m: Msg;
    var i: int;
    i := 0;
    while (i < n) { 
        call m := MasterReceive();
	assert is#Ack(m);
	call FinishTask(cid#Ack(m)); // PROCESSED -> FINISHED
	i := i + 1;
    }
}
