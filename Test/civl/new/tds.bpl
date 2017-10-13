procedure main(sid: int, n: int)
{
    var i: int;
    var m: Msg;
    
    i := 0;
    while (i < n) {
        async client(cid);
	i := i + 1;
    }
    async master(mid);
    call server(sid, n);
    i := 0;
    while (i < n) {
        m := ServerReceive();
	assert m is Request;
	CreateTask(m.cid);
	send m.cid, Task();
	i := i + 1;
    }
}

procedure client(cid: int, mid: int, sid: int)
{
    var m: Msg;
    send sid, Request(cid);
    call m := ClientReceive();
    assert m is Task;
    ProcessTask(cid);
    send mid, Ack();
}

procedure master(sid: int, n: int) {
    var m: Msg;
    var i: int;
    i := 0;
    while (i < n) { 
        call m := MasterReceive();
	assert m is Ack(cid);
	FinishTask(m.cid);
    }
}