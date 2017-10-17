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


procedure {:left}  {:layer 4} atomic_server({:linear "tid"} id: int, sid: int, n: int)
modifies status;
{
    assert (forall i: int :: 0 <= i && i < n ==> status[i] == DEFAULT);
    status := (lambda j: int :: if (0 <= j && j < n) then CREATED else status[j]);
}

