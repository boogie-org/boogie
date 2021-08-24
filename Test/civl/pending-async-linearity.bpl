// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;

type {:pending_async}{:datatype} PA;
function {:constructor} A(pid:int) : PA;
function {:constructor} B(pid:int) : PA;

function {:inline} NoPAs () : [PA]int
{ (lambda pa:PA :: 0) }

procedure {:atomic}{:layer 1}
A ({:linear_in "pid"} pid:int)
{}

procedure {:atomic}{:layer 1}
B ({:linear_in "pid"} pid:int)
{}

procedure {:atomic}{:layer 1}
M0 (pid:int)
returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A(/* out of thin air ☠ */ pid) := 1];
}

procedure {:atomic}{:layer 1}
M1 ({:linear_in "pid"} pid:int)
returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A(pid) := 1];
}

procedure {:atomic}{:layer 1}
M2 ({:linear "pid"} pid:int)
returns ({:pending_async "A"} PAs:[PA]int)
{
  PAs := NoPAs()[A(/* duplication ☠ */ pid) := 1];
}

procedure {:atomic}{:layer 1}
M3 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int)
returns ({:pending_async "A","B"} PAs:[PA]int)
{
  PAs := NoPAs()[A(pid1) := 1][B(pid2) := 1];
}

procedure {:atomic}{:layer 1}
M4 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int)
returns ({:pending_async "A","B"} PAs:[PA]int)
{
  PAs := NoPAs()[A(pid1) := 1][B(/* duplication ☠ */ pid1) := 1];
}

procedure {:atomic}{:layer 1}
M5 ({:linear_in "pid"} pid:int)
returns ({:linear "pid"} pid_out:int, {:pending_async "A"} PAs:[PA]int)
{
  pid_out := pid;
  PAs := NoPAs()[A(/* duplication ☠ */ pid) := 1];
}

procedure {:atomic}{:layer 1}
M6 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int, {:linear_in "pid"} pid3:int)
returns ({:linear "pid"} pid_out:int, {:pending_async "A","B"} PAs:[PA]int)
{
  pid_out := pid3;
  PAs := NoPAs()[A(pid1) := 1][B(pid2) := 1];
}

procedure {:atomic}{:layer 1}
M7 ({:linear_in "pid"} pid:[int]bool)
returns ({:pending_async "A"} PAs:[PA]int)
{
  assert pid == (lambda i:int :: 1 <= i && i <= 10);
  PAs := NoPAs()[A(5) := 1];
}

procedure {:atomic}{:layer 1}
M8 ({:linear_in "pid"} pid:[int]bool)
returns ({:pending_async "A"} PAs:[PA]int)
{
  assert pid == (lambda i:int :: 1 <= i && i <= 10);
  PAs := NoPAs()[A(/* out of thin air ☠ */ 0) := 1];
}
