// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;

procedure {:atomic}{:layer 1} {:pending_async}
A ({:linear_in "pid"} pid:int)
{}

procedure {:atomic}{:layer 1} {:pending_async}
B ({:linear_in "pid"} pid:int)
{}

procedure {:atomic}{:layer 1} {:creates "A"}
M0 (pid:int)
{
  call create_async(A(/* out of thin air */ pid));
}

procedure {:atomic}{:layer 1} {:creates "A"}
M1 ({:linear_in "pid"} pid:int)
{
  call create_async(A(pid));
}

procedure {:atomic}{:layer 1} {:creates "A"}
M2 ({:linear "pid"} pid:int)
{
  call create_async(A(/* duplication */ pid));
}

procedure {:atomic}{:layer 1} {:creates "A", "B"}
M3 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int)
{
  call create_async(A(pid1));
  call create_async(B(pid2));
}

procedure {:atomic}{:layer 1} {:creates "A", "B"}
M4 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int)
{
  call create_async(A(pid1));
  call create_async(B(/* duplication */ pid1));
}

procedure {:atomic}{:layer 1} {:creates "A"}
M5 ({:linear_in "pid"} pid:int)
returns ({:linear "pid"} pid_out:int)
{
  pid_out := pid;
  call create_async(A(/* duplication */ pid));
}

procedure {:atomic}{:layer 1} {:creates "A", "B"}
M6 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int, {:linear_in "pid"} pid3:int)
returns ({:linear "pid"} pid_out:int)
{
  pid_out := pid3;
  call create_async(A(pid1));
  call create_async(B(pid2));
}

procedure {:atomic}{:layer 1} {:creates "A"}
M7 ({:linear_in "pid"} pid:[int]bool)
{
  assert pid == (lambda i:int :: 1 <= i && i <= 10);
  call create_async(A(5));
}

procedure {:atomic}{:layer 1} {:creates "A"}
M8 ({:linear_in "pid"} pid:[int]bool)
{
  assert pid == (lambda i:int :: 1 <= i && i <= 10);
  call create_async(A(/* out of thin air */ 0));
}
