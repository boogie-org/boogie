// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:linear "pid"} Pid = int;

async atomic action {:layer 1} A ({:linear_in "pid"} pid:int)
{}

async atomic action {:layer 1} B ({:linear_in "pid"} pid:int)
{}

atomic action {:layer 1} M0 (pid:int)
creates A;
{
  call create_async(A(/* out of thin air */ pid));
}

atomic action {:layer 1} M1 ({:linear_in "pid"} pid:int)
creates A;
{
  call create_async(A(pid));
}

atomic action {:layer 1} M2 ({:linear "pid"} pid:int)
creates A;
{
  call create_async(A(/* duplication */ pid));
}

atomic action {:layer 1} M3 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int)
creates A, B;
{
  call create_async(A(pid1));
  call create_async(B(pid2));
}

atomic action {:layer 1} M4 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int)
creates A, B;
{
  call create_async(A(pid1));
  call create_async(B(/* duplication */ pid1));
}

atomic action {:layer 1} M5 ({:linear_in "pid"} pid:int) returns ({:linear "pid"} pid_out:int)
creates A;
{
  pid_out := pid;
  call create_async(A(/* duplication */ pid));
}

atomic action {:layer 1} M6 ({:linear_in "pid"} pid1:int, {:linear_in "pid"} pid2:int, {:linear_in "pid"} pid3:int)
returns ({:linear "pid"} pid_out:int)
creates A, B;
{
  pid_out := pid3;
  call create_async(A(pid1));
  call create_async(B(pid2));
}

atomic action {:layer 1} M7 ({:linear_in "pid"} pid:[int]bool)
creates A;
{
  assert pid == (lambda i:int :: 1 <= i && i <= 10);
  call create_async(A(5));
}

atomic action {:layer 1} M8 ({:linear_in "pid"} pid:[int]bool)
creates A;
{
  assert pid == (lambda i:int :: 1 <= i && i <= 10);
  call create_async(A(/* out of thin air */ 0));
}
