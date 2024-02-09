// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

async atomic action {:layer 1} A ({:linear_in} pid: One int)
{}

async atomic action {:layer 1} B ({:linear_in} pid: One int)
{}

atomic action {:layer 1} M0 (pid:int)
creates A;
{
  call create_async(A(/* out of thin air */ One(pid)));
}

atomic action {:layer 1} M1 ({:linear_in} pid: One int)
creates A;
{
  call create_async(A(pid));
}

atomic action {:layer 1} M2 ({:linear} pid: One int)
creates A;
{
  call create_async(A(/* duplication */ pid));
}

atomic action {:layer 1} M3 ({:linear_in} pid1: One int, {:linear_in} pid2: One int)
creates A, B;
{
  call create_async(A(pid1));
  call create_async(B(pid2));
}

atomic action {:layer 1} M4 ({:linear_in} pid1: One int, {:linear_in} pid2: One int)
creates A, B;
{
  call create_async(A(pid1));
  call create_async(B(/* duplication */ pid1));
}

atomic action {:layer 1} M5 ({:linear_in} pid: One int) returns ({:linear} pid_out: One int)
creates A;
{
  pid_out := pid;
  call create_async(A(/* duplication */ pid));
}

atomic action {:layer 1} M6 ({:linear_in} pid1: One int, {:linear_in} pid2: One int, {:linear_in} pid3: One int)
returns ({:linear} pid_out: One int)
creates A, B;
{
  pid_out := pid3;
  call create_async(A(pid1));
  call create_async(B(pid2));
}

atomic action {:layer 1} M7 ({:linear_in} pids: Set int)
creates A;
{
  assert pids->val == (lambda i:int :: 1 <= i && i <= 10);
  call create_async(A(One(5)));
}

atomic action {:layer 1} M8 ({:linear_in} pids: Set int)
creates A;
{
  assert pids->val == (lambda i:int :: 1 <= i && i <= 10);
  call create_async(A(/* out of thin air */ One(0)));
}
