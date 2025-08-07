// RUN: %parallel-boogie -timeLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const N: int; // size of the ring
axiom N > 0;
function {:inline} Next(i: int) : int { (i + 1) mod N }
function {:inline} ValidPid(pid: int) : bool { 0 <= pid && pid < N }

var {:layer 0,1} leader: [int]bool;       // leader[pid] iff pid is a leader

// priority for becoming leader (ties are broken by pid)
function Priority(int): int;      // pid -> priority
function {:inline} Below(self: int, pid: int): bool
{
  Priority(self) < Priority(pid) || 
  (Priority(self) == Priority(pid) && self < pid)
}

const ExpectedLeader: int;
axiom ValidPid(ExpectedLeader);
axiom (forall i: int:: ValidPid(i) ==> i == ExpectedLeader || Below(i, ExpectedLeader));

// alternative coordinates for identifying processes where ExpectedLeader is at position 0
// Pid converts from position to process id
function {:inline} Pid(pos: int) : int { (ExpectedLeader + pos) mod N }

////////////////////////////////////////////////////////////////////////////////

yield left procedure {:layer 1} main()
requires {:layer 1} leader == MapConst(false);
ensures {:layer 1} leader == MapOne(ExpectedLeader);
modifies leader;
{
  var pos: int;
  var pid: int;

  pos := N - 1;
  while (0 <= pos)
  invariant {:layer 1} pos < N;
  invariant {:layer 1} if 0 <= pos then leader == MapConst(false) else leader == MapOne(ExpectedLeader);
  {
    pid := Pid(pos);
    async call {:sync} p(Next(pid), pid);
    pos := pos - 1;
  }
}

yield left procedure {:layer 1} p(self: int, pid: int)
requires {:layer 1} ValidPid(self) && ValidPid(pid);
requires {:layer 1} leader == MapConst(false);
requires {:layer 1} pid == ExpectedLeader || (ExpectedLeader - self) mod N < (ExpectedLeader - pid) mod N;
ensures {:layer 1} if pid == ExpectedLeader then leader == MapOne(ExpectedLeader) else leader == MapConst(false);
modifies leader;
{
  if (self == pid)
  {
    call set_leader(pid);
  }
  else if (Below(self, pid))
  {
    async call {:sync} p(Next(self), pid);
  }
}

////////////////////////////////////////////////////////////////////////////////

yield procedure {:layer 0} set_leader(pid: int);
refines both action {:layer 1} _ {
  leader[pid] := true;
}
