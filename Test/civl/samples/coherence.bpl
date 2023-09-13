// RUN: %parallel-boogie "%s" > "%t"
type MemAddr;
type Value;
datatype State {
  Modified(),
  Exclusive(),
  Shared(),
  Invalid()
}

type CacheAddr;
datatype CacheLine {
  CacheLine(ma: MemAddr, value: Value, state: State, pending: bool)
}
type Cache = [CacheAddr]CacheLine;
type CacheId;
function Hash(MemAddr): CacheAddr;

datatype DirState {
  Owner(i: CacheId),
  Sharers(iset: Set CacheId)
}

datatype DirRequest {
  Share(i: CacheId),
  Own(i: CacheId),
  OwnWithPendingAcks(i: CacheId, iset: Set CacheId),
  NoRequest()
}

datatype DirInfo {
  DirInfo(state: DirState, currRequest: DirRequest)
}

var mem: [MemAddr]Value;
var dir: [MemAddr]DirInfo;
var cache: [CacheId]Cache;

var front: [CacheId][MemAddr]int;
var back: [CacheId][MemAddr]int;

atomic action {:layer 1} GetTicket(i: CacheId, ma: MemAddr) returns (ticket: int)
modifies back;
{
  ticket := back[i][ma];
  back[i][ma] := back[i][ma] + 1;
}


// at cpu
async atomic action {:layer 1} cpu_read_resp(i: CacheId, ma: MemAddr, v: Value) {}

async atomic action {:layer 1} cpu_write_resp(i: CacheId, ma: MemAddr) {}

// at cache
async atomic action {:layer 1} cache_read_req(i: CacheId, ma: MemAddr)
creates cpu_read_resp;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->state != Invalid();
  assert line->ma == ma;
  call create_async(cpu_read_resp(i, ma, line->value));
}

async atomic action {:layer 1} cache_write_req(i: CacheId, ma: MemAddr, v: Value)
modifies cache;
creates cpu_write_resp;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  assert line->state == Exclusive() || line->state == Modified();
  assert line->ma == ma;
  cache[i][ca]->state := Modified();
  cache[i][ca]->value := v;
  call create_async(cpu_write_resp(i, ma));
}

async atomic action {:layer 1} cache_read_shared_req(i: CacheId, ma: MemAddr)
modifies cache;
creates dir_read_shared_req, dir_evict_req;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  if (line->state != Invalid() && line->ma == ma) {
    return;
  }
  assume !cache[i][ca]->pending;
  cache[i][ca]->pending := true;
  if (line->state == Invalid()) {
    call create_async(dir_read_shared_req(i, ma));
  } else if (line->state == Modified()) {
    call create_async(dir_evict_req(i, ma, Some(line->value)));
  } else {
    call create_async(dir_evict_req(i, ma, None()));
  }
}

async atomic action {:layer 1} cache_read_own_req(i: CacheId, ma: MemAddr)
modifies cache;
creates dir_read_own_req, dir_evict_req;
{
  var ca: CacheAddr;
  var line: CacheLine;
  ca := Hash(ma);
  line := cache[i][ca];
  if (line->state != Invalid() && line->state != Shared() && line->ma == ma) {
    return;
  }
  assume !cache[i][ca]->pending;
  cache[i][ca]->pending := true;
  if (line->state == Invalid() || line->ma == ma) {
    call create_async(dir_read_own_req(i, ma));
  } else if (line->state == Modified()) {
    call create_async(dir_evict_req(i, ma, Some(line->value)));
  } else {
    call create_async(dir_evict_req(i, ma, None()));
  }
}

async atomic action {:layer 1} cache_read_resp(i: CacheId, ma: MemAddr, v: Value, s: State, ticket: int)
modifies cache, front;
{
  assume ticket == front[i][ma];
  front[i][ma] := front[i][ma] + 1;
  assert s == Shared() || s == Exclusive();
  assert cache[i][Hash(ma)]->pending;
  cache[i][Hash(ma)] := CacheLine(ma, v, s, false);
}

async atomic action {:layer 1} cache_evict_resp(i: CacheId, ma: MemAddr, ticket: int)
modifies cache, front;
{
  assume ticket == front[i][ma];
  front[i][ma] := front[i][ma] + 1;
  assert cache[i][Hash(ma)]->pending;
  cache[i][Hash(ma)]->state := Invalid();
  cache[i][Hash(ma)]->pending := false;
}

async atomic action {:layer 1} cache_snoop_req(i: CacheId, ma: MemAddr, s: State, ticket: int)
modifies cache;
creates dir_snoop_resp;
{
  var ca: CacheAddr;
  var line: CacheLine;
  assume ticket <= front[i][ma];
  ca := Hash(ma);
  line := cache[i][ca];
  assert s == Invalid() || s == Shared();
  assert line->state != Invalid();
  assert line->ma == ma;
  if (line->state == Modified()) {
    call create_async(dir_snoop_resp(i, ma, Some(line->value)));
  } else {
    call create_async(dir_snoop_resp(i, ma, None()));
  }
  cache[i][ca]->state := s;
}

// at dir
async atomic action {:layer 1} dir_read_shared_req(i: CacheId, ma: MemAddr)
modifies dir, back;
creates cache_snoop_req, cache_read_resp;
{
  var ticket: int;
  assume dir[ma]->currRequest == NoRequest();
  if (dir[ma]->state is Owner) {
    dir[ma]->currRequest := Share(i);
    ticket := back[dir[ma]->state->i][ma];
    call create_async(cache_snoop_req(dir[ma]->state->i, ma, Shared(), ticket));
  } else if (dir[ma]->state == Sharers(Set_Empty())) {
    dir[ma]->state := Owner(i);
    call ticket := GetTicket(i, ma);
    call create_async(cache_read_resp(i, ma, mem[ma], Exclusive(), ticket));
  } else {
    dir[ma]->state := Sharers(Set_Add(dir[ma]->state->iset, i));
    call ticket := GetTicket(i, ma);
    call create_async(cache_read_resp(i, ma, mem[ma], Shared(), ticket));
  }
}

async atomic action {:layer 1} dir_read_own_req(i: CacheId, ma: MemAddr)
modifies dir, back;
creates cache_snoop_req;
{
  assume dir[ma]->currRequest == NoRequest();
  if (dir[ma]->state is Owner) {
    dir[ma]->currRequest := Own(i);
    call create_async(cache_snoop_req(dir[ma]->state->i, ma, Invalid(), back[dir[ma]->state->i][ma]));
  } else {
    dir[ma]->currRequest := OwnWithPendingAcks(i, dir[ma]->state->iset);
    call create_asyncs(
      (lambda x: cache_snoop_req ::
        Set_Contains(dir[ma]->state->iset, x->i) &&
        x->ma == ma && x->s == Invalid() &&
        x->ticket == back[x->i][ma]));
  }
}

async atomic action {:layer 1} dir_evict_req(i: CacheId, ma: MemAddr, opt_value: Option Value)
modifies mem, dir, back;
creates cache_evict_resp;
{
  var ticket: int;
  assume dir[ma]->currRequest == NoRequest();
  if (opt_value is Some) {
    assert dir[ma]->state is Owner;
    mem[ma] := opt_value->t;
  }
  if (dir[ma]->state is Owner) {
    dir[ma]->state := Sharers(Set_Empty());
  } else {
    assert opt_value is None;
    dir[ma]->state->iset := Set_Remove(dir[ma]->state->iset, i);
  }
  call ticket := GetTicket(i, ma);
  call create_async(cache_evict_resp(i, ma, ticket));
}

async atomic action {:layer 1} dir_snoop_resp(i: CacheId, ma: MemAddr, opt_value: Option Value)
modifies mem, dir, back;
creates cache_read_resp;
{
  var ticket: int;
  assert !(dir[ma]->currRequest is NoRequest);
  if (opt_value is Some) {
    assert dir[ma]->state is Owner;
    mem[ma] := opt_value->t;
  }
  if (dir[ma]->state is Owner) {
    assert !(dir[ma]->currRequest is OwnWithPendingAcks);
    call ticket := GetTicket(dir[ma]->currRequest->i, ma);
    if (dir[ma]->currRequest is Own) {
      call create_async(cache_read_resp(dir[ma]->currRequest->i, ma, mem[ma], Exclusive(), ticket));
      dir[ma]->state := Owner(dir[ma]->currRequest->i);
    } else {
      call create_async(cache_read_resp(dir[ma]->currRequest->i, ma, mem[ma], Shared(), ticket));
      dir[ma]->state := Sharers(Set_Add(Set_Singleton(dir[ma]->state->i), dir[ma]->currRequest->i));
    }
    dir[ma]->currRequest := NoRequest();
  } else {
    assert dir[ma]->currRequest is OwnWithPendingAcks;
    dir[ma]->currRequest->iset := Set_Remove(dir[ma]->currRequest->iset, i);
    if (dir[ma]->currRequest->iset == Set_Empty()) {
      call ticket := GetTicket(dir[ma]->currRequest->i, ma);
      call create_async(cache_read_resp(dir[ma]->currRequest->i, ma, mem[ma], Exclusive(), ticket));
      dir[ma]->state := Owner(dir[ma]->currRequest->i);
      dir[ma]->currRequest := NoRequest();
    }
  }
}
