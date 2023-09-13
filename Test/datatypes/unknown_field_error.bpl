// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MemAddr;
type CacheId;

datatype DirState {
  Owner(i: CacheId),
  Sharers(i: CacheId)
}

datatype DirRequest {
  Share(i: CacheId),
  Own(i: CacheId)
}

datatype DirInfo {
  DirInfo(state: DirState, pending: DirRequest)
}

var dir: [MemAddr]DirInfo;

procedure cache_snoop_resp(i: CacheId, ma: MemAddr)
modifies dir;
{
  dir[ma]->t->pending := dir[ma]->t->pending;
}
