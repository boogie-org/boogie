// RUN: %boogie -noinfer -typeEncoding:m -useArrayTheory -doModSetAnalysis "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure A() {}

procedure B({:linear_in ""} tid:int) returns({:linear ""} tid':int)
{
  tid' := tid;
  call A();
}

