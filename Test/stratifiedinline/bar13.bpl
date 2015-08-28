// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var alloc: int;
var assertsPassed: bool;
procedure boogie_si_record_li2bpl_int(x: int);

procedure __HAVOC_malloc(size: int) returns (ret: int);
  free requires size >= 0;
  modifies alloc;
  free ensures ret == old(alloc);
  free ensures alloc >= old(alloc) + size;


procedure foo(arg: int) 
  modifies alloc;
{
  var tt: int;

  anon0__unique__1:
    // assume NumberOfBytes_2 >= 0;
    call boogie_si_record_li2bpl_int(arg);
    call tt := __HAVOC_malloc(arg);
    call boogie_si_record_li2bpl_int(alloc);
    return;
}

procedure {:entrypoint} main()
  modifies alloc;
{
  var t1: int;

  assume alloc > 0;
  call foo(t1);
  assume alloc < 0;
}

