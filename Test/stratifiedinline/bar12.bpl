// RUN: %boogie -stratifiedInline:1 -vc:i "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function {:inline} f(a:bool) : bool { true }

procedure {:entrypoint} main()
{
  var x: int;
   assume f(x >= 0);
  assume x >= 0;
}
