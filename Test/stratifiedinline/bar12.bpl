function {:inline} f(a:bool) : bool { true }

procedure {:entrypoint} main()
{
  var x: int;
   assume f(x >= 0);
  assume x >= 0;
}
