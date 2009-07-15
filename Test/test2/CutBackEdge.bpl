procedure Test()
{
  var i: int;

  entry:
    i := 0;
    goto block850;

  block850:
    assert i == 0;
    havoc i;
    goto block850;

}
