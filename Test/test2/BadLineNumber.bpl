// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure p();
  ensures false;

implementation p()
{
    if (*)
    {
    }
    else
    {
    }
}