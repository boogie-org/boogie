// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure Dup(y: int)
{
  X:
  X:  // error: duplicate label
  while (y < 100)
  {
    Y:
  }
  while (y < 1000)
  {
    Y:  // error: duplicate label (labels must be unique in entire procedure body)
  }
}
