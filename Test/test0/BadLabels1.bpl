// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P0()
{
  // these labels don't exist at all
  goto X;  // error: undefined label
  goto Y;  // error: undefined label
}

procedure P1(y: int)
{
  goto X;  
  while (y < 100)
  {
    X:
  }

  Q:
  if (y == 102) {
    A:
    goto Q;
  } else if (y == 104) {
    B:
  } else {
    C:
    goto K;  
  }

  while (y < 1000)
  {
    K:
    goto A;  
    if (y mod 2 == 0) {
      goto L;
      M:
    }
    goto K, L;
    L:
    if (*) {
      goto M;  
    }
  }
  goto B;  
}


procedure Break(n: int)
{
  break;  // error: break not inside a loop
  if (*) {
    break;  // error: label-less break not inside a loop
  }
  
  A:
  if (*) {
    break A;  // this is fine, since the break statement uses a label
  }

  B:
  assert 2 <= n;
  while (*) {
    break B;  // error: B does not label a loop
    break;
    C: while (*) { assert n < 100; }
    break A;     // error: A does not label a loop
    break C;     // error: A does not label an enclosing loop
    F: break F;  // error: F does not label an enclosing loop
  }

  D:
  while (*) {
    E:
    while (*) {
      if (*) {
        break;
      } else if (*) {
        if (*) { break E; }
      } else {
        break D;
      }
    }
  }
}
