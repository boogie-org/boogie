// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P()
{
  assert |{ A: return true; }|;
}

// ------------

procedure Q()
{
  assert |{ var x: bool; A: x := true; return x; }|;
}

procedure R()
{
  assert |{ var x: bool; A: x := false; return x; }|;  // error
}

procedure S()
{
  assert |{ var x: bool; A: return x; }|;  // error
}

// ------------

procedure T(x: int, y: int)
  requires |{ var z: bool;
              Start: goto A;
              A: z := false; goto B, C;
              B: assume 0 <= x; goto D;
              C: assume x < 0; goto R;
              D: goto E, F;
              E: assume 0 <= y; z := true; goto R;
              F: assume y < 0; goto R;
              R: return z;
           }|;
{
  assert 0 <= x + y;
}

procedure U(x: int, y: int)
  requires |{ var z: bool;
              Start: goto A;
              A: z := false; goto B, C;
              B: assume 0 <= x; goto D;
              C: assume x < 0; goto R;
              D: goto E, F;
              E: assume 0 <= y; z := true; goto R;
              F: assume y < 0; goto R;
              R: return z;
           }|;
{
  assert x <= y;  // error
}
