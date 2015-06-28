// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// ----------- BEGIN PRELUDE

var Heap: [ref, name]int;
const N: name;

procedure Q0()
{
  var h: int;

  entry:
    goto Else;

  Then:
    h := 15;
    goto end;

  Else:
    assume h == 0;
    goto end;

  end:
    assert 0 <= h;
    return;
}

procedure Q1()
{
  var h: int;

  entry:
    goto Else;

  Then:
    h := -15;
    goto end;

  Else:
    assume h == 0;
    goto end;

  end:
    h := -h;
    assert 0 <= h;
    return;
}

procedure P0(this: ref)
  modifies Heap;
{
  entry:
    goto Else;

  Then:
    Heap[this, N] := 15;
    goto end;

  Else:
    assume Heap[this, N] == 0;
    goto end;

  end:
    assert 0 <= Heap[this, N];
    return;
}

procedure P1(this: ref)
  modifies Heap;
{
  entry:
    goto Else;

  Then:
    Heap[this, N] := -15;
    goto end;

  Else:
    assume Heap[this, N] == 0;
    goto end;

  end:
    Heap[this, N] := -Heap[this, N];
    assert 0 <= Heap[this, N];
    return;
}

type name, ref;
