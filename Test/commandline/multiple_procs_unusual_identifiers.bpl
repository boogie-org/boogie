// RUN: %boogie "-proc:*Bar*" "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 10 verified, 0 errors

procedure foo()
{
    assert false;
}

procedure bar()
{
    assert false;
}

/* Start should be matched */

procedure _Bar()
{
    assert true;
}

procedure .Bar()
{
    assert true;
}

procedure ..Bar..()
{
    assert true;
}

procedure $Bar()
{
    assert true;
}

procedure #Bar()
{
    assert true;
}

procedure 'Bar''()
{
    assert true;
}

procedure ``Bar``()
{
    assert true;
}

procedure ~Bar()
{
    assert true;
}

procedure Bar^^()
{
    assert true;
}

/* This is Boogie2 claims backslash is a valid identifier
   but the parser rejects this.
procedure Bar\\()
{
    assert true;
}
*/

procedure ??Bar()
{
    assert true;
}

/* End should be matched */
