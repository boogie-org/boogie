// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var g: int;

procedure Foo() returns ();
    modifies g;
    free ensures 0 <= g;

implementation Foo() returns ()
{
    entry:
        g := g + 1;
        return;
}

procedure BarGood() returns ()
    modifies g;
{
    entry:
        call Foo();
        assert 0 <= g;
        return;
}

procedure BarBad() returns ()
    modifies g;
{
    entry:
        call Foo();
        assert 0 < g;
        return;
}

// ----- Free preconditions

procedure Proc() returns ();
    free requires g == 15;

implementation Proc() returns ()
{
    entry:
        assert g > 10;  // yes, this condition can be used here
        return;
}

implementation Proc() returns ()
{
    entry:
        assert g < 10;  // error
        return;
}

procedure Caller0() returns ()
{
    entry:
        call Proc();  // yes, legal, since the precondition is not checked
        return;
}

procedure Caller1() returns ()
{
    entry:
        call Proc();
        assert g > 10;  // error, because:
        // Free preconditions are ignored (that is, treated as "skip") for the caller.
        // This is a BoogiePL design choice.  Another alternative would be to treat free
        // preconditions as assume commands also on the caller side, either in the order
        // that all preconditions are given, or before or after all the checked preconditions
        // have been checked.
        return;
}
