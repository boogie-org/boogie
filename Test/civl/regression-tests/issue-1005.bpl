// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

left action {:layer 1, 100} voting_action ()
{
}

yield procedure {:layer 0} voting_procedure ();
refines voting_action;


yield left procedure {:layer 100} voting_loop_yield_procedure()
{
    async call voting_procedure();
}
