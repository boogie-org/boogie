// RUN: %boogie /vcsCores:1 "/proverOpt:PROVER_PATH=doesNotExit" "%s" > "%t" || True
// RUN: %diff "%s.expect" "%t"

procedure first()
{
    assume true;
}

procedure second()
{
    assume true;
}