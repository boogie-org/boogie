// RUN: %boogie /proverOpt:BATCH_MODE=true /rlimit:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure P(x: real) {
    assert x > 0.0 ==> (x*2.0 + x) / x > x;
}
