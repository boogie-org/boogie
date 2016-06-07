// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


const {:Incorrect pux0 ++ F0(pux1)} pux0: int;

function {:Incorrect F0(pux0 < 0) + pux1} F0(int) returns (int);

axiom {:Incorrect F0(pux0 == pux1)} true;

var {:Incorrect pux0 && pux1} pux1: int;

procedure {:Incorrect !(pux0 - pux1)} P();

implementation {:Incorrect pux0 ==> pux1} P()
{
}

// ------  and here are various correct things



const {:Correct hux0 + F1(hux1)} hux0: int;

function {:Correct F1(hux0) + hux1} F1(int) returns (int);

axiom {:Correct F1(hux0 + hux1)} true;

var {:Correct hux0*hux1} hux1: int;

procedure {:Correct hux0 - hux1} H();

implementation {:Correct hux0 + hux1} {:AlsoCorrect "hello"} H()
{
}


type any;