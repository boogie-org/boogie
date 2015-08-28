// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %boogie -noVerify -print:- -env:0 "%s" > "%t"
// RUN: %diff "%s.print.expect" "%t"


type Set a = [a]bool;

type Field a, Heap = <a>[ref, Field a]a;

type notAllParams a b = Field b;

type Cyclic0 = Cyclic1;
type Cyclic1 = Cyclic0;

type AlsoCyclic a = <b>[AlsoCyclic b]int;

type C a b;

type C2 b a = C a b;

function f(C int bool) returns (int);
const x : C2 bool int;


const y : Field int bool;       // wrong number of arguments
const z : Set int bool;         // wrong number of arguments


const d : <a,b>[notAllParams a b]int;         // error: not all parameters are used


type ref;
