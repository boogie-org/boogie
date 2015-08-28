// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type C;

const c:int extends a;
const d:int extends a complete;
const e:int extends unique a, b;
const f:int extends complete;

const a:int;
const b:int;

const g:int extends x;        // error: undeclared parent

const c0:C;
const c1:C extends c0, c0;    // error: parent mentioned twice
const c2:C extends c2;        // error: constant as its own parent

const h:int extends y;        // error: variable cannot be parent

var y:int;