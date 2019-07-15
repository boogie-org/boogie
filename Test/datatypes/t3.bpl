// RUN: %boogie -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type {:datatype} Value;
function {:constructor} Int(i: int): Value;

type {:datatype} Path;
function {:constructor} Int(i: int): Path;
