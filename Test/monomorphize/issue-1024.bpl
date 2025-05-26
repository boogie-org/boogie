// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Ref;

type Field T;

const allocated: Field bool; 

const owner: Field Ref;

type Frame = <alpha>[Ref, Field alpha]bool;

function { :inline } closed_under_domains(frame: Frame): bool
{ 
  (exists <V> o: Ref, f: Field V :: frame[o, f])
}
	          
const writable: Frame;

procedure GCD.divides(d: int, n: int) returns (Result: bool);
free requires closed_under_domains(writable);

implementation GCD.divides(d: int, n: int) returns (Result: bool)
{
}
