# Overview

This project provides a printer that renders passive Boogie programs in
Lean syntax. The generated Lean programs include a theorem for every
proof obligation, discharged by `lean-auto` (which uses an automated
theorem prover such as Z3, CVC5, or a first-order prover).

Although it would be possible to write interactive proofs for the
generated goals, the primary purpose of this package is to use Lean as
an enhanced SMT solver, with support for tactics that pre-process goals
and custom decision procedures that, in some cases, may be able to
discharge goals without depending on an external solver. None of those
tactics or decision procedures have been written yet, however.

For the moment, it works manually. The `/printLean:file.lean` option
will print the Lean source text (with `Prelude.lean` prepended) into
`file.lean` after completing normal verification. Ultimately, the code
will call out to Lean as an external process, like Boogie does with SMT
solvers at the moment, but doing that will require building some new
Lean infrastructure.

# Checking the prelude

Two files in this directory, `lean-toolchain` and `lakefile.lean` exist
primarily as development conveniences. With them in place, it's possible
to run `lake build` in this directory and check the code in
`Prelude.lean`.

These files are also used in the test suite for this project, and can be
used as examples of the configuration needed to use the backend in
practice.
