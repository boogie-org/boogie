import Auto
import Auto.Tactic
import Auto.MathlibEmulator.Basic -- For `Real`
open Lean Std Auto

set_option linter.unusedVariables false
set_option auto.smt true
set_option trace.auto.smt.printCommands false
set_option trace.auto.smt.result true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"
set_option trace.auto.buildChecker false

@[simp] def assert (ψ β: Prop): Prop := ψ ∧ β
@[simp] def assume (ψ β: Prop): Prop := ψ → β
@[simp] def skip (β: Prop): Prop := β
@[simp] def ret: Prop := true
@[simp] def goto: Prop → Prop := id

-- SMT Array definition
def SMTArray1 (s1 s2: Type) := s1 → s2

def SMTArray2 (s1 s2 s3 : Type) := s1 → s2 → s3

def store1 [BEq s1] (m: SMTArray1 s1 s2) (i: s1) (v: s2): SMTArray1 s1 s2 :=
  fun i' => if i' == i then v else m i'

def select1 (m: SMTArray1 s1 s2) (i: s1): s2 := m i

def store2 [BEq s1] [BEq s2] (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (v: s3): SMTArray2 s1 s2 s3 :=
  fun i' j' => if i' == i && j' == j then v else m i' j'

def select2 (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2): s3 := m i j

axiom SelectStoreSame1 (s1 s2: Type) [BEq s1] (a: SMTArray1 s1 s2) (i: s1) (e: s2):
  select1 (store1 a i e) i = e

axiom SelectStoreDistinct1 (s1 s2: Type) [BEq s1] (a: SMTArray1 s1 s2) (i: s1) (j: s1) (e: s2):
  i ≠ j → select1 (store1 a i e) j = select1 a j

axiom SelectStoreSame2 (s1 s2 s3: Type) [BEq s1] [BEq s2] (a: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (e: s3):
  select2 (store2 a i j e) i j = e

axiom SelectStoreDistinct2 (s1 s2 s3: Type) [BEq s1] [BEq s2] (a: SMTArray2 s1 s2 s3) (i: s1) (i': s1) (j: s2) (j' : s2) (e: s3):
  i ≠ i' \/ j ≠ j' → select2 (store2 a i j e) i' j' = select2 a i' j'

-- TODO: provide either a definition or some functional axioms (or a definition plus some lemmas)
axiom distinct : {a : Type} → List a → Prop

axiom realToInt : Real → Int
axiom intToReal : Int → Real
instance BEqReal: BEq Real := by sorry
