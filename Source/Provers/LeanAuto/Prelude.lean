import Auto
import Auto.Tactic
import Auto.MathlibEmulator.Basic -- For `Real`
import Auto.Translation.SMTAttributes
open Lean Std Auto Auto.SMT.Attribute

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

def store1
  [BEq s1]
  (m: SMTArray1 s1 s2) (i: s1) (v: s2): SMTArray1 s1 s2 :=
    fun i' => if i' == i then v else m i'

def select1 (m: SMTArray1 s1 s2) (i: s1): s2 := m i

def store2
  [BEq s1] [BEq s2]
  (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (v: s3): SMTArray2 s1 s2 s3 :=
    fun i' j' => if i' == i && j' == j then v else m i' j'

def select2 (m: SMTArray2 s1 s2 s3) (i: s1) (j: s2): s3 := m i j

theorem SelectStoreSame1
  (s1 s2: Type)
  [BEq s1] [LawfulBEq s1]
  (a: SMTArray1 s1 s2) (i: s1) (e: s2):
  select1 (store1 a i e) i = e :=
    by simp [select1, store1]

theorem SelectStoreDistinct1
  (s1 s2: Type)
  [BEq s1] [LawfulBEq s1]
  (a: SMTArray1 s1 s2) (i: s1) (j: s1) (e: s2):
  i ≠ j → select1 (store1 a i e) j = select1 a j :=
    by simp [select1, store1]
       intro neq eq1
       have eq2: i = j := Eq.symm eq1
       contradiction

theorem SelectStoreSame2
  (s1 s2 s3: Type)
  [BEq s1] [BEq s2]
  [LawfulBEq s1] [LawfulBEq s2]
  (a: SMTArray2 s1 s2 s3) (i: s1) (j: s2) (e: s3):
  select2 (store2 a i j e) i j = e :=
    by simp [select2, store2]

theorem SelectStoreDistinct2
  (s1 s2 s3: Type)
  [BEq s1] [BEq s2]
  [LawfulBEq s1] [LawfulBEq s2]
  (a: SMTArray2 s1 s2 s3) (i: s1) (i': s1) (j: s2) (j' : s2) (e: s3):
  i ≠ i' \/ j ≠ j' → select2 (store2 a i j e) i' j' = select2 a i' j' :=
    by simp [select2, store2]
       intro either eq1 eq2
       cases either
       have eq3: i = i' := Eq.symm eq1
       contradiction
       have eq4: j = j' := Eq.symm eq2
       contradiction

-- TODO: make this translate to the appropriate thing in SMT or prove some
-- theorems and include them as SMT axioms.
def distinct {a : Type} [BEq a] (xs: List a) : Prop :=
  match xs with
  | [] => true
  | x :: rest => x ∉ rest ∧ distinct rest

axiom realToInt : Real → Int
axiom intToReal : Int → Real
instance BEqReal: BEq Real := by sorry
