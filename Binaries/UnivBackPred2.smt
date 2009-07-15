; -------------------------------------------------------------------------
; Boogie universal background predicate
; Copyright (c) 2004-2006, Microsoft Corp.
  :logic AUFLIA
  :category { industrial }

:extrasorts ( boogieU )
:extrasorts ( boogieT )
:extrasorts ( TermBool )

:extrafuns (( boolTrue TermBool ))
:extrafuns (( boolFalse TermBool ))
:extrafuns (( boolIff TermBool TermBool TermBool ))
:extrafuns (( boolImplies TermBool TermBool TermBool ))
:extrafuns (( boolAnd TermBool TermBool TermBool ))
:extrafuns (( boolOr TermBool TermBool TermBool ))
:extrafuns (( boolNot TermBool TermBool ))
:extrafuns (( UEqual boogieU boogieU TermBool ))
:extrafuns (( TEqual boogieT boogieT TermBool ))
:extrafuns (( IntEqual Int Int TermBool ))
:extrafuns (( intLess Int Int TermBool ))
:extrafuns (( intAtMost Int Int TermBool ))
:extrafuns (( intGreater Int Int TermBool ))
:extrafuns (( intAtLeast Int Int TermBool ))
:extrafuns (( boogieIntMod Int Int Int ))
:extrafuns (( boogieIntDiv Int Int Int ))

; used for translation with type premisses
:extrapreds (( UOrdering2 boogieU boogieU ))
; used for translation with type arguments
:extrapreds (( UOrdering3 boogieT boogieU boogieU ))

; used for translation with type premisses
:extrafuns (( TermUOrdering2 boogieU boogieU TermBool ))
; used for translation with type arguments
:extrafuns (( TermUOrdering3 boogieT boogieU boogieU TermBool ))

  ; formula/term axioms
  :assumption
  (forall (?x TermBool) (?y TermBool)
    (iff
      (= (boolIff ?x ?y) boolTrue)
      (iff (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x TermBool) (?y TermBool)
    (iff
      (= (boolImplies ?x ?y) boolTrue)
      (implies (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x TermBool) (?y TermBool)
    (iff
      (= (boolAnd ?x ?y) boolTrue)
      (and (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x TermBool) (?y TermBool)
    (iff
      (= (boolOr ?x ?y) boolTrue)
      (or (= ?x boolTrue) (= ?y boolTrue))))

  :assumption
  (forall (?x TermBool)
    (iff
      (= (boolNot ?x) boolTrue)
      (not (= ?x boolTrue)))
    :pat { (boolNot ?x) }
  )

  :assumption
  (forall (?x boogieU) (?y boogieU)
    (iff
      (= (UEqual ?x ?y) boolTrue)
      (= ?x ?y)))

  :assumption
  (forall (?x boogieT) (?y boogieT)
    (iff
      (= (TEqual ?x ?y) boolTrue)
      (= ?x ?y)))

  :assumption
  (forall (?x Int) (?y Int)
    (iff
      (= (IntEqual ?x ?y) boolTrue)
      (= ?x ?y)))

  :assumption
  (forall (?x Int) (?y Int)
    (iff
      (= (intLess ?x ?y) boolTrue)
      (< ?x ?y)))

  :assumption
  (forall (?x Int) (?y Int)
    (iff
      (= (intAtMost ?x ?y) boolTrue)
      (<= ?x ?y)))

  :assumption
  (forall (?x Int) (?y Int)
    (iff
      (= (intAtLeast ?x ?y) boolTrue)
      (>= ?x ?y)))

  :assumption
  (forall (?x Int) (?y Int)
    (iff
      (= (intGreater ?x ?y) boolTrue)
      (> ?x ?y)))

  ; false is not true
  :assumption
  (distinct boolFalse boolTrue)

  :assumption
  (forall (?x boogieU) (?y boogieU)
    (iff
      (= (TermUOrdering2 ?x ?y) boolTrue)
      (UOrdering2 ?x ?y)))

  :assumption
  (forall (?x boogieT) (?y boogieU) (?z boogieU)
    (iff
      (= (TermUOrdering3 ?x ?y ?z) boolTrue)
      (UOrdering3 ?x ?y ?z)))

; End Boogie universal background predicate
; -------------------------------------------------------------------------

