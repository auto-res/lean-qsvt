/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Operator.Basic
import QSVT.Encoding.Projected
import QSVT.SVT.PhaseOp
import QSVT.SVT.AltSeq

/-!
# QSVTTest.Encoding

Regression tests for the operator layer: ENC-1 (`ProjUnitaryEncoding`), SVT-2 (`phaseOp`)
and SVT-1 (`altSeq`). Each check is a compile-time assertion.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- GSLW Def 15, `n = 1`. -/
example (E : ProjUnitaryEncoding ℋ) (a : ℝ) : altSeq E [a] = phaseOp E.P' a * E.U :=
  altSeq_one E a

/-- GSLW Def 15, `n = 2`. -/
example (E : ProjUnitaryEncoding ℋ) (a b : ℝ) :
    altSeq E [a, b] = phaseOp E.P a * E.U† * (phaseOp E.P' b * E.U) :=
  altSeq_two E a b

/-- GSLW Def 15, `n = 3`. -/
example (E : ProjUnitaryEncoding ℋ) (a b c : ℝ) :
    altSeq E [a, b, c] = phaseOp E.P' a * E.U * (phaseOp E.P b * E.U† * (phaseOp E.P' c * E.U)) :=
  altSeq_three E a b c

/-- The trivial encoding of a unitary encodes the unitary itself. -/
example (U : L ℋ) (hU : U ∈ unitary (L ℋ)) : (ProjUnitaryEncoding.ofUnitary U hU).encoded = U :=
  ProjUnitaryEncoding.encoded_ofUnitary U hU

/-- `phaseOp P 0 = 1` for any `P`. -/
example (P : L ℋ) : phaseOp P 0 = 1 := phaseOp_zero P

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.SVT.altSeq_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.altSeq_mem_unitary

/-- info: 'QSVT.SVT.phaseOp_mul_phaseOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.phaseOp_mul_phaseOp

/-- info: 'QSVT.SVT.phaseOp_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.phaseOp_mem_unitary

/-- info: 'QuantumState.IsProjective.one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QuantumState.IsProjective.one_sub
