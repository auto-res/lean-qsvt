/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.TwoVector

/-!
# QSVTTest.TwoVector

Regression tests for the two-vector lemma of SVT-3 (`QSVT.SVT.TwoVector`): instances of
(R1) and of the headline `Π U_Φ ψ = (seqR Φ ς)₀₀ ψ` for `Φ = [φ]`, and the axiom audit.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- (R1): `U ψ = ς ψ + √(1 - ς²) ψ̃⊥`. -/
example (E : HermitianEncoding ℋ) {ψ : ℋ} {ς : ℝ} (hψ : E.P ψ = ψ)
    (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ^ 2 < 1) :
    E.U ψ = (ς : ℂ) • ψ + (Real.sqrt (1 - ς ^ 2) : ℂ) • ψt E ς ψ :=
  U_ψ E hψ hA hς

/-- (R0): both perpendicular vectors lie in `ker Π`. -/
example (E : HermitianEncoding ℋ) (ψ : ℋ) (ς : ℝ) : E.P (ψt E ς ψ) = 0 ∧ E.P (ψp E ς ψ) = 0 :=
  ⟨P_ψt E, P_ψp E⟩

/-- The headline for a single phase, in `seqR` form. -/
example (E : HermitianEncoding ℋ) {ψ : ℋ} {ς : ℝ} (hψ : E.P ψ = ψ)
    (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ∈ Set.Icc (-1 : ℝ) 1) (φ : ℝ) :
    E.P (altSeq E.toProjUnitaryEncoding [φ] ψ) = (seqR [φ] ς) 0 0 • ψ :=
  proj_altSeq_apply_eigen E hψ hA hς [φ]

/-- The headline for a single phase, evaluated: `Π e^{iφ(2Π̃-I)} U ψ = e^{iφ} ς ψ`. -/
example (E : HermitianEncoding ℋ) {ψ : ℋ} {ς : ℝ} (hψ : E.P ψ = ψ)
    (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ∈ Set.Icc (-1 : ℝ) 1) (φ : ℝ) :
    E.P ((phaseOp E.P' φ * E.U) ψ) = (Complex.exp (Complex.I * φ) * ς) • ψ := by
  have h := proj_altSeq_apply_eigen E hψ hA hς [φ]
  rw [altSeq_one, seqR_cons, seqR_nil, phaseZ_mul_Rref_mul_apply_zero_zero] at h
  simpa using h

/-- The polynomial form of the headline for a single phase: `P_[φ](ς) = e^{iφ} ς`. -/
example (E : HermitianEncoding ℋ) {ψ : ℋ} {ς : ℝ} (hψ : E.P ψ = ψ)
    (hA : E.encoded ψ = (ς : ℂ) • ψ) (hς : ς ∈ Set.Icc (-1 : ℝ) 1) (φ : ℝ) :
    E.P (altSeq E.toProjUnitaryEncoding [φ] ψ) = ((qspPoly [φ]).1.eval (ς : ℂ)) • ψ :=
  proj_altSeq_apply_eigen_eval E hψ hA hς [φ]

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.SVT.proj_altSeq_apply_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.proj_altSeq_apply_eigen

/-- info: 'QSVT.SVT.altSeq_apply_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.altSeq_apply_eigen

/-- info: 'QSVT.SVT.proj_altSeq_apply_eigen_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.proj_altSeq_apply_eigen_eval
