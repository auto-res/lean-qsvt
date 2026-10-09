/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.QSP.Conversion
import QSVT.QSP.Perturb

/-!
# QSVTTest.Conversion

Sanity checks for QSP-2 (conversion between the rotation and reflection conventions) and QSP-6
(phase perturbation bound) in degree `d = 1`, plus axiom audits of the main theorems.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QSVT.QSP
open scoped Real Matrix.Norms.L2Operator

/-! ### QSP-2, `d = 1` -/

/-- `d = 1`: `seqW φ₀ [φ₁] x = i • seqR [φ₀ - π/4] x * e^{i(φ₁ - π/4)σ_z}`. -/
example (φ₀ φ₁ x : ℝ) :
    seqW φ₀ [φ₁] x = Complex.I • (seqR [φ₀ - π / 4] x * phaseZ (φ₁ - π / 4)) := by
  rw [seqW_eq_seqR φ₀ x (List.cons_ne_nil φ₁ [])]
  simp [shift]

/-- `d = 1`, GSLW Cor 8: the top-left entry of `seqW φ₀ [φ₁] x` is that of `seqR [φ₀ + φ₁] x`. -/
example (φ₀ φ₁ x : ℝ) : (seqW φ₀ [φ₁] x) 0 0 = (seqR [φ₀ + φ₁] x) 0 0 := by
  rw [seqW_apply_zero_zero_eq φ₀ x (List.cons_ne_nil φ₁ [])]
  simp [cor8Phases]

/-- The Cor 8 phase list has the same length as the rotation phase list. -/
example (φ₀ : ℝ) : (cor8Phases φ₀ [1, 2, 3] (by simp)).length = 3 := by simp

/-- The shifted phase list for `d = 2`. -/
example (φ₀ φ₁ φ₂ : ℝ) : shift φ₀ [φ₁, φ₂] = [φ₀ - π / 4, φ₁ - π / 2] := by
  simp [shift]

/-! ### QSP-6, `d = 1` -/

/-- One phase: `‖seqR [φ] x - seqR [ψ] x‖ ≤ 2 |φ - ψ|`. -/
example (φ ψ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖seqR [φ] x - seqR [ψ] x‖ ≤ 2 * |φ - ψ| := by
  simpa using norm_seqR_sub_seqR hx [φ] [ψ] rfl

/-- Two phases: `‖seqR [φ₁, φ₂] x - seqR [ψ₁, ψ₂] x‖ ≤ 2 (|φ₁ - ψ₁| + |φ₂ - ψ₂|)`. -/
example (φ₁ φ₂ ψ₁ ψ₂ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖seqR [φ₁, φ₂] x - seqR [ψ₁, ψ₂] x‖ ≤ 2 * (|φ₁ - ψ₁| + |φ₂ - ψ₂|) := by
  simpa using norm_seqR_sub_seqR hx [φ₁, φ₂] [ψ₁, ψ₂] rfl

/-- Entrywise, sharp constant: `|P_[φ](x) - P_[ψ](x)| ≤ |φ - ψ|`. -/
example (φ ψ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(seqR [φ] x) 0 0 - (seqR [ψ] x) 0 0‖ ≤ |φ - ψ| := by
  simpa using norm_seqR_sub_seqR_apply_le hx [φ] [ψ] rfl 0 0

/-! ### Axiom audit -/

/-- info: 'QSVT.QSP.Wrot_eq_Rref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.Wrot_eq_Rref

/-- info: 'QSVT.QSP.seqW_eq_seqR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqW_eq_seqR

/-- info: 'QSVT.QSP.seqW_apply_zero_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqW_apply_zero_zero_eq

/-- info: 'QSVT.QSP.norm_seqR_sub_seqR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.norm_seqR_sub_seqR

/-- info: 'QSVT.QSP.norm_seqR_sub_seqR_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.norm_seqR_sub_seqR_apply
