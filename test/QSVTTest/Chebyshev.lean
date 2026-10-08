/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.QSP.Chebyshev
import QSVT.QSP.Endpoints

/-!
# QSVTTest.Chebyshev

Sanity checks for QSP-4 (Chebyshev phases `chebPhases`) and QSP-5 (endpoint formulas at
`x = ±1, 0`), plus axiom audits of the main theorems.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QSVT.QSP Polynomial

/-! ### QSP-4: small degrees -/

/-- `d = 0`: the empty phase list gives the identity, `T_0 = 1`. -/
example {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : (seqR (chebPhases 0) x) 0 0 = 1 := by
  rw [seqR_chebPhases hx]
  simp

/-- `d = 1`: `chebPhases 1 = [0]`, so `seqR [0] x = R(x)` and the top-left entry is `T_1(x) = x`. -/
example {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : (seqR (chebPhases 1) x) 0 0 = x := by
  rw [seqR_chebPhases hx]
  simp

/-- `d = 2`: the top-left entry is `T_2(x) = 2x² - 1`. -/
example {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (seqR (chebPhases 2) x) 0 0 = 2 * (x : ℂ) ^ 2 - 1 := by
  rw [seqR_chebPhases hx]
  simp [Chebyshev.T_two]

/-- `d = 3`: the top-left entry is `T_3(x) = 4x³ - 3x`. -/
example {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (seqR (chebPhases 3) x) 0 0 = 4 * (x : ℂ) ^ 3 - 3 * (x : ℂ) := by
  rw [seqR_chebPhases hx]
  simp [Chebyshev.T_eq ℂ 3, Chebyshev.T_two]
  ring

/-- The phase list has the right shape. -/
example : chebPhases 3 = [(1 - 3) * Real.pi / 2, Real.pi / 2, Real.pi / 2] := by
  rw [chebPhases_eq (by norm_num)]
  norm_num [List.replicate]

#guard (List.range 5).map (fun d => (List.replicate (d - 1) ()).length + min d 1) = [0, 1, 2, 3, 4]

/-! ### QSP-5: endpoints -/

/-- `x = 1`, one phase: `P(1) = e^{iφ}`. -/
example (φ : ℝ) : (seqR [φ] 1) 0 0 = Complex.exp (Complex.I * φ) := by
  rw [seqR_one_apply]
  simp

/-- `x = -1`, two phases: `P(-1) = e^{i(φ₁+φ₂)}`. -/
example (φ₁ φ₂ : ℝ) :
    (seqR [φ₁, φ₂] (-1)) 0 0 = Complex.exp (Complex.I * φ₁) * Complex.exp (Complex.I * φ₂) := by
  rw [seqR_neg_one_apply]
  simp

/-- The alternating sum. -/
example : alt [1, 2, 3] = 2 := by norm_num [alt]

/-- `x = 0`, even length: `P(0) = e^{i(φ₁ - φ₂)}`. -/
example (φ₁ φ₂ : ℝ) :
    (seqR [φ₁, φ₂] 0) 0 0 = Complex.exp (Complex.I * ((φ₁ - φ₂ : ℝ) : ℂ)) := by
  rw [seqR_zero_apply_of_even ⟨1, rfl⟩]
  simp

/-- `x = 0`, odd length: `P(0) = 0`. -/
example (φ : ℝ) : (seqR [φ] 0) 0 0 = 0 :=
  seqR_zero_apply_of_odd ⟨0, rfl⟩

/-! ### Axiom audit -/

/-- info: 'QSVT.QSP.seqR_chebPhases_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqR_chebPhases_eq

/-- info: 'QSVT.QSP.seqR_chebPhases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqR_chebPhases

/-- info: 'QSVT.QSP.seqR_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqR_one_apply

/-- info: 'QSVT.QSP.seqR_neg_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqR_neg_one_apply

/-- info: 'QSVT.QSP.seqR_zero_even_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqR_zero_even_odd
