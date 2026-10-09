/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.QSP.Complementary

/-!
# QSVTTest.Complementary

Sanity checks for the complementary-polynomial theorems (QSP-7a/7b/7d: GSLW Lemma 6, Theorem 5,
Cor 10) in small degrees, the elementary identities behind them, and axiom audits.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open Polynomial QSVT.QSP QSVT.Poly

/-! ### The elementary identities -/

/-- The Brahmagupta–Fibonacci identity with weight `w` (pure `ring`). -/
example (w B₁ C₁ B₂ C₂ : ℝ[X]) :
    (B₁ ^ 2 + w * C₁ ^ 2) * (B₂ ^ 2 + w * C₂ ^ 2) =
      (B₁ * B₂ - w * (C₁ * C₂)) ^ 2 + w * (B₁ * C₂ + B₂ * C₁) ^ 2 :=
  sumsq_mul_sumsq w B₁ C₁ B₂ C₂

/-- GSLW (10): for `v ≥ 1` the quadratic factor is `v - X²`. -/
example (v : ℝ) (hv : 1 ≤ v) :
    (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2) : ℝ[X]) = C v - X ^ 2 := by
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
  simp only [C_neg, C_sub, C_1]
  ring

/-- GSLW (11): for `v ≤ 0` the quadratic factor is `X² - v` (`= X² + t²` for `v = -t²`). -/
example (v : ℝ) (hv : v ≤ 0) :
    (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2) : ℝ[X]) = X ^ 2 - C v := by
  rw [abs_of_nonneg (by linarith), abs_of_nonpos hv, C_sub, C_1, C_neg]
  ring

/-- GSLW (12): the quartic attached to `a = s²` over `ℂ`. -/
example (a : ℂ) :
    (quartic a).map (algebraMap ℝ ℂ) = (X ^ 2 - C a) * (X ^ 2 - C ((starRingEnd ℂ) a)) :=
  quartic_map a

/-- The quartic for `a = i` is `X⁴ + 1`. -/
example : quartic Complex.I = X ^ 4 + 1 := by
  simp [quartic]

/-! ### Lemma 6 in small cases -/

/-- The constant `1` has a `0`-representation. -/
example : SOSRep 0 (1 : ℝ[X]) := by
  have h := sosRep_C_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
  rwa [C_1] at h

/-- The constant `1` also has a `1`-representation (`1 = X² + (1 - X²)`). -/
example : SOSRep 1 (1 : ℝ[X]) := by
  have h := sosRep_C_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
  rw [C_1] at h
  exact h.succ

/-- Lemma 6 for `A = 1 - X²` (`k = 1`): e.g. `B = 0`, `C = 1`. -/
example : ∃ B C : ℝ[X], (1 - X ^ 2 : ℝ[X]) = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧ B.natDegree ≤ 1 ∧
    C.natDegree ≤ 1 - 1 ∧ (1 = 0 → C = 0) ∧ HasParity (B.map (algebraMap ℝ ℂ)) 1 ∧
    HasParity (C.map (algebraMap ℝ ℂ)) (1 - 1) :=
  exists_sumsq_decomposition 1 (1 - X ^ 2)
    (by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X, sq]
      exact isEven_one.sub (hasParity_X.X_mul.1 even_two))
    (by compute_degree)
    (fun x hx => by rw [eval_sub, eval_one, eval_pow, eval_X]; nlinarith [hx.1, hx.2])

/-! ### Theorem 5 / Cor 10 in degree `1` -/

/-- `P̃ = X` (`k = 1`): the complementary pair exists with `Re P = X`. -/
example : ∃ P Q : ℂ[X], P.natDegree ≤ 1 ∧ Q.natDegree ≤ 1 - 1 ∧ (1 = 0 → Q = 0) ∧
    HasParity P 1 ∧ HasParity Q (1 - 1) ∧ P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1 ∧
    QSVT.SVT.rePoly P = (X : ℝ[X]).map (algebraMap ℝ ℂ) :=
  exists_complement 1 X natDegree_X_le (by rw [Polynomial.map_X]; exact hasParity_X)
    (fun x hx => by rw [eval_X]; nlinarith [hx.1, hx.2])

/-- `P̃ = X` is realised by a reflection-convention phase list of length `1`. -/
example : ∃ Φ : List ℝ, Φ.length = 1 ∧
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ((seqR Φ x) 0 0).re = (X : ℝ[X]).eval x :=
  exists_phases_R_real 1 le_rfl X natDegree_X_le (by rw [Polynomial.map_X]; exact hasParity_X)
    (fun x hx => by rw [eval_X]; nlinarith [hx.1, hx.2])

/-- The direct assembly from a Lemma 6 decomposition: `P̃ = X`, `B = 0`, `C = 1`. -/
example : ∃ P Q : ℂ[X], P.natDegree ≤ 1 ∧ Q.natDegree ≤ 1 - 1 ∧ (1 = 0 → Q = 0) ∧
    HasParity P 1 ∧ HasParity Q (1 - 1) ∧ P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1 ∧
    QSVT.SVT.rePoly P = (X : ℝ[X]).map (algebraMap ℝ ℂ) :=
  exists_complement_of_sumsq (B := 0) (C := 1) natDegree_X_le
    (by rw [Polynomial.map_X]; exact hasParity_X) (by ring) (by simp) (by simp)
    (fun h => absurd h one_ne_zero) (by rw [Polynomial.map_zero]; exact hasParity_zero _)
    (by rw [Polynomial.map_one]; exact hasParity_one)

/-! ### Axiom audit -/

/-- info: 'QSVT.QSP.sosRep_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.sosRep_of_nonneg

/--
info: 'QSVT.QSP.exists_sumsq_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QSVT.QSP.exists_sumsq_decomposition

/-- info: 'QSVT.QSP.exists_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.exists_complement

/-- info: 'QSVT.QSP.exists_phases_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.exists_phases_real

/--
info: 'QSVT.QSP.exists_phases_R_real' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms QSVT.QSP.exists_phases_R_real
