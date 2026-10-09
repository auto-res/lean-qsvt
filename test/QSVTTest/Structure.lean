/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.QSP.Structure

/-!
# QSVTTest.Structure

Regression tests for the QSP structure theorem (formal-spec QSP-3): concrete instances of
`seqR_eval` for one and two phases, and the axiom audit of the main theorems.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open Polynomial QSVT.QSP

/-! ### One phase: `seqR [φ] x = [[e^{iφ} x, e^{iφ} s], [e^{-iφ} s, -e^{-iφ} x]]` -/

/-- `qspPoly [φ] = (e^{iφ} X, e^{-iφ})`. -/
example (φ : ℝ) :
    qspPoly [φ] = (C (Complex.exp (Complex.I * φ)) * X, C (Complex.exp (-(Complex.I * φ)))) := by
  rw [qspPoly_cons, qspPoly_nil]
  simp

/-- The evaluation theorem specialised to one phase (statement-level check). -/
example (φ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    seqR [φ] x =
      !![(qspPoly [φ]).1.eval (x : ℂ),
          (conjP (qspPoly [φ]).2).eval (-(x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ);
        (qspPoly [φ]).2.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (conjP (qspPoly [φ]).1).eval (-(x : ℂ))] :=
  seqR_eval hx [φ]

/-- Top-left entry for one phase: `e^{iφ} x`. -/
example (φ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    seqR [φ] x 0 0 = Complex.exp (Complex.I * φ) * x := by
  rw [seqR_apply_zero_zero hx, qspPoly_cons, qspPoly_nil]
  simp

/-- Bottom-right entry for one phase: `-e^{-iφ} x` (the sign comes from `det R = -1`). -/
example (φ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    seqR [φ] x 1 1 = -(Complex.exp (-(Complex.I * φ)) * x) := by
  rw [seqR_eval hx, qspPoly_cons, qspPoly_nil]
  simp [conj_exp_I_mul]

/-! ### Two phases -/

/-- The evaluation theorem specialised to two phases (statement-level check). -/
example (φ ψ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    seqR [φ, ψ] x =
      !![(qspPoly [φ, ψ]).1.eval (x : ℂ),
          (conjP (qspPoly [φ, ψ]).2).eval (-(x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ);
        (qspPoly [φ, ψ]).2.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (conjP (qspPoly [φ, ψ]).1).eval (-(x : ℂ))] :=
  seqR_eval hx [φ, ψ]

/-- Top-left entry for two phases: `e^{iφ} (e^{iψ} x² + e^{-iψ} (1 - x²))`. -/
example (φ ψ x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    seqR [φ, ψ] x 0 0 =
      Complex.exp (Complex.I * φ) *
        (Complex.exp (Complex.I * ψ) * x ^ 2 + Complex.exp (-(Complex.I * ψ)) * (1 - x ^ 2)) := by
  rw [seqR_apply_zero_zero hx, qspPoly_cons, qspPoly_cons, qspPoly_nil]
  simp
  ring

/-- Degree and parity bookkeeping for two phases. -/
example (φ ψ : ℝ) : (qspPoly [φ, ψ]).1.natDegree ≤ 2 := natDegree_fst_le [φ, ψ]

example (φ ψ : ℝ) : (qspPoly [φ, ψ]).2.natDegree ≤ 1 := natDegree_snd_le [φ, ψ]

example (φ ψ : ℝ) : QSVT.Poly.IsEven (qspPoly [φ, ψ]).1 :=
  (hasParity_fst [φ, ψ]).isEven ⟨1, rfl⟩

example (φ ψ : ℝ) : QSVT.Poly.IsOdd (qspPoly [φ, ψ]).2 :=
  (hasParity_snd [φ, ψ]).isOdd ⟨0, rfl⟩

/-! ### Axiom audit -/

/-- info: 'QSVT.QSP.seqR_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.seqR_eval

/-- info: 'QSVT.QSP.norm_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.norm_identity

/-- info: 'QSVT.QSP.qspPoly_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.qspPoly_neg

/-- info: 'QSVT.QSP.hasParity_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.hasParity_fst

/-- info: 'QSVT.QSP.natDegree_snd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.QSP.natDegree_snd_le
