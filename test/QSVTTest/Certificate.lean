/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Bound
import QSVT.Certificate.Sign21

/-!
# QSVTTest.Certificate

Regression tests for the LeanCert glue (formal-spec CERT-B, part 1): the Horner evaluation of
concrete coefficient lists, a small kernel-checked LeanCert certificate written through
`PolyQ.horner`, and the axiom audit of the glue lemmas and of the certified theorems (kernel
trust: no `Lean.ofReduceBool`).
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QSVT.Poly QSVT.Certificate

/-! ### Horner evaluation -/

-- `4 · 2³ − 3 · 2 = 26`
example : cheb3.horner 2 = 26 := by
  simp only [cheb3, PolyQ.horner]
  norm_num

example (x : ℝ) : PolyQ.horner [1 / 2, 0, 1 / 2] x = 1 / 2 + x * (0 + x * (1 / 2 + x * 0)) := by
  simp only [PolyQ.horner]
  push_cast
  rfl

-- the fold form agrees
example (x : ℝ) :
    cheb3.horner x = ([0, -3, 0, 4] : PolyQ).foldr (fun (a : ℚ) acc => (a : ℝ) + x * acc) 0 :=
  PolyQ.horner_eq_foldr _ _

-- `sub` pads with zeros
#guard PolyQ.sub [1, 2] [1] = [0, 2]
#guard PolyQ.sub [1] [1, 2] = [0, -2]
#guard PolyQ.toPolyQC [1, -1 / 2] = [(1, 0), (-1 / 2, 0)]

/-! ### A small LeanCert certificate through `PolyQ.horner` (kernel trust) -/

-- `x² = (T₀ + T₂) / 2` is bounded by `1` on `[-1, 1]`; with a decimal slack.
theorem sq_horner_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ PolyQ.horner [0, 0, 1] x ∧ PolyQ.horner [0, 0, 1] x ≤ 1.0001 := by
  simp only [PolyQ.horner]
  push_cast
  leancert (trust := kernel)

-- and its transfer to the complex polynomial
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    ‖(PolyQ.toPoly [0, 0, 1]).eval (x : ℂ) - ((0.50005 : ℝ) : ℂ)‖ ≤ 0.50005 :=
  PolyQ.forall_norm_eval_sub_le_of_two_sided fun x hx => by
    have h := sq_horner_bound x hx
    constructor <;> linarith [h.1, h.2]

/-! ### Axiom audit: kernel-checked certificates use only the standard three axioms -/

/-- info: 'QSVT.Certificate.PolyQ.eval_toPoly_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolyQ.eval_toPoly_ofReal

/-- info: 'QSVT.Certificate.PolyQ.supNorm_sub_le_of_horner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolyQ.supNorm_sub_le_of_horner

/-- info: 'QSVT.Certificate.cheb3_horner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cheb3_horner_bound

/-- info: 'QSVT.Certificate.supNorm_cheb3_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_cheb3_le_one

/-- info: 'sq_horner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sq_horner_bound

/-- info: 'QSVT.Certificate.sign21_horner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign21_horner_bound

/-- info: 'QSVT.Certificate.supNorm_sign21_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_sign21_le_one

/-- info: 'QSVT.Certificate.sign21_plateau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign21_plateau

/-- info: 'QSVT.Certificate.sign21_plateau_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign21_plateau_neg

/-- info: 'QSVT.Certificate.norm_eval_sign21_sub_scale_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_sign21_sub_scale_le
