/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVTHeavy.SignD01Phases

/-!
# QSVTTest.SignD01

Regression tests for the second certified sign approximation (CERT-B, gap `δ = 0.1`, degree
`35`): the polynomial certificates of `QSVT.Certificate.SignD01`, the kernel-checked phases of
`QSVT.Certificate.SignD01Phases`, the shape of the data (`35` phases, `36` target coefficients,
symmetric phases, `|φ| ≤ 2.1`, odd polynomial), the identification of the phase target with the
Chebyshev coefficients of `signD01` computed by POLY-6, the headline theorems instantiated, and the
axiom audit (kernel trust only).  Each check is a compile-time assertion.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Poly
open Polynomial

/-! ### The certified data -/

#guard signD01.length = 36
#guard signD01Phases.length = 35
#guard signD01Target.length = 36
#guard signD01Eps = 1 / 1000000000000
#guard signD01Scale = 79 / 80
#guard signD01Delta = 1 / 10

-- the plateau centre and ripple: `c ± ε_p` are the certified plateau bounds
#guard signD01Scale - 0.012 = 0.9755
#guard signD01Scale + 0.012 = 0.9995

-- `signD01` is odd (even monomial coefficients vanish) with alternating odd coefficients
#guard (List.range 18).all fun j => signD01.getD (2 * j) 0 == 0
#guard (List.range 18).all fun j => (0 : ℚ) < (-1 : ℚ) ^ j * signD01.getD (2 * j + 1) 0

-- symmetric QSP phases: the last `34` are palindromic
#guard signD01Phases.tail = signD01Phases.tail.reverse

-- phase magnitudes `|φ| ≤ 2.1` (the reason for Taylor depth `30` in `signD01_checkRe`)
#guard signD01Phases.all fun φ => |φ| ≤ 2.1

-- the target is odd (even coefficients vanish) with alternating odd coefficients
#guard (List.range 18).all fun j => signD01Target.getD (2 * j) 0 == 0
#guard (List.range 18).all fun j => (0 : ℚ) < (-1 : ℚ) ^ j * signD01Target.getD (2 * j + 1) 0

-- the JSON target coincides with the Chebyshev coefficients of `signD01` computed by POLY-6
#guard signD01Target = (ChebQC.ofMonomials (PolyQ.toPolyQC signD01)).map Prod.fst

example : signD01Phases.length = 35 := signD01Phases_length
example : signD01Target.length = 36 := signD01Target_length

/-! ### The headline theorems instantiated -/

/-- CERT-B part 1: admissibility and the plateau of the polynomial. -/
example : supNorm signD01.toPoly ≤ 1 := supNorm_signD01_le_one

example : ∀ x ∈ Set.Icc (0.1 : ℝ) 1,
    ‖signD01.toPoly.eval (x : ℂ) - ((signD01Scale : ℝ) : ℂ)‖ ≤ 0.012 :=
  norm_eval_signD01_sub_scale_le

example : ∀ x ∈ Set.Icc (-1 : ℝ) (-0.1),
    ‖signD01.toPoly.eval (x : ℂ) + ((signD01Scale : ℝ) : ℂ)‖ ≤ 0.012 :=
  norm_eval_signD01_add_scale_le

/-- CERT-B part 2: the certified polynomial statement about the phases. -/
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) - signD01.toPoly.eval (x : ℂ)‖ ≤
      ((1 / 10 ^ 12 : ℚ) : ℝ) :=
  signD01_rePoly_bound

/-- The phase target is the certified polynomial. -/
example : ChebC.target signD01Target = signD01.toPoly := target_signD01_eq

/-- The real-valued form of the phase certificate through `checkRe_sound_real`. -/
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |((qspPoly (signD01Phases.map (↑))).1.eval (x : ℂ)).re -
      ∑ k ∈ Finset.range signD01Target.length,
        (signD01Target.getD k 0 : ℝ) * (Polynomial.Chebyshev.T ℝ k).eval x| ≤
      (signD01Eps : ℝ) :=
  checkRe_sound_real signD01_checkRe

/-- The realised polynomial on the positive plateau. -/
example : ∀ x ∈ Set.Icc (0.1 : ℝ) 1,
    ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) - (signD01Scale : ℂ)‖ ≤
      signD01Eps + 0.012 :=
  signD01_rePoly_sub_scale_le

/-- The realised polynomial on the negative plateau. -/
example : ∀ x ∈ Set.Icc (-1 : ℝ) (-0.1),
    ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) + (signD01Scale : ℂ)‖ ≤
      signD01Eps + 0.012 :=
  signD01_rePoly_add_scale_le

/-- The global bound on the realised polynomial. -/
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ)‖ ≤ 1 + signD01Eps :=
  signD01_rePoly_norm_le

/-- The total error bound is below `0.0121`, and the certified output amplitude lies in
`[0.975, 1]`. -/
example : (signD01Eps : ℝ) + 0.012 ≤ 0.0121 := by
  rw [signD01Eps]; norm_num

example : (0.975 : ℝ) ≤ (signD01Scale : ℝ) - 0.012 - signD01Eps ∧
    (signD01Scale : ℝ) + 0.012 + signD01Eps ≤ 1 := by
  rw [signD01Scale, signD01Eps]; norm_num

/-! ### Axiom audit: kernel trust only (no `Lean.ofReduceBool`) -/

/-- info: 'QSVT.Certificate.signD01_horner_bound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_horner_bound_nonneg

/-- info: 'QSVT.Certificate.signD01_horner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_horner_bound

/-- info: 'QSVT.Certificate.signD01_plateau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_plateau

/-- info: 'QSVT.Certificate.signD01_plateau_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_plateau_neg

/-- info: 'QSVT.Certificate.supNorm_signD01_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_signD01_le_one

/-- info: 'QSVT.Certificate.norm_eval_signD01_sub_scale_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_signD01_sub_scale_le

/-- info: 'QSVT.Certificate.norm_eval_signD01_add_scale_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_eval_signD01_add_scale_le

/-- info: 'QSVT.Certificate.signD01_checkRe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_checkRe

/-- info: 'QSVT.Certificate.target_signD01_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_signD01_eq

/-- info: 'QSVT.Certificate.signD01_rePoly_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_rePoly_bound

/-- info: 'QSVT.Certificate.signD01_rePoly_sub_scale_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_rePoly_sub_scale_le

/-- info: 'QSVT.Certificate.signD01_rePoly_add_scale_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_rePoly_add_scale_le

/-- info: 'QSVT.Certificate.signD01_rePoly_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signD01_rePoly_norm_le
