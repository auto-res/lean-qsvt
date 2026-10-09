/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVTHeavy.InverseAA

/-!
# QSVTTest.InverseAA

Regression tests for the gap-`0.1` fixed-point amplitude amplification (APP-1,
`QSVTHeavy.FixedPointAAD01`) and the matrix-inversion block composed with it (APP-3 completion,
`QSVTHeavy.InverseAA`, GSLW Thm 41 flavour): the headline statements instantiated, the resource
counts (`35` queries per round, `35 · 435 = 15225` oracle queries in all), the numerical margins
behind `invAmp_ge_01`, `fixedPointAAD01_amplitude` and `inverseAA_output_le`, and the axiom audit
(kernel trust only). Each check is a compile-time assertion.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Certificate QSVT.Examples
open QSVT.IR QSVT.Pipeline
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### APP-1 with gap `0.1`: fixed-point amplitude amplification -/

section AA

variable {U : L ℋ} {G : L ℋ} {ψ₀ ψG : ℋ} {a : ℝ} (hU : U ∈ unitary (L ℋ)) (hG : IsProjective G)
  (hψ₀ : ‖ψ₀‖ = 1) (hψG : ‖ψG‖ = 1) (ha0 : 0 < a) (hGU : G (U ψ₀) = (a : ℂ) • ψG)

/-- Exact action: the output in the good subspace is `Re[P_Φ̃](a) ψ_G`. -/
example :
    topLeft (blockDiag G 0 * aaCircuitD01 hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ =
      ((rePoly (qspPoly (signD01Phases.map (↑))).1).eval (a : ℂ)) • ψG :=
  fixedPointAAD01_apply hU hG hψ₀ hψG ha0 hGU

/-- Fixed-point property: amplitude `≈ 0.9875` for every `a ≥ 0.1`. -/
example (ha : 0.1 ≤ a) :
    ‖topLeft (blockDiag G 0 * aaCircuitD01 hU hG hψ₀ * blockDiag (rankOne ψ₀) 0) ψ₀ -
        (signD01Scale : ℂ) • ψG‖ ≤ signD01Eps + 0.012 :=
  fixedPointAAD01_bound hU hG hψ₀ hψG ha0 hGU ha

/-- Success amplitude at least `0.975` after one run. -/
example (ha : 0.1 ≤ a) : 0.975 ≤ ‖blockDiag G 0 (aaCircuitD01 hU hG hψ₀ (inl ψ₀))‖ :=
  fixedPointAAD01_amplitude hU hG hψ₀ hψG ha0 hGU ha

/-- The circuit is the compiled gate list. -/
example :
    aaCircuitD01 hU hG hψ₀ =
      QSVT.Circuit.denote (aaEncoding hU hG hψ₀)
        (QSVT.Circuit.compileQsvtReal (signD01Phases.map (↑))) :=
  aaCircuitD01_eq_denote hU hG hψ₀

end AA

/-! ### APP-3: the inversion block with amplitude amplification -/

section Inverse

variable (E : HermitianEncoding ℋ) (b : ℋ) (hb : E.P b = b) (hb1 : ‖b‖ = 1)
  (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|)

/-- The initial amplitude is above the gap of `signD01`. -/
example : 0.1 ≤ invAmp E b := invAmp_ge_01 E b hb hb1 hsupp

/-- The initial amplitude equals the APP-COMPOSE amplitude of the Route A circuit. -/
example : regAmp E (invCircuit E) b = invAmp E b := regAmp_invCircuit E b hb

/-- The ideal solution solves `A x = (invScale/4) b`. -/
example : E.encoded (idealInv E b) = (((invScale : ℝ) / 4 : ℝ) : ℂ) • b :=
  encoded_idealInv E b hb hsupp

/-- Success amplitude at least `0.975` after one round. -/
example : 0.975 ≤ ‖blockDiag (atZero E.P) 0 (inverseAA E b hb1 (inl (inj 0 b)))‖ :=
  inverseAA_amplitude E b hb hb1 hsupp

/-- The headline: the output is `0.9875 · |0⟩ ⊗ A⁻¹b/‖A⁻¹b‖` up to `0.02`. -/
example :
    ‖topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (signD01Scale : ℂ) • inj 0 (idealInvState E b)‖ ≤ 0.02 :=
  inverseAA_output_le E b hb hb1 hsupp

end Inverse

/-! ### Numerical margins -/

/-- The gap-`0.1` amplitude bound: `0.1 · ‖c‖₁ ≤ invScale/4 − ε` for `‖c‖₁ ≤ 1.6636`. -/
example : (0.1 : ℝ) * 1.6636 ≤ (invScale : ℝ) / 4 - invEps := by
  rw [invScale, invEps]; norm_num

/-- Numerically `a ≥ 0.112`: `(invScale/4 − ε)/1.6636 ≥ 0.112`. -/
example : (0.112 : ℝ) * 1.6636 ≤ (invScale : ℝ) / 4 - invEps := by
  rw [invScale, invEps]; norm_num

/-- The plateau lower bound minus the phase error exceeds `0.975`. -/
example : (0.975 : ℝ) ≤ 0.9755 - signD01Eps := by
  rw [signD01Eps]; norm_num

/-- The success probability bound `0.975² > 0.95`. -/
example : (0.95 : ℝ) < 0.975 ^ 2 := by norm_num

/-- The closeness constant `2ε/(invScale/4) = 0.008`. -/
example : (2 * invEps / ((invScale : ℝ) / 4) : ℝ) = 0.008 := by
  rw [invScale, invEps]; norm_num

/-- The headline constant: `10⁻¹² + 0.012 + 0.9875 · 0.008 ≤ 0.02`. -/
example :
    (signD01Eps : ℝ) + 0.012 + signD01Scale * (2 * invEps / ((invScale : ℝ) / 4)) ≤ 0.02 := by
  rw [signD01Eps, signD01Scale, invEps, invScale]; norm_num

/-- Resources: `35` queries and `142` gates per amplification round, `15225` oracle queries. -/
example : QSVT.Circuit.oracleCount (QSVT.Circuit.compileQsvtReal (signD01Phases.map (↑))) = 35 :=
  aaCircuitD01_oracleCount
example : (QSVT.Circuit.compileQsvtReal (signD01Phases.map (↑))).length = 142 :=
  aaCircuitD01_length
example : inverseAA_queries = 15225 := inverseAA_queries_eq
#guard 35 * 435 = 15225

/-! ### Axiom audit: kernel trust only -/

/-- info: 'QSVT.Examples.fixedPointAAD01_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPointAAD01_apply

/-- info: 'QSVT.Examples.fixedPointAAD01_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPointAAD01_bound

/-- info: 'QSVT.Examples.fixedPointAAD01_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fixedPointAAD01_amplitude

/-- info: 'QSVT.Examples.aaCircuitD01_eq_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aaCircuitD01_eq_denote

/-- info: 'QSVT.Examples.regAAD01_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regAAD01_amplitude

/-- info: 'QSVT.Examples.invAmp_ge_01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invAmp_ge_01

/-- info: 'QSVT.Examples.encoded_idealInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encoded_idealInv

/-- info: 'QSVT.Examples.inverseAA_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inverseAA_amplitude

/-- info: 'QSVT.Examples.inverseAA_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inverseAA_output

/-- info: 'QSVT.Examples.inverseAA_output_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inverseAA_output_le

/-- info: 'QSVT.Examples.inverseAA_queries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inverseAA_queries_eq
