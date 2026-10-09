/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.EvolutionAA

/-!
# QSVTTest.EvolutionAA

Regression tests for the composition machinery (APP-COMPOSE, `QSVT.Examples.Compose`) and the
Hamiltonian-simulation algorithm with amplitude amplification (APP-4 completion,
`QSVT.Examples.EvolutionAA`): the lower bound of the polynomial functional calculus, the
register-to-AA bridge, the headline statements instantiated, the numerical margins
(`a ≥ 0.15`, output error `≤ 0.0237`, `1386` queries), and the axiom audit (kernel trust only).
Each check is a compile-time assertion.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.IR QSVT.QSP QSVT.Poly QSVT.Pipeline QSVT.Certificate
  QSVT.Examples
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### APP-COMPOSE: functional calculus and the register-to-AA bridge -/

section Compose

variable (E : HermitianEncoding ℋ)

/-- Lower bound of the polynomial functional calculus on `ran Π`. -/
example (p : ℂ[X]) (m : ℝ) (hm : ∀ i, m ≤ ‖p.eval (eigenValue E i : ℂ)‖) (x : ℋ)
    (hx : E.P x = x) : m * ‖x‖ ≤ ‖aeval E.encoded p x‖ :=
  norm_aeval_apply_ge E p m hm x hx

/-- `funCalc` agrees with `p(A)` on `ran Π`. -/
example (p : ℂ[X]) (x : ℋ) (hx : E.P x = x) :
    aeval E.encoded p x = funCalc E (fun t => p.eval (t : ℂ)) x :=
  aeval_eq_funCalc E p x hx

/-- Unimodular functions act isometrically on `ran Π`. -/
example (f : ℝ → ℂ) (hf : ∀ i, ‖f (eigenValue E i)‖ = 1) (x : ℋ) (hx : E.P x = x) :
    ‖funCalc E f x‖ = ‖x‖ :=
  norm_funCalc_eq_of_unimodular E f hf x hx

/-- The good component of `W (|0⟩ ⊗ b)` under `|0⟩⟨0| ⊗ Π` is `|0⟩ ⊗ (Π W₀₀ Π) b`. -/
example {m : ℕ} [NeZero m] (W : L (Reg m ℋ)) (b : ℋ) (hb : E.P b = b) :
    atZero E.P (W (inj 0 b)) = inj 0 (regTopLeft (regP E * W * regP E) b) :=
  atZero_P_apply E W b hb

/-- The APP-1 hypotheses `G (U ψ₀) = a ψ_G`, `‖ψ_G‖ = 1`. -/
example {m : ℕ} [NeZero m] (W : L (Reg m ℋ)) (b : ℋ) (hb : E.P b = b)
    (h : 0 < regAmp E W b) :
    atZero E.P (W (inj 0 b)) = ((regAmp E W b : ℝ) : ℂ) • regGoodState E W b ∧
      ‖regGoodState E W b‖ = 1 :=
  ⟨atZero_P_apply_eq_smul E W b hb h, norm_regGoodState E W b h⟩

/-- Normalisation is `2`-Lipschitz towards unit vectors. -/
example (v w : ℋ) (hv : v ≠ 0) (hw : ‖w‖ = 1) :
    ‖((‖v‖ : ℝ) : ℂ)⁻¹ • v - w‖ ≤ 2 * ‖v - w‖ :=
  norm_normalize_sub_le v w hv hw

end Compose

/-! ### APP-4: Hamiltonian simulation with amplitude amplification -/

section EvolutionAA

variable (E : HermitianEncoding ℋ) (b : ℋ) (hb : E.P b = b) (hb1 : ‖b‖ = 1)

/-- The initial amplitude is above the sign-polynomial threshold. -/
example : 0.15 ≤ evoAmp E b := evoAmp_ge_015 E b hb hb1

/-- Two-sided bounds on the initial amplitude. -/
example : (1 - 2 * 0.000001) / evoL1 ≤ evoAmp E b ∧ evoAmp E b ≤ (1 + 2 * 0.000001) / evoL1 :=
  ⟨evoAmp_ge E b hb hb1, evoAmp_le E b hb hb1⟩

/-- Exact action of the composed circuit on the good subspace. -/
example :
    topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) =
      ((rePoly (qspPoly (sign21Phases.map (↑))).1).eval ((evoAmp E b : ℝ) : ℂ)) •
        evoGoodState E b :=
  evolutionAA_apply E b hb hb1

/-- Success amplitude at least `0.869` after one round. -/
example : 0.869 ≤ ‖blockDiag (atZero E.P) 0 (evolutionAA E b hb1 (inl (inj 0 b)))‖ :=
  evolutionAA_amplitude E b hb hb1

/-- The ideal evolved state is a unit vector, and the prepared state is within `4ε` of it. -/
example : ‖idealEvo E b‖ = 1 := by rw [norm_idealEvo E b hb, hb1]
example : ‖evoGoodState E b - inj 0 (idealEvo E b)‖ ≤ 4 * 0.000001 :=
  norm_evoGoodState_sub_idealEvo_le E b hb hb1

/-- Headline: the good-subspace output is `sign21Scale · |0⟩ ⊗ e^{-2iA} b` up to `0.0237`. -/
example :
    ‖topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (sign21Scale : ℂ) • inj 0 (idealEvo E b)‖ ≤ 0.0237 :=
  evolutionAA_output_le E b hb hb1

end EvolutionAA

/-! ### Numerical margins -/

/-- `a ≥ (1 − 2ε)/‖c‖₁ ≥ 0.412`, comfortably above the threshold `0.15`. -/
example : (0.412 : ℝ) ≤ (1 - 2 * 0.000001) / 2.4258 := by norm_num
example : (0.15 : ℝ) ≤ (1 - 2 * 0.000001) / 2.4258 := by norm_num

/-- The exact output bound is below the clean constant `0.0237`. -/
example : (sign21Eps : ℝ) + 0.0236 + sign21Scale * (4 * 0.000001) ≤ 0.0237 := by
  rw [sign21Eps, sign21Scale]; norm_num

/-- `c · 4ε < 4 · 10⁻⁶`. -/
example : (sign21Scale : ℝ) * (4 * 0.000001) < 4 * 0.000001 := by
  rw [sign21Scale]; norm_num

/-- Success probability `0.869² > 0.75` against `a² ≤ ((1 + 2ε)/2.4257)² < 0.17` initially. -/
example : (0.75 : ℝ) < 0.869 ^ 2 := by norm_num
example : ((1 + 2 * 0.000001) / 2.4257 : ℝ) ^ 2 < 0.17 := by norm_num

/-- Resources: `21 · 66 = 1386` oracle queries. -/
example : evolutionAA_queries = 1386 := evolutionAA_queries_eq
#guard 21 * 66 = 1386

/-! ### Axiom audit: kernel trust only -/

/-- info: 'QSVT.Examples.norm_aeval_apply_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_aeval_apply_ge

/-- info: 'QSVT.Examples.norm_normalize_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_normalize_sub_le

/-- info: 'QSVT.Examples.regAA_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms regAA_amplitude

/-- info: 'QSVT.Examples.evoAmp_ge_015' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evoAmp_ge_015

/-- info: 'QSVT.Examples.evolutionAA_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evolutionAA_apply

/-- info: 'QSVT.Examples.evolutionAA_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evolutionAA_amplitude

/-- info: 'QSVT.Examples.norm_evoGoodState_sub_idealEvo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_evoGoodState_sub_idealEvo_le

/-- info: 'QSVT.Examples.evolutionAA_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evolutionAA_output
