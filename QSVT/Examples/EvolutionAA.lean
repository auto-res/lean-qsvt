/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Examples.Compose
import QSVT.Examples.Evolution

/-!
# APP-4 (completion): Hamiltonian simulation `e^{-2iA} b` with amplitude amplification

GSLW Thm 58 ("Hamiltonian simulation") prepares `e^{-itA} |b⟩` from a block encoding of `A` in two
steps: a polynomial approximation of `e^{-itx}` implemented by QSVT/LCU, which produces
`e^{-itA} b / ‖c‖₁` in the ancilla-`0` branch (a subnormalised state), followed by fixed-point
amplitude amplification (GSLW Thm 27) to remove the subnormalisation with a constant number of
rounds. This module composes the two certified building blocks of this library for `t = 2`:

* the Route A circuit `evoCircuit E` of APP-4 (`QSVT.Examples.Evolution`), which implements
  `p(A)/‖c‖₁` exactly for the degree-11 certified polynomial `p = evoPoly ≈ e^{-2ix}`
  (`‖p − e^{-2ix}‖ ≤ 2ε` on `[-1, 1]`, `ε = 10⁻⁶`, `‖c‖₁ = evoL1 ≈ 2.4258`, `66` oracle queries);
* the fixed-point amplitude amplification `aaCircuit` of APP-1 (`QSVT.Examples.FixedPointAA`),
  through the register-to-AA bridge of APP-COMPOSE (`QSVT.Examples.Compose`).

## Statements (for `E : HermitianEncoding ℋ`, `b ∈ ran Π`, `‖b‖ = 1`)

* The initial good amplitude is `a = evoAmp E b = ‖p(A) b‖ / ‖c‖₁`, with the lower bound
  `(1 − 2ε)/‖c‖₁ ≤ a` (`evoAmp_ge`, from the new lower bound `norm_aeval_apply_ge` of the
  polynomial functional calculus and `‖p(x)‖ ≥ ‖e^{-2ix}‖ − 2ε = 1 − 2ε`), hence `a ≥ 0.15`
  (`evoAmp_ge_015`; numerically `a ≈ 0.4122`), the threshold of the certified sign polynomial.
* The composed circuit `evolutionAA E b hb1 : L (Anc (Reg 12 ℋ))` (one ancilla qubit for the AA
  step, the `12`-dimensional Route A register, the system) satisfies the exact statement
  `evolutionAA_apply`: the good-subspace (`|0⟩⟨0| ⊗ Π` on the register, ancilla `|0⟩`) output is
  `Re[P_Φ̃](a) ψ_G` with `ψ_G = evoGoodState E b = |0⟩ ⊗ p(A) b / ‖p(A) b‖`; the fixed-point bound
  `evolutionAA_bound` (`‖output − c ψ_G‖ ≤ 10⁻¹² + 0.0236`, `c = sign21Scale ≈ 0.8924`); and the
  success amplitude `evolutionAA_amplitude`: `0.869 ≤ ‖(|0⟩⟨0| ⊗ |0⟩⟨0| ⊗ Π) W (|0⟩ ⊗ |0⟩ ⊗ b)‖`,
  so the probability of measuring both ancilla registers in `0` is at least `0.869² ≈ 0.755`
  (against `a² ≈ 0.17` without amplification), and the post-measurement state is exactly `ψ_G`.
* The ideal evolved state is `idealEvo E b = ∑ᵢ ⟪ψᵢ, b⟫ e^{-2iςᵢ} ψᵢ`, the spectral functional
  calculus `e^{-2iA} b` through the eigenbasis of `A|_{ran Π}` (APP-COMPOSE `funCalc`); it is a
  unit vector (`norm_idealEvo`, Parseval). The polynomial certificate transfers to the operators:
  `‖p(A) b − e^{-2iA} b‖ ≤ 2ε` (`norm_aeval_evoPoly_sub_idealEvo_le`), and since normalisation is
  `2`-Lipschitz, `‖ψ_G − |0⟩ ⊗ e^{-2iA} b‖ ≤ 4ε` (`norm_evoGoodState_sub_idealEvo_le`; the
  subnormalisation `1/‖c‖₁` cancels in the normalisation, `evoGoodState_eq_normalize`).
* **Headline** `evolutionAA_output`: after one round of amplitude amplification the good-subspace
  component of the output is the ideal evolved state up to
  `‖output − c · |0⟩ ⊗ e^{-2iA} b‖ ≤ 10⁻¹² + 0.0236 + c · 4ε ≤ 0.0237` (`evolutionAA_output_le`),
  with `c = sign21Scale ≈ 0.8924`.
* Resources: the AA circuit uses `evoCircuit E`/its adjoint `21` times
  (`aaCircuit_oracleCount`), each using `66` queries to `U`/`U†` (`evoCircuit_queries`), so the
  composed algorithm makes `21 · 66 = 1386` oracle queries (`evolutionAA_queries_eq`). This is a
  derived count: `evoCircuit` is an LCU on a `12`-dimensional register and has no `Circuit`
  gate-list denotation yet (the IR takes real coefficient lists), so the composed circuit is not
  yet a `Circuit.oracleCount` theorem.

## Relation to GSLW Thm 58

GSLW prepare `e^{-itA} b` to precision `ε` with success amplitude `1 − ε` after `O(1)` rounds of
fixed-point amplification with a sign polynomial of plateau value `1 − ε`. Our certified sign
polynomial (`sign21`, degree `21`, CERT-B) has plateau value `c = sign21Scale ≈ 0.8924` rather
than `1 − ε` (the phase solver's target was scaled to fit the QSP unit-disc constraint) and ripple
`0.0236` on `[0.15, 1]`; this is why the output is `≈ 0.892 · (ideal state)` with error `≈ 0.024`,
instead of `≈ 1 · (ideal state)` with error `ε`. The *direction* of the good-subspace output is
exact (`evolutionAA_apply`): conditioned on both ancillas measuring `0`, the system is in
`ψ_G = p(A) b / ‖p(A) b‖`, within `4ε = 4 · 10⁻⁶` of `e^{-2iA} b`. A sign polynomial with plateau
closer to `1` would tighten the `0.024` and raise the success probability; the composition here
would not change. The identification of `idealEvo E b` with the operator exponential
`e^{-2iA} b` (Mathlib's `NormedSpace.exp` applied to `-2i A`) is left as a remark: `funCalc` is the
spectral functional calculus, and `exp` agrees with it on the eigenbasis.

Every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`test/QSVTTest/EvolutionAA.lean`).

## Mathlib API used

`Complex.norm_exp_ofReal_mul_I`, `norm_le_norm_add_norm_sub`, `le_div_iff₀`, `norm_smul`,
`map_smul`, `map_sub`, `Complex.ofReal_inv`, `Complex.norm_ratCast`, `abs_of_nonneg`,
`sub_add_sub_cancel`, `smul_sub`.
-/

namespace QSVT.Examples

open QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Encoding QSVT.IR QSVT.Pipeline QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The polynomial: lower bound on the spectrum -/

/-- APP-4. `‖e^{-2ix}‖ = 1` for real `x`. -/
theorem norm_exp_neg_two_mul_I (x : ℝ) : ‖Complex.exp (-(2 * (x : ℂ)) * Complex.I)‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (-(2 * x))
  push_cast at this
  exact this

/-- APP-4. `‖p(x)‖ ≥ 1 − 2ε` on `[-1, 1]`, since `‖e^{-2ix}‖ = 1` and `‖p(x) − e^{-2ix}‖ ≤ 2ε`. -/
theorem norm_eval_evoPoly_ge :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      1 - 2 * 0.000001 ≤ ‖(PolyQC.toPoly evoPoly).eval (x : ℂ)‖ := by
  intro x hx
  have h := norm_eval_evoPoly_sub_exp_le x hx
  have he := norm_exp_neg_two_mul_I x
  have h3 := norm_le_norm_add_norm_sub ((PolyQC.toPoly evoPoly).eval (x : ℂ))
    (Complex.exp (-(2 * (x : ℂ)) * Complex.I))
  linarith

section Setting

variable (E : HermitianEncoding ℋ) (b : ℋ)

/-! ### The ideal evolved state -/

/-- APP-4. The ideal evolved state `e^{-2iA} b = ∑ᵢ ⟪ψᵢ, b⟫ e^{-2iςᵢ} ψᵢ`, the spectral functional
calculus of `x ↦ e^{-2ix}` through the eigenbasis of `A|_{ran Π}` (APP-COMPOSE `funCalc`). -/
noncomputable def idealEvo : ℋ :=
  funCalc E (fun t => Complex.exp (-(2 * (t : ℂ)) * Complex.I)) b

theorem idealEvo_eq_sum :
    idealEvo E b =
      ∑ i, (inner ℂ (eigenVec E i) b * Complex.exp (-(2 * (eigenValue E i : ℂ)) * Complex.I)) •
        eigenVec E i :=
  rfl

/-- APP-4. `‖e^{-2iA} b‖ = ‖b‖` for `b ∈ ran Π` (Parseval; the evolution is unitary on `ran Π`). -/
theorem norm_idealEvo (hb : E.P b = b) : ‖idealEvo E b‖ = ‖b‖ :=
  norm_funCalc_eq_of_unimodular E _ (fun _ => norm_exp_neg_two_mul_I _) b hb

/-- APP-4 (certificate transferred to the operators). `‖p(A) b − e^{-2iA} b‖ ≤ 2ε ‖b‖` for
`b ∈ ran Π`. -/
theorem norm_aeval_evoPoly_sub_idealEvo_le (hb : E.P b = b) :
    ‖aeval E.encoded (PolyQC.toPoly evoPoly) b - idealEvo E b‖ ≤ 2 * 0.000001 * ‖b‖ :=
  norm_aeval_sub_funCalc_le E _ _ _ (by norm_num)
    (fun i => norm_eval_evoPoly_sub_exp_le _ (eigenValue_mem_Icc E i)) b hb

/-- APP-4. `(1 − 2ε) ‖b‖ ≤ ‖p(A) b‖` for `b ∈ ran Π` (`norm_aeval_apply_ge`). -/
theorem norm_aeval_evoPoly_ge (hb : E.P b = b) :
    (1 - 2 * 0.000001) * ‖b‖ ≤ ‖aeval E.encoded (PolyQC.toPoly evoPoly) b‖ :=
  norm_aeval_apply_ge E _ _ (fun i => norm_eval_evoPoly_ge _ (eigenValue_mem_Icc E i)) b hb

/-! ### The initial good amplitude -/

/-- APP-4. The good vector of the Route A circuit on `b ∈ ran Π` is `‖c‖₁⁻¹ p(A) b`
(`evoCircuit_topLeft`). -/
theorem regGood_evoCircuit (hb : E.P b = b) :
    regGood E (evoCircuit E) b =
      ((evoL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded (PolyQC.toPoly evoPoly) b := by
  rw [regGood, evoCircuit_topLeft, LinearMap.smul_apply, Module.End.mul_apply, hb]

/-- APP-4. The initial good amplitude `a = ‖‖c‖₁⁻¹ p(A) b‖ = ‖p(A) b‖ / ‖c‖₁ ≈ 0.4122`. -/
noncomputable def evoAmp : ℝ := ‖((evoL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded (PolyQC.toPoly evoPoly) b‖

theorem regAmp_evoCircuit (hb : E.P b = b) : regAmp E (evoCircuit E) b = evoAmp E b := by
  rw [regAmp, regGood_evoCircuit E b hb, evoAmp]

theorem evoAmp_eq : evoAmp E b = evoL1⁻¹ * ‖aeval E.encoded (PolyQC.toPoly evoPoly) b‖ := by
  rw [evoAmp, norm_smul, norm_inv_evoL1]

/-- APP-4. `(1 − 2ε)/‖c‖₁ ≤ a` for a unit `b ∈ ran Π`. -/
theorem evoAmp_ge (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    (1 - 2 * 0.000001) / evoL1 ≤ evoAmp E b := by
  rw [evoAmp_eq, div_eq_inv_mul]
  have h := norm_aeval_evoPoly_ge E b hb
  rw [hb1, mul_one] at h
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr evoL1_pos.le)

/-- APP-4. `a ≤ (1 + 2ε)/‖c‖₁` for a unit `b ∈ ran Π` (`norm_aeval_apply_le` is not needed:
the pointwise bound `‖p‖ ≤ 1 + 2ε` and Parseval suffice). -/
theorem evoAmp_le (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    evoAmp E b ≤ (1 + 2 * 0.000001) / evoL1 := by
  rw [evoAmp_eq, div_eq_inv_mul, aeval_eq_funCalc E _ b hb]
  have h := norm_funCalc_le E (fun t => (PolyQC.toPoly evoPoly).eval (t : ℂ)) (1 + 2 * 0.000001)
    (by norm_num) (fun i => norm_eval_evoPoly_le _ (eigenValue_mem_Icc E i)) b hb
  rw [hb1, mul_one] at h
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr evoL1_pos.le)

/-- APP-4. `0.15 ≤ a`: the initial amplitude is above the threshold of the certified sign
polynomial (`(1 − 2ε)/‖c‖₁ ≥ 0.999998/2.4258 ≈ 0.412`). -/
theorem evoAmp_ge_015 (hb : E.P b = b) (hb1 : ‖b‖ = 1) : 0.15 ≤ evoAmp E b := by
  refine le_trans ?_ (evoAmp_ge E b hb hb1)
  rw [le_div_iff₀ evoL1_pos]
  have := evoL1_mem_Icc.2
  linarith

theorem evoAmp_pos (hb : E.P b = b) (hb1 : ‖b‖ = 1) : 0 < evoAmp E b := by
  linarith [evoAmp_ge_015 E b hb hb1]

/-! ### The amplitude-amplification instance -/

/-- APP-4. The normalised good state `ψ_G = a⁻¹ (|0⟩ ⊗ ‖c‖₁⁻¹ p(A) b)` on the Route A register
(GSLW Thm 27's `Π U ψ₀ / ‖Π U ψ₀‖`). -/
noncomputable def evoGoodState : Reg evoCheb.length ℋ :=
  ((evoAmp E b : ℝ) : ℂ)⁻¹ • inj 0 (((evoL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded (PolyQC.toPoly evoPoly) b)

theorem regGoodState_evoCircuit (hb : E.P b = b) :
    regGoodState E (evoCircuit E) b = evoGoodState E b := by
  rw [regGoodState, regAmp_evoCircuit E b hb, regGood_evoCircuit E b hb, evoGoodState]

/-- APP-4. The hypotheses of APP-1 for `U = evoCircuit E`, `G = |0⟩⟨0| ⊗ Π`, `ψ₀ = |0⟩ ⊗ b`:
`G (U ψ₀) = a ψ_G`. -/
theorem atZero_P_evoCircuit_apply (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    atZero E.P (evoCircuit E (inj 0 b)) = ((evoAmp E b : ℝ) : ℂ) • evoGoodState E b := by
  rw [← regAmp_evoCircuit E b hb, ← regGoodState_evoCircuit E b hb]
  exact atZero_P_apply_eq_smul E (evoCircuit E) b hb
    (by rw [regAmp_evoCircuit E b hb]; exact evoAmp_pos E b hb hb1)

/-- APP-4. `‖ψ_G‖ = 1`. -/
theorem norm_evoGoodState (hb : E.P b = b) (hb1 : ‖b‖ = 1) : ‖evoGoodState E b‖ = 1 := by
  rw [← regGoodState_evoCircuit E b hb]
  exact norm_regGoodState E (evoCircuit E) b
    (by rw [regAmp_evoCircuit E b hb]; exact evoAmp_pos E b hb hb1)

/-- APP-4 (GSLW Thm 58, composed circuit). Fixed-point amplitude amplification (APP-1, `21` uses
of `evoCircuit E`/its adjoint, one more ancilla qubit) applied to the Route A circuit
`evoCircuit E` with initial state `|0⟩ ⊗ b` and good projector `|0⟩⟨0| ⊗ Π`, on
`Anc (Reg 12 ℋ)`. -/
noncomputable def evolutionAA (hb1 : ‖b‖ = 1) : L (Anc (Reg evoCheb.length ℋ)) :=
  regAACircuit E (evoCircuit_mem_unitary E) hb1

/-- APP-4. The composed circuit is unitary. -/
theorem evolutionAA_mem_unitary (hb1 : ‖b‖ = 1) :
    evolutionAA E b hb1 ∈ unitary (L (Anc (Reg evoCheb.length ℋ))) :=
  regAACircuit_mem_unitary E _ hb1

/-- APP-4 (exact). The good-subspace, ancilla-`0` block of the composed circuit maps `|0⟩ ⊗ b`
exactly onto `ψ_G = |0⟩ ⊗ p(A) b / ‖p(A) b‖`, scaled by `Re[P_Φ̃](a)`:
```
(⟨0| ⊗ (|0⟩⟨0| ⊗ Π)) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ = Re[P_Φ̃](a) ψ_G,    ψ₀ = |0⟩ ⊗ b.
```
-/
theorem evolutionAA_apply (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) =
      ((rePoly (qspPoly (sign21Phases.map (↑))).1).eval ((evoAmp E b : ℝ) : ℂ)) •
        evoGoodState E b := by
  have h := regAA_apply E (evoCircuit_mem_unitary E) hb1 hb
    (by rw [regAmp_evoCircuit E b hb]; exact evoAmp_pos E b hb hb1)
  rw [regAmp_evoCircuit E b hb, regGoodState_evoCircuit E b hb] at h
  exact h

/-- APP-4 (fixed-point property). The good-subspace output is `sign21Scale · ψ_G ≈ 0.8924 ψ_G` up
to `10⁻¹² + 0.0236`. -/
theorem evolutionAA_bound (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    ‖topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (sign21Scale : ℂ) • evoGoodState E b‖ ≤ sign21Eps + 0.0236 := by
  have h := regAA_bound E (evoCircuit_mem_unitary E) hb1 hb
    (by rw [regAmp_evoCircuit E b hb]; exact evoAmp_ge_015 E b hb hb1)
  rw [regGoodState_evoCircuit E b hb] at h
  exact h

/-- APP-4 (success amplitude). After one round of amplitude amplification on `|0⟩ ⊗ |0⟩ ⊗ b`, the
norm of the component with both ancilla registers in `0` and the system in `ran Π` is at least
`0.869` (success probability `≥ 0.869² ≈ 0.755`, against `a² ≈ 0.17` for `evoCircuit` alone);
conditioned on this outcome the register state is exactly `ψ_G`. -/
theorem evolutionAA_amplitude (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    0.869 ≤ ‖blockDiag (atZero E.P) 0 (evolutionAA E b hb1 (inl (inj 0 b)))‖ :=
  regAA_amplitude E (evoCircuit_mem_unitary E) hb1 hb
    (by rw [regAmp_evoCircuit E b hb]; exact evoAmp_ge_015 E b hb hb1)

/-! ### Closeness to the ideal evolved state -/

/-- APP-4. The subnormalisation cancels in the normalisation: `ψ_G = |0⟩ ⊗ p(A) b / ‖p(A) b‖`. -/
theorem evoGoodState_eq_normalize :
    evoGoodState E b =
      ((‖(inj 0 (aeval E.encoded (PolyQC.toPoly evoPoly) b) : Reg evoCheb.length ℋ)‖ : ℝ) : ℂ)⁻¹ •
        inj 0 (aeval E.encoded (PolyQC.toPoly evoPoly) b) := by
  rw [evoGoodState, evoAmp,
    ← norm_inj (0 : Fin evoCheb.length)
      (((evoL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded (PolyQC.toPoly evoPoly) b),
    map_smul, ← Complex.ofReal_inv evoL1]
  exact normalize_smul evoL1⁻¹ (inv_pos.mpr evoL1_pos) _

/-- APP-4. `p(A) b ≠ 0` (embedded), from `‖p(A) b‖ ≥ 1 − 2ε`. -/
theorem inj_aeval_evoPoly_ne_zero (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    (inj 0 (aeval E.encoded (PolyQC.toPoly evoPoly) b) : Reg evoCheb.length ℋ) ≠ 0 := by
  rw [← norm_pos_iff, norm_inj]
  have h := norm_aeval_evoPoly_ge E b hb
  rw [hb1, mul_one] at h
  linarith

/-- APP-4. `‖ψ_G − |0⟩ ⊗ e^{-2iA} b‖ ≤ 4ε`: the prepared state is within `4 · 10⁻⁶` of the ideal
evolved state (normalisation is `2`-Lipschitz, `norm_normalize_sub_le`). -/
theorem norm_evoGoodState_sub_idealEvo_le (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    ‖evoGoodState E b - inj 0 (idealEvo E b)‖ ≤ 4 * 0.000001 := by
  rw [evoGoodState_eq_normalize E b]
  have hw : ‖(inj 0 (idealEvo E b) : Reg evoCheb.length ℋ)‖ = 1 := by
    rw [norm_inj, norm_idealEvo E b hb, hb1]
  have h := norm_normalize_sub_le _ _ (inj_aeval_evoPoly_ne_zero E b hb hb1) hw
  rw [← map_sub,
    norm_inj (0 : Fin evoCheb.length) (aeval E.encoded (PolyQC.toPoly evoPoly) b - idealEvo E b)]
    at h
  have h2 := norm_aeval_evoPoly_sub_idealEvo_le E b hb
  rw [hb1, mul_one] at h2
  linarith

theorem norm_sign21Scale : ‖(sign21Scale : ℂ)‖ = (sign21Scale : ℝ) := by
  rw [Complex.norm_ratCast, abs_of_nonneg]
  rw [sign21Scale]
  norm_num

/-- APP-4 (headline; GSLW Thm 58 for `t = 2`). After one round of fixed-point amplitude
amplification, the good-subspace output of the composed circuit on `|0⟩ ⊗ |0⟩ ⊗ b` is the ideal
evolved state `|0⟩ ⊗ e^{-2iA} b`, scaled by `c = sign21Scale ≈ 0.8924`, up to
`10⁻¹² + 0.0236 + 4εc ≈ 0.0236`:
```
‖(⟨0| ⊗ (|0⟩⟨0| ⊗ Π)) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ − c · |0⟩ ⊗ e^{-2iA} b‖ ≤ 10⁻¹² + 0.0236 + c · 4ε.
```
-/
theorem evolutionAA_output (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    ‖topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (sign21Scale : ℂ) • inj 0 (idealEvo E b)‖ ≤
      sign21Eps + 0.0236 + sign21Scale * (4 * 0.000001) := by
  have h1 := evolutionAA_bound E b hb hb1
  have h2 := norm_evoGoodState_sub_idealEvo_le E b hb hb1
  have hc0 : (0 : ℝ) ≤ sign21Scale := by
    rw [sign21Scale]
    norm_num
  calc ‖topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
          (inj 0 b) - (sign21Scale : ℂ) • inj 0 (idealEvo E b)‖
      = ‖(topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 *
            blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) - (sign21Scale : ℂ) • evoGoodState E b) +
          (sign21Scale : ℂ) • (evoGoodState E b - inj 0 (idealEvo E b))‖ := by
        rw [smul_sub, sub_add_sub_cancel]
    _ ≤ ‖topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 *
            blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) - (sign21Scale : ℂ) • evoGoodState E b‖ +
          ‖(sign21Scale : ℂ) • (evoGoodState E b - inj 0 (idealEvo E b))‖ := norm_add_le _ _
    _ = ‖topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 *
            blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) - (sign21Scale : ℂ) • evoGoodState E b‖ +
          sign21Scale * ‖evoGoodState E b - inj 0 (idealEvo E b)‖ := by
        rw [norm_smul, norm_sign21Scale]
    _ ≤ sign21Eps + 0.0236 + sign21Scale * (4 * 0.000001) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 hc0)

/-- APP-4. The headline with a clean constant: `‖output − c · |0⟩ ⊗ e^{-2iA} b‖ ≤ 0.0237`. -/
theorem evolutionAA_output_le (hb : E.P b = b) (hb1 : ‖b‖ = 1) :
    ‖topLeft (blockDiag (atZero E.P) 0 * evolutionAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (sign21Scale : ℂ) • inj 0 (idealEvo E b)‖ ≤ 0.0237 :=
  (evolutionAA_output E b hb hb1).trans (by rw [sign21Eps, sign21Scale]; norm_num)

end Setting

/-! ### Resources -/

/-- APP-4. The oracle query count of the composed algorithm: the AA circuit makes
`oracleCount (compileQsvtReal Φ̃) = 21` calls to `evoCircuit E`/its adjoint, each of which makes
`routeA_queries 12 = 66` queries to `U`/`U†`. (A derived count: `evoCircuit` is an LCU on a
`12`-dimensional register without a `Circuit` gate-list denotation yet, so this is not a
`Circuit.oracleCount` theorem about the composed circuit.) -/
def evolutionAA_queries : ℕ :=
  Circuit.oracleCount (Circuit.compileQsvtReal (sign21Phases.map (↑))) *
    routeA_queries evoCheb.length

/-- APP-4. `21 · 66 = 1386` oracle queries. -/
theorem evolutionAA_queries_eq : evolutionAA_queries = 1386 := by
  rw [evolutionAA_queries, aaCircuit_oracleCount, evoCircuit_queries]

end QSVT.Examples
