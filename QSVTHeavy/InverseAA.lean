/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVTHeavy.FixedPointAAD01
import QSVT.Examples.Inverse

/-!
# APP-3 (completion): the matrix-inversion block with fixed-point amplitude amplification

GSLW Thm 41 (quantum linear systems by QSVT) prepares a state proportional to `A⁻¹ b` from a
block encoding of `A` in two steps: a polynomial approximation of `1/(κx)` implemented by QSVT,
which produces the subnormalised state `p(A) b / ‖c‖₁ ≈ A⁻¹ b / (κ ‖c‖₁)` in the ancilla-`0`
branch, followed by fixed-point amplitude amplification (GSLW Thm 27) with a constant number of
rounds, since the initial amplitude is at least `≈ 1/(κ ‖c‖₁)`, a constant. This module composes
the two certified building blocks of this library, for the Hermitian/eigenvector case with
`κ = 4`:

* the Route A circuit `invCircuit E` of APP-3 (`QSVT.Examples.Inverse`), which implements
  `p(A)/‖c‖₁` exactly for the degree-29 certified polynomial `p = invPoly ≈ (3/4)/(4x)` on
  `|x| ∈ [1/4, 1]` (`‖p(x) − (3/4)/(4x)‖ ≤ ε`, `ε = invEps = 7.5 · 10⁻⁴`, `‖c‖₁ = invL1 ≈ 1.6635`,
  `435` oracle queries);
* the gap-`0.1` fixed-point amplitude amplification `aaCircuitD01` of the heavy library
  (`QSVTHeavy.FixedPointAAD01`, degree `35`, plateau `c = signD01Scale = 0.9875`, ripple `0.012`),
  through the register-to-AA bridge of APP-COMPOSE (`QSVT.Examples.Compose`). The degree-21
  polynomial of APP-1 (gap `0.15`) is *not* enough here: the initial amplitude is only
  `≈ 0.112 < 0.15`.

## The spectral support hypothesis

The polynomial `invPoly` is certified only on `|x| ∈ [1/4, 1]` (below the gap `1/κ` it is merely
bounded by `1`), so all statements assume that `b` is supported on the invertible part of the
spectrum: `hsupp : ∀ i, ⟪ψᵢ, b⟫ ≠ 0 → 1/4 ≤ |ςᵢ|` for the eigenbasis `ψᵢ` of `A|_{ran Π}` with
eigenvalues `ςᵢ` (SVT-3). This is GSLW's assumption that `A` has no singular values in
`(0, 1/κ)` on the relevant subspace. The lower bounds then only use the eigenvalues in the
support of `b` (`norm_aeval_apply_ge_of_support`, and the new `norm_funCalc_le_of_support`).

## Statements (for `E : HermitianEncoding ℋ`, `b ∈ ran Π`, `‖b‖ = 1`, `hsupp`)

* The initial good amplitude is `a = invAmp E b = ‖p(A) b‖ / ‖c‖₁`, with the lower bound
  `(invScale/4 − ε)/‖c‖₁ ≤ a` (`invAmp_ge`: on the support, `‖p(ς)‖ ≥ |invScale/(4ς)| − ε ≥
  invScale/4 − ε` since `|ς| ≤ 1`), numerically `(0.1875 − 0.00075)/1.6636 ≈ 0.112`, hence
  `a ≥ 0.1` (`invAmp_ge_01`), the gap of the certified sign polynomial `signD01`.
* The composed circuit `inverseAA E b hb1 : L (Anc (Reg 30 ℋ))` (one ancilla qubit for the AA
  step, the `30`-dimensional Route A register, the system) satisfies the exact statement
  `inverseAA_apply` (the good-subspace output is `Re[P_Φ̃](a) ψ_G` with
  `ψ_G = invGoodState E b = |0⟩ ⊗ p(A) b / ‖p(A) b‖`), the fixed-point bound `inverseAA_bound`
  (`‖output − c ψ_G‖ ≤ 10⁻¹² + 0.012`, `c = signD01Scale = 0.9875`) and the success amplitude
  `inverseAA_amplitude`: `0.975 ≤ ‖(|0⟩⟨0| ⊗ |0⟩⟨0| ⊗ Π) W (|0⟩ ⊗ |0⟩ ⊗ b)‖`, so the probability
  of measuring both ancilla registers in `0` is at least `0.975² ≈ 0.95` (against
  `a² ≈ 0.0127` without amplification), and the post-measurement state is exactly `ψ_G`.
* The ideal (unnormalised) solution is `idealInv E b = ∑ᵢ ⟪ψᵢ, b⟫ (invScale/(4 ςᵢ)) ψᵢ`, the
  spectral functional calculus of `x ↦ invScale/(4x)` (APP-COMPOSE `funCalc`); on the support
  this is `(invScale/4) · A⁻¹ b`: `A (idealInv E b) = (invScale/4) b` (`encoded_idealInv`), so
  its normalisation `idealInvState E b = idealInv E b / ‖idealInv E b‖` is the normalised solution
  of the linear system `A x = b` (GSLW's `A⁻¹ b / ‖A⁻¹ b‖`; off the support the coefficients
  `⟪ψᵢ, b⟫` vanish, so the value of `invScale/(4x)` there is irrelevant). The polynomial
  certificate transfers to the operators on the support: `‖p(A) b − idealInv E b‖ ≤ ε`
  (`norm_aeval_invPoly_sub_idealInv_le`), `‖idealInv E b‖ ≥ invScale/4` (`norm_idealInv_ge`), and
  since normalisation is Lipschitz, `‖ψ_G − |0⟩ ⊗ idealInvState E b‖ ≤ 2ε/(invScale/4) = 0.008`
  (`norm_invGoodState_sub_idealInvState_le`).
* **Headline** `inverseAA_output`: after one round of amplitude amplification the good-subspace
  component of the output is the normalised solution, scaled by `c = 0.9875`, up to
  `‖output − c · |0⟩ ⊗ A⁻¹b/‖A⁻¹b‖‖ ≤ 10⁻¹² + 0.012 + c · 2ε/(invScale/4) ≤ 0.02`
  (`inverseAA_output_le`).
* Resources: the AA circuit uses `invCircuit E`/its adjoint `35` times
  (`aaCircuitD01_oracleCount`), each using `435` queries to `U`/`U†` (`invCircuit_queries`), so
  the composed algorithm makes `35 · 435 = 15225` oracle queries (`inverseAA_queries_eq`); a
  derived count, as for APP-4 (`invCircuit` is an LCU on a `30`-dimensional register without a
  `Circuit` gate-list denotation).

## Relation to GSLW Thm 41

For a block encoding whose singular values lie in `[1/κ, 1]`, GSLW implement a block encoding of
`A⁻¹/(2κ)` (up to `ε`) with `O(κ log(1/ε))` queries and then amplify the state `A⁻¹ b/(2κ)`
(amplitude `≥ 1/(2κ)`) with `O(κ)` rounds of fixed-point amplitude amplification; the result is
`A⁻¹ b / ‖A⁻¹ b‖` to precision `ε`. Here `κ = 4` (so one round of a gap-`0.1` sign polynomial
suffices), the polynomial has the forced constant
`invScale = 3/4` in front of `1/(κx)` (an odd polynomial bounded by `1` cannot approximate
`1/(κx)` itself to `10⁻³` below degree `Ω(10³)`, see `QSVT.Certificate.InvExample`), and the sign
polynomial of the amplification has plateau `0.9875` rather than `1 − ε`; this is why the output is
`≈ 0.9875 · (normalised solution)` with error `≈ 0.02` rather than `≈ 1 · (normalised solution)`
with error `ε`. The *direction* of the good-subspace output is exact (`inverseAA_apply`):
conditioned on both ancillas measuring `0`, the register is in `ψ_G = |0⟩ ⊗ p(A) b / ‖p(A) b‖`,
within `0.008` of `|0⟩ ⊗ A⁻¹ b / ‖A⁻¹ b‖`.

Every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`QSVTHeavy.InverseAATest`).

## Mathlib API used

`div_le_div_of_nonneg_left`, `div_le_div₀`, `le_abs`, `abs_le`, `abs_div`, `abs_mul`,
`norm_le_norm_add_norm_sub`, `le_div_iff₀`, `smul_ne_zero`, `Complex.ofReal_inv`,
`Complex.norm_real`, `Real.norm_eq_abs`, `Finset.smul_sum`, `map_sum`, `field_simp`.
-/

namespace QSVT.Examples

open QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Encoding QSVT.IR QSVT.Pipeline QuantumState
open Polynomial

universe u

/-! ### Normalisation between two non-unit vectors -/

section Normalize

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- APP-3 (APP-COMPOSE companion). Normalisation is Lipschitz between two nonzero vectors:
`‖v/‖v‖ − w/‖w‖‖ ≤ 2 ‖v − w‖ / ‖w‖` (from `norm_normalize_sub_le` applied to `v/‖w‖` and the
unit vector `w/‖w‖`). -/
theorem norm_normalize_sub_normalize_le (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    ‖((‖v‖ : ℝ) : ℂ)⁻¹ • v - ((‖w‖ : ℝ) : ℂ)⁻¹ • w‖ ≤ 2 * ‖v - w‖ / ‖w‖ := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hc : 0 < ‖w‖⁻¹ := inv_pos.mpr hw'
  have h1 : ((‖v‖ : ℝ) : ℂ)⁻¹ • v =
      ((‖((‖w‖⁻¹ : ℝ) : ℂ) • v‖ : ℝ) : ℂ)⁻¹ • (((‖w‖⁻¹ : ℝ) : ℂ) • v) :=
    (normalize_smul ‖w‖⁻¹ hc v).symm
  have hv' : ((‖w‖⁻¹ : ℝ) : ℂ) • v ≠ 0 :=
    smul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') hv
  have h2 := norm_normalize_sub_le (((‖w‖⁻¹ : ℝ) : ℂ) • v) (((‖w‖ : ℝ) : ℂ)⁻¹ • w) hv'
    (norm_normalize w hw)
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  rw [← Complex.ofReal_inv, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  ring

end Normalize

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The functional calculus on the support -/

section FunCalcSupport

variable (E : HermitianEncoding ℋ)

/-- APP-3 (APP-COMPOSE companion). `‖f(A) x‖ ≤ M ‖x‖` for `x ∈ ran Π` when `‖f(ςᵢ)‖ ≤ M` for
every eigenvalue `ςᵢ` in the support of `x` (`⟪ψᵢ, x⟫ ≠ 0`). -/
theorem norm_funCalc_le_of_support (f : ℝ → ℂ) (M : ℝ) (hM0 : 0 ≤ M) (x : ℋ) (hx : E.P x = x)
    (hM : ∀ i, inner ℂ (eigenVec E i) x ≠ 0 → ‖f (eigenValue E i)‖ ≤ M) :
    ‖funCalc E f x‖ ≤ M * ‖x‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg hM0 (norm_nonneg x))
  rw [norm_funCalc_sq, mul_pow, norm_sq_eq_sum_inner_eigenVec E x hx, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm (M ^ 2)]
  by_cases hi : inner ℂ (eigenVec E i) x = 0
  · rw [hi, norm_zero]
    simp
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hM i hi) 2) (sq_nonneg _)

/-- APP-3 (APP-COMPOSE companion). `‖p(A) x − f(A) x‖ ≤ η ‖x‖` for `x ∈ ran Π` when
`‖p(ςᵢ) − f(ςᵢ)‖ ≤ η` for every eigenvalue in the support of `x`. -/
theorem norm_aeval_sub_funCalc_le_of_support (p : ℂ[X]) (f : ℝ → ℂ) (η : ℝ) (hη0 : 0 ≤ η)
    (x : ℋ) (hx : E.P x = x)
    (hη : ∀ i, inner ℂ (eigenVec E i) x ≠ 0 →
      ‖p.eval (eigenValue E i : ℂ) - f (eigenValue E i)‖ ≤ η) :
    ‖aeval E.encoded p x - funCalc E f x‖ ≤ η * ‖x‖ := by
  rw [aeval_eq_funCalc E p x hx, funCalc_sub]
  exact norm_funCalc_le_of_support E _ η hη0 x hx fun i hi => hη i hi

end FunCalcSupport

/-! ### The polynomial on the invertible part of the spectrum -/

/-- APP-3. `0 ≤ invScale`. -/
theorem invScale_nonneg : (0 : ℝ) ≤ invScale := by
  rw [invScale]
  norm_num

/-- APP-3. `0 < invScale/4` (`= 0.1875`). -/
theorem invScale_div_four_pos : (0 : ℝ) < (invScale : ℝ) / 4 := by
  rw [invScale]
  norm_num

/-- APP-3. `0 < invScale/4 − ε` (`= 0.18675`). -/
theorem invScale_div_four_sub_invEps_pos : (0 : ℝ) < (invScale : ℝ) / 4 - invEps := by
  rw [invScale, invEps]
  norm_num

/-- APP-3. The target `invScale/(4x)` has modulus at least `invScale/4` for `1/4 ≤ |x| ≤ 1`. -/
theorem invScale_div_four_le_norm_target {x : ℝ} (h1 : 1 / 4 ≤ |x|) (h2 : |x| ≤ 1) :
    (invScale : ℝ) / 4 ≤ ‖(((invScale : ℝ) / (4 * x) : ℝ) : ℂ)‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg invScale_nonneg, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact div_le_div_of_nonneg_left invScale_nonneg (by linarith) (by linarith)

/-- APP-3. The certificate `‖p(x) − invScale/(4x)‖ ≤ ε` on both parts `|x| ∈ [1/4, 1]` of the
invertible spectrum (`norm_eval_invPoly_sub_inv_le` and its mirror). -/
theorem norm_eval_invPoly_sub_inv_le_of_abs {x : ℝ} (h1 : 1 / 4 ≤ |x|)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖invPoly.toPoly.eval (x : ℂ) - (((invScale : ℝ) / (4 * x) : ℝ) : ℂ)‖ ≤ invEps := by
  rcases le_abs.mp h1 with h | h
  · exact norm_eval_invPoly_sub_inv_le x ⟨h, hx.2⟩
  · exact norm_eval_invPoly_sub_inv_le_neg x ⟨hx.1, by linarith⟩

/-- APP-3. `invScale/4 − ε ≤ ‖p(x)‖` for `1/4 ≤ |x| ≤ 1`: the polynomial is bounded below on
the invertible spectrum (`‖p(x)‖ ≥ |invScale/(4x)| − ε ≥ invScale/4 − ε`). -/
theorem norm_eval_invPoly_ge_of_abs {x : ℝ} (h1 : 1 / 4 ≤ |x|) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (invScale : ℝ) / 4 - invEps ≤ ‖invPoly.toPoly.eval (x : ℂ)‖ := by
  have h2 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have hc := norm_eval_invPoly_sub_inv_le_of_abs h1 hx
  have hl := invScale_div_four_le_norm_target h1 h2
  have h3 := norm_le_norm_add_norm_sub (invPoly.toPoly.eval (x : ℂ))
    (((invScale : ℝ) / (4 * x) : ℝ) : ℂ)
  linarith

section Setting

variable (E : HermitianEncoding ℋ) (b : ℋ)

/-! ### The ideal solution -/

/-- APP-3. The ideal (unnormalised) solution `idealInv E b = ∑ᵢ ⟪ψᵢ, b⟫ (invScale/(4 ςᵢ)) ψᵢ`,
the spectral functional calculus of `x ↦ invScale/(4x)` through the eigenbasis of `A|_{ran Π}`
(APP-COMPOSE `funCalc`). On the support hypothesis this is `(invScale/4) · A⁻¹ b`
(`encoded_idealInv`); off the support the coefficients `⟪ψᵢ, b⟫` vanish. -/
noncomputable def idealInv : ℋ := funCalc E (fun t => (((invScale : ℝ) / (4 * t) : ℝ) : ℂ)) b

theorem idealInv_eq_sum :
    idealInv E b =
      ∑ i, (inner ℂ (eigenVec E i) b * (((invScale : ℝ) / (4 * eigenValue E i) : ℝ) : ℂ)) •
        eigenVec E i :=
  rfl

/-- APP-3 (`idealInv E b ∝ A⁻¹ b`). On the support, `A (idealInv E b) = (invScale/4) b`: the
ideal solution solves the linear system `A x = (invScale/4) b`. -/
theorem encoded_idealInv (hb : E.P b = b)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    E.encoded (idealInv E b) = (((invScale : ℝ) / 4 : ℝ) : ℂ) • b := by
  rw [idealInv_eq_sum, map_sum]
  conv_rhs => rw [sum_repr_eigenVec E b hb, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, encoded_eigenVec, smul_smul, smul_smul]
  by_cases hi : inner ℂ (eigenVec E i) b = 0
  · rw [hi]
    simp
  · congr 1
    have hς : eigenValue E i ≠ 0 := by
      intro h0
      have := hsupp i hi
      rw [h0, abs_zero] at this
      norm_num at this
    have hς' : (eigenValue E i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hς
    push_cast
    field_simp

/-- APP-3. `(invScale/4) ‖b‖ ≤ ‖idealInv E b‖` on the support (Parseval and
`|invScale/(4ς)| ≥ invScale/4` for `|ς| ≤ 1`). -/
theorem norm_idealInv_ge (hb : E.P b = b)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    (invScale : ℝ) / 4 * ‖b‖ ≤ ‖idealInv E b‖ :=
  norm_funCalc_ge_of_support E _ _ b hb fun i hi =>
    invScale_div_four_le_norm_target (hsupp i hi)
      (abs_le.mpr ⟨(eigenValue_mem_Icc E i).1, (eigenValue_mem_Icc E i).2⟩)

/-- APP-3. `idealInv E b ≠ 0` for a unit `b ∈ ran Π` on the support. -/
theorem idealInv_ne_zero (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    idealInv E b ≠ 0 := by
  rw [← norm_pos_iff]
  have h := norm_idealInv_ge E b hb hsupp
  rw [hb1, mul_one] at h
  linarith [invScale_div_four_pos]

/-- APP-3. The normalised ideal solution `idealInvState E b = idealInv E b / ‖idealInv E b‖`,
i.e. `A⁻¹ b / ‖A⁻¹ b‖` on the support (GSLW Thm 41's target state). -/
noncomputable def idealInvState : ℋ := ((‖idealInv E b‖ : ℝ) : ℂ)⁻¹ • idealInv E b

/-- APP-3. `‖idealInvState E b‖ = 1` for a unit `b ∈ ran Π` on the support. -/
theorem norm_idealInvState (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ‖idealInvState E b‖ = 1 :=
  norm_normalize _ (idealInv_ne_zero E b hb hb1 hsupp)

/-- APP-3 (certificate transferred to the operators). `‖p(A) b − idealInv E b‖ ≤ ε ‖b‖` for
`b ∈ ran Π` supported on the invertible spectrum. -/
theorem norm_aeval_invPoly_sub_idealInv_le (hb : E.P b = b)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ‖aeval E.encoded invPoly.toPoly b - idealInv E b‖ ≤ invEps * ‖b‖ :=
  norm_aeval_sub_funCalc_le_of_support E _ _ _ invEps_nonneg b hb fun i hi =>
    norm_eval_invPoly_sub_inv_le_of_abs (hsupp i hi) (eigenValue_mem_Icc E i)

/-- APP-3. `(invScale/4 − ε) ‖b‖ ≤ ‖p(A) b‖` for `b ∈ ran Π` supported on the invertible
spectrum (`norm_aeval_apply_ge_of_support`). -/
theorem norm_aeval_invPoly_ge (hb : E.P b = b)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ((invScale : ℝ) / 4 - invEps) * ‖b‖ ≤ ‖aeval E.encoded invPoly.toPoly b‖ :=
  norm_aeval_apply_ge_of_support E _ _ b hb fun i hi =>
    norm_eval_invPoly_ge_of_abs (hsupp i hi) (eigenValue_mem_Icc E i)

/-! ### The initial good amplitude -/

/-- APP-3. The good vector of the Route A circuit on `b ∈ ran Π` is `‖c‖₁⁻¹ p(A) b`
(`invCircuit_topLeft`). -/
theorem regGood_invCircuit (hb : E.P b = b) :
    regGood E (invCircuit E) b = ((invL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded invPoly.toPoly b := by
  rw [regGood, invCircuit_topLeft, LinearMap.smul_apply, Module.End.mul_apply, hb]

/-- APP-3. The initial good amplitude `a = ‖‖c‖₁⁻¹ p(A) b‖ = ‖p(A) b‖ / ‖c‖₁ ≈ 0.112`
(`= regAmp E (invCircuit E) b` for `b ∈ ran Π`, `regAmp_invCircuit`). -/
noncomputable def invAmp : ℝ := ‖((invL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded invPoly.toPoly b‖

theorem regAmp_invCircuit (hb : E.P b = b) : regAmp E (invCircuit E) b = invAmp E b := by
  rw [regAmp, regGood_invCircuit E b hb, invAmp]

theorem invAmp_eq : invAmp E b = invL1⁻¹ * ‖aeval E.encoded invPoly.toPoly b‖ := by
  rw [invAmp, norm_smul, norm_inv_invL1]

/-- APP-3. `(invScale/4 − ε)/‖c‖₁ ≤ a` for a unit `b ∈ ran Π` supported on the invertible
spectrum. -/
theorem invAmp_ge (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ((invScale : ℝ) / 4 - invEps) / invL1 ≤ invAmp E b := by
  rw [invAmp_eq, div_eq_inv_mul]
  have h := norm_aeval_invPoly_ge E b hb hsupp
  rw [hb1, mul_one] at h
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr invL1_pos.le)

/-- APP-3. `0.1 ≤ a`: the initial amplitude is above the gap of the certified sign polynomial
`signD01` (`(invScale/4 − ε)/‖c‖₁ ≥ 0.18675/1.6636 ≈ 0.112`). -/
theorem invAmp_ge_01 (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    0.1 ≤ invAmp E b := by
  refine le_trans ?_ (invAmp_ge E b hb hb1 hsupp)
  rw [le_div_iff₀ invL1_pos]
  have h1 : (0.1 : ℝ) * 1.6636 ≤ (invScale : ℝ) / 4 - invEps := by
    rw [invScale, invEps]
    norm_num
  have h2 := invL1_mem_Icc.2
  linarith

theorem invAmp_pos (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    0 < invAmp E b := by
  linarith [invAmp_ge_01 E b hb hb1 hsupp]

/-! ### The amplitude-amplification instance -/

/-- APP-3. The normalised good state `ψ_G = a⁻¹ (|0⟩ ⊗ ‖c‖₁⁻¹ p(A) b)` on the Route A register
(GSLW Thm 27's `Π U ψ₀ / ‖Π U ψ₀‖`). -/
noncomputable def invGoodState : Reg invCheb.length ℋ :=
  ((invAmp E b : ℝ) : ℂ)⁻¹ • inj 0 (((invL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded invPoly.toPoly b)

theorem regGoodState_invCircuit (hb : E.P b = b) :
    regGoodState E (invCircuit E) b = invGoodState E b := by
  rw [regGoodState, regAmp_invCircuit E b hb, regGood_invCircuit E b hb, invGoodState]

/-- APP-3. The hypotheses of APP-1 for `U = invCircuit E`, `G = |0⟩⟨0| ⊗ Π`, `ψ₀ = |0⟩ ⊗ b`:
`G (U ψ₀) = a ψ_G`. -/
theorem atZero_P_invCircuit_apply (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    atZero E.P (invCircuit E (inj 0 b)) = ((invAmp E b : ℝ) : ℂ) • invGoodState E b := by
  rw [← regAmp_invCircuit E b hb, ← regGoodState_invCircuit E b hb]
  exact atZero_P_apply_eq_smul E (invCircuit E) b hb
    (by rw [regAmp_invCircuit E b hb]; exact invAmp_pos E b hb hb1 hsupp)

/-- APP-3. `‖ψ_G‖ = 1`. -/
theorem norm_invGoodState (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ‖invGoodState E b‖ = 1 := by
  rw [← regGoodState_invCircuit E b hb]
  exact norm_regGoodState E (invCircuit E) b
    (by rw [regAmp_invCircuit E b hb]; exact invAmp_pos E b hb hb1 hsupp)

/-- APP-3 (GSLW Thm 41, composed circuit). Fixed-point amplitude amplification with gap `0.1`
(`35` uses of `invCircuit E`/its adjoint, one more ancilla qubit) applied to the Route A circuit
`invCircuit E` with initial state `|0⟩ ⊗ b` and good projector `|0⟩⟨0| ⊗ Π`, on
`Anc (Reg 30 ℋ)`. -/
noncomputable def inverseAA (hb1 : ‖b‖ = 1) : L (Anc (Reg invCheb.length ℋ)) :=
  regAAD01Circuit E (invCircuit_mem_unitary E) hb1

/-- APP-3. The composed circuit is unitary. -/
theorem inverseAA_mem_unitary (hb1 : ‖b‖ = 1) :
    inverseAA E b hb1 ∈ unitary (L (Anc (Reg invCheb.length ℋ))) :=
  regAAD01Circuit_mem_unitary E _ hb1

/-- APP-3 (exact). The good-subspace, ancilla-`0` block of the composed circuit maps `|0⟩ ⊗ b`
exactly onto `ψ_G = |0⟩ ⊗ p(A) b / ‖p(A) b‖`, scaled by `Re[P_Φ̃](a)`:
```
(⟨0| ⊗ (|0⟩⟨0| ⊗ Π)) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ = Re[P_Φ̃](a) ψ_G,    ψ₀ = |0⟩ ⊗ b.
```
-/
theorem inverseAA_apply (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) =
      ((rePoly (qspPoly (signD01Phases.map (↑))).1).eval ((invAmp E b : ℝ) : ℂ)) •
        invGoodState E b := by
  have h := regAAD01_apply E (invCircuit_mem_unitary E) hb1 hb
    (by rw [regAmp_invCircuit E b hb]; exact invAmp_pos E b hb hb1 hsupp)
  rw [regAmp_invCircuit E b hb, regGoodState_invCircuit E b hb] at h
  exact h

/-- APP-3 (fixed-point property). The good-subspace output is `signD01Scale · ψ_G = 0.9875 ψ_G`
up to `10⁻¹² + 0.012`. -/
theorem inverseAA_bound (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ‖topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (signD01Scale : ℂ) • invGoodState E b‖ ≤ signD01Eps + 0.012 := by
  have h := regAAD01_bound E (invCircuit_mem_unitary E) hb1 hb
    (by rw [regAmp_invCircuit E b hb]; exact invAmp_ge_01 E b hb hb1 hsupp)
  rw [regGoodState_invCircuit E b hb] at h
  exact h

/-- APP-3 (success amplitude). After one round of amplitude amplification on `|0⟩ ⊗ |0⟩ ⊗ b`,
the norm of the component with both ancilla registers in `0` and the system in `ran Π` is at
least `0.975` (success probability `≥ 0.975² ≈ 0.95`, against `a² ≈ 0.0127` for `invCircuit`
alone); conditioned on this outcome the register state is exactly `ψ_G`. -/
theorem inverseAA_amplitude (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    0.975 ≤ ‖blockDiag (atZero E.P) 0 (inverseAA E b hb1 (inl (inj 0 b)))‖ :=
  regAAD01_amplitude E (invCircuit_mem_unitary E) hb1 hb
    (by rw [regAmp_invCircuit E b hb]; exact invAmp_ge_01 E b hb hb1 hsupp)

/-! ### Closeness to the normalised solution -/

/-- APP-3. The subnormalisation cancels in the normalisation: `ψ_G = |0⟩ ⊗ p(A) b / ‖p(A) b‖`. -/
theorem invGoodState_eq_normalize :
    invGoodState E b =
      ((‖(inj 0 (aeval E.encoded invPoly.toPoly b) : Reg invCheb.length ℋ)‖ : ℝ) : ℂ)⁻¹ •
        inj 0 (aeval E.encoded invPoly.toPoly b) := by
  rw [invGoodState, invAmp,
    ← norm_inj (0 : Fin invCheb.length) (((invL1 : ℝ) : ℂ)⁻¹ • aeval E.encoded invPoly.toPoly b),
    map_smul, ← Complex.ofReal_inv invL1]
  exact normalize_smul invL1⁻¹ (inv_pos.mpr invL1_pos) _

/-- APP-3. `p(A) b ≠ 0` (embedded), from `‖p(A) b‖ ≥ invScale/4 − ε`. -/
theorem inj_aeval_invPoly_ne_zero (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    (inj 0 (aeval E.encoded invPoly.toPoly b) : Reg invCheb.length ℋ) ≠ 0 := by
  rw [← norm_pos_iff, norm_inj]
  have h := norm_aeval_invPoly_ge E b hb hsupp
  rw [hb1, mul_one] at h
  linarith [invScale_div_four_sub_invEps_pos]

/-- APP-3. `‖ψ_G − |0⟩ ⊗ idealInvState E b‖ ≤ 2ε/(invScale/4) = 0.008`: the prepared state is
within `0.008` of the normalised solution (normalisation is Lipschitz,
`norm_normalize_sub_normalize_le`, with `‖p(A) b − idealInv E b‖ ≤ ε` and
`‖idealInv E b‖ ≥ invScale/4`). -/
theorem norm_invGoodState_sub_idealInvState_le (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ‖invGoodState E b - inj 0 (idealInvState E b)‖ ≤ 2 * invEps / ((invScale : ℝ) / 4) := by
  rw [invGoodState_eq_normalize E b, idealInvState, map_smul,
    ← norm_inj (0 : Fin invCheb.length) (idealInv E b)]
  have hw : (inj 0 (idealInv E b) : Reg invCheb.length ℋ) ≠ 0 := by
    rw [← norm_pos_iff, norm_inj]
    exact norm_pos_iff.mpr (idealInv_ne_zero E b hb hb1 hsupp)
  refine (norm_normalize_sub_normalize_le _ _ (inj_aeval_invPoly_ne_zero E b hb hb1 hsupp)
    hw).trans ?_
  rw [← map_sub, norm_inj, norm_inj]
  have h1 := norm_aeval_invPoly_sub_idealInv_le E b hb hsupp
  have h2 := norm_idealInv_ge E b hb hsupp
  rw [hb1, mul_one] at h1 h2
  exact div_le_div₀ (by linarith [invEps_nonneg]) (by linarith) invScale_div_four_pos h2

/-- APP-3 (headline; GSLW Thm 41 for `κ = 4`). After one round of fixed-point amplitude
amplification, the good-subspace output of the composed circuit on `|0⟩ ⊗ |0⟩ ⊗ b` is the
normalised solution `|0⟩ ⊗ A⁻¹ b / ‖A⁻¹ b‖` of the linear system, scaled by
`c = signD01Scale = 0.9875`, up to `10⁻¹² + 0.012 + c · 2ε/(invScale/4) ≈ 0.0199`:
```
‖(⟨0| ⊗ (|0⟩⟨0| ⊗ Π)) W (|0⟩ ⊗ |ψ₀⟩⟨ψ₀|) ψ₀ − c · |0⟩ ⊗ idealInvState E b‖
    ≤ 10⁻¹² + 0.012 + c · 2ε/(invScale/4).
```
-/
theorem inverseAA_output (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ‖topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (signD01Scale : ℂ) • inj 0 (idealInvState E b)‖ ≤
      signD01Eps + 0.012 + signD01Scale * (2 * invEps / ((invScale : ℝ) / 4)) := by
  have h1 := inverseAA_bound E b hb hb1 hsupp
  have h2 := norm_invGoodState_sub_idealInvState_le E b hb hb1 hsupp
  calc ‖topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
          (inj 0 b) - (signD01Scale : ℂ) • inj 0 (idealInvState E b)‖
      = ‖(topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 *
            blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) - (signD01Scale : ℂ) • invGoodState E b) +
          (signD01Scale : ℂ) • (invGoodState E b - inj 0 (idealInvState E b))‖ := by
        rw [smul_sub, sub_add_sub_cancel]
    _ ≤ ‖topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 *
            blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) - (signD01Scale : ℂ) • invGoodState E b‖ +
          ‖(signD01Scale : ℂ) • (invGoodState E b - inj 0 (idealInvState E b))‖ :=
        norm_add_le _ _
    _ = ‖topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 *
            blockDiag (rankOne (inj 0 b)) 0) (inj 0 b) - (signD01Scale : ℂ) • invGoodState E b‖ +
          signD01Scale * ‖invGoodState E b - inj 0 (idealInvState E b)‖ := by
        rw [norm_smul, norm_signD01Scale]
    _ ≤ signD01Eps + 0.012 + signD01Scale * (2 * invEps / ((invScale : ℝ) / 4)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 signD01Scale_nonneg)

/-- APP-3. The headline with a clean constant: `‖output − c · |0⟩ ⊗ A⁻¹b/‖A⁻¹b‖‖ ≤ 0.02`
(`10⁻¹² + 0.012 + 0.9875 · 0.008 = 0.0199 + 10⁻¹²`). -/
theorem inverseAA_output_le (hb : E.P b = b) (hb1 : ‖b‖ = 1)
    (hsupp : ∀ i, inner ℂ (eigenVec E i) b ≠ 0 → 1 / 4 ≤ |eigenValue E i|) :
    ‖topLeft (blockDiag (atZero E.P) 0 * inverseAA E b hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (signD01Scale : ℂ) • inj 0 (idealInvState E b)‖ ≤ 0.02 :=
  (inverseAA_output E b hb hb1 hsupp).trans
    (by rw [signD01Eps, signD01Scale, invEps, invScale]; norm_num)

end Setting

/-! ### Resources -/

/-- APP-3. The oracle query count of the composed algorithm: the AA circuit makes
`oracleCount (compileQsvtReal Φ̃) = 35` calls to `invCircuit E`/its adjoint, each of which makes
`routeA_queries 30 = 435` queries to `U`/`U†`. (A derived count: `invCircuit` is an LCU on a
`30`-dimensional register without a `Circuit` gate-list denotation yet, so this is not a
`Circuit.oracleCount` theorem about the composed circuit.) -/
def inverseAA_queries : ℕ :=
  Circuit.oracleCount (Circuit.compileQsvtReal (signD01Phases.map (↑))) *
    routeA_queries invCheb.length

/-- APP-3. `35 · 435 = 15225` oracle queries. -/
theorem inverseAA_queries_eq : inverseAA_queries = 15225 := by
  rw [inverseAA_queries, aaCircuitD01_oracleCount, invCircuit_queries]

end QSVT.Examples
