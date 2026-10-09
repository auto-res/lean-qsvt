/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.NormBound
import QSVT.IR.Denote
import QSVT.Examples.FixedPointAA

/-!
# APP-COMPOSE: composing a register circuit with fixed-point amplitude amplification

Reusable machinery for feeding a Route A circuit `W` on the register `Reg m ℋ` (CERT-A, e.g. the
Hamiltonian-simulation circuit `evoCircuit` of APP-4) into the fixed-point amplitude
amplification of APP-1 (`aaCircuit`, GSLW Thm 27), as required by GSLW Thm 58. Three layers:

* **Normalisation** (any complex normed space): `v = ‖v‖ • (‖v‖⁻¹ • v)`, `‖‖v‖⁻¹ • v‖ = 1`,
  positive real scalings normalise to the same unit vector (`normalize_smul`), and the
  normalisation map is `2`-Lipschitz towards unit vectors: `‖v/‖v‖ − w‖ ≤ 2 ‖v − w‖` for `‖w‖ = 1`
  (`norm_normalize_sub_le`).
* **Spectral functional calculus** of a Hermitian encoding `E` (encoded operator `A`, eigenbasis
  `ψᵢ` of `A|_{ran Π}` with eigenvalues `ςᵢ`, SVT-3/SVT-4): `funCalc E f x = ∑ᵢ ⟪ψᵢ, x⟫ f(ςᵢ) ψᵢ`
  for `f : ℝ → ℂ`, which agrees with `p(A) x` for polynomials (`aeval_eq_funCalc`). Parseval
  (`norm_funCalc_sq`) gives the two-sided bounds `m ‖x‖ ≤ ‖f(A) x‖ ≤ M ‖x‖` whenever
  `m ≤ ‖f(ςᵢ)‖ ≤ M` on the spectrum (`norm_funCalc_ge`, `norm_funCalc_le`; the lower bound only
  needs the eigenvalues in the support of `x`, `norm_funCalc_ge_of_support`), the isometry
  statement for unimodular `f` (`norm_funCalc_eq_of_unimodular`), and the approximation lemma
  `‖p(A) x − f(A) x‖ ≤ η ‖x‖` from `‖p(ςᵢ) − f(ςᵢ)‖ ≤ η` (`norm_aeval_sub_funCalc_le`). The
  polynomial lower bound `norm_aeval_apply_ge` is the companion of SVT-4 `norm_aeval_apply_le`.
* **The amplitude-amplification instance of a register circuit** `W : L (Reg m ℋ)`, unitary, on an
  input `b ∈ ran Π`, `‖b‖ = 1`: the initial state is `ψ₀ = |0⟩ ⊗ b` (`norm_inj_zero`), the good
  projector is `G = |0⟩⟨0| ⊗ Π = atZero Π` (IR-1, `atZero_isProjective`), and the good component
  of the output is `G W ψ₀ = |0⟩ ⊗ ((⟨0| ⊗ Π) W (|0⟩ ⊗ Π)) b` (`atZero_P_apply`): the vector
  `regGood E W b` on the system, with norm `a = regAmp E W b` and normalisation
  `ψ_G = regGoodState E W b`. These satisfy the hypotheses `G (U ψ₀) = a ψ_G`, `‖ψ_G‖ = 1`,
  `0 < a` of APP-1 (`atZero_P_apply_eq_smul`, `norm_regGoodState`), so the APP-1 circuit
  `regAACircuit E hW hb1 = aaCircuit …` on `Anc (Reg m ℋ)` (one more ancilla qubit, `21` uses of
  `W`/`W†`) inherits `fixedPointAA_apply`/`_bound`/`_amplitude` (`regAA_apply`, `regAA_bound`,
  `regAA_amplitude`): for `a ≥ 0.15` the good-subspace output is `≈ 0.8924 ψ_G` with success
  amplitude `≥ 0.869`.

Why `atZero Π` and not the ancilla projector `reg0 = |0⟩⟨0| ⊗ 1`: the Route A theorems
(`routeA`, `evoCircuit_topLeft`) describe the `(0,0)` block of the *compressed* circuit
`(1 ⊗ Π) W (1 ⊗ Π)`, i.e. `Π W₀₀ Π`; with the good projector `|0⟩⟨0| ⊗ Π` the good component of
`W (|0⟩ ⊗ b)` is exactly `|0⟩ ⊗ Π W₀₀ b = |0⟩ ⊗ (Π W₀₀ Π) b` (`regTopLeft_regP_apply`), so the
compressed block is all that is needed, with zero error.

## Mathlib API used

`le_of_sq_le_sq`, `pow_le_pow_left₀`, `mul_nonpos_iff`, `abs_norm_sub_norm_le`,
`norm_sub_rev`, `norm_pos_iff`, `norm_ne_zero_iff`, `Complex.ofReal_inv`, `Complex.ofReal_mul`,
`Complex.norm_real`, `mul_inv`, `inv_mul_cancel₀`, `Finset.sum_sub_distrib`, `Finset.mul_sum`.
-/

namespace QSVT.Examples

open QSVT.Certificate QSVT.SVT QSVT.QSP QSVT.Poly QSVT.Encoding QSVT.IR QSVT.Pipeline QuantumState
open Polynomial

universe u

/-! ### Normalisation -/

section Normalize

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- APP-COMPOSE. `v = ‖v‖ • (‖v‖⁻¹ • v)` for `v ≠ 0`. -/
theorem eq_norm_smul_normalize (v : V) (hv : v ≠ 0) :
    v = ((‖v‖ : ℝ) : ℂ) • (((‖v‖ : ℝ) : ℂ)⁻¹ • v) := by
  rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)), one_smul]

/-- APP-COMPOSE. `‖‖v‖⁻¹ • v‖ = 1` for `v ≠ 0`. -/
theorem norm_normalize (v : V) (hv : v ≠ 0) : ‖((‖v‖ : ℝ) : ℂ)⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- APP-COMPOSE. Normalising `c • v` for a positive real `c` gives the normalisation of `v`. -/
theorem normalize_smul (c : ℝ) (hc : 0 < c) (v : V) :
    ((‖(c : ℂ) • v‖ : ℝ) : ℂ)⁻¹ • ((c : ℂ) • v) = ((‖v‖ : ℝ) : ℂ)⁻¹ • v := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le, smul_smul, Complex.ofReal_mul,
    mul_inv, mul_comm ((c : ℝ) : ℂ)⁻¹, mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), mul_one]

/-- APP-COMPOSE. Normalisation is `2`-Lipschitz towards unit vectors:
`‖v/‖v‖ − w‖ ≤ 2 ‖v − w‖` for `v ≠ 0` and `‖w‖ = 1` (the first `‖v − w‖` bounds the change of
norm `|1 − ‖v‖|`, the second the change of direction). -/
theorem norm_normalize_sub_le (v w : V) (hv : v ≠ 0) (hw : ‖w‖ = 1) :
    ‖((‖v‖ : ℝ) : ℂ)⁻¹ • v - w‖ ≤ 2 * ‖v - w‖ := by
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h0 : ((‖v‖ : ℝ) : ℂ)⁻¹ • v - v = (((‖v‖ : ℝ) : ℂ)⁻¹ - 1) • v := by
    rw [sub_smul, one_smul]
  have h1 : ‖((‖v‖ : ℝ) : ℂ)⁻¹ • v - v‖ = |1 - ‖v‖| := by
    rw [h0, norm_smul, ← Complex.ofReal_one, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    calc |‖v‖⁻¹ - 1| * ‖v‖ = |(‖v‖⁻¹ - 1) * ‖v‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
      _ = |1 - ‖v‖| := by rw [sub_mul, inv_mul_cancel₀ hv', one_mul]
  have h2 : |1 - ‖v‖| ≤ ‖v - w‖ := by
    rw [← hw, norm_sub_rev]
    exact abs_norm_sub_norm_le w v
  calc ‖((‖v‖ : ℝ) : ℂ)⁻¹ • v - w‖
      = ‖(((‖v‖ : ℝ) : ℂ)⁻¹ • v - v) + (v - w)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖((‖v‖ : ℝ) : ℂ)⁻¹ • v - v‖ + ‖v - w‖ := norm_add_le _ _
    _ ≤ ‖v - w‖ + ‖v - w‖ := add_le_add (h1 ▸ h2) le_rfl
    _ = 2 * ‖v - w‖ := by ring

end Normalize

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The spectral functional calculus on `ran Π` -/

section FunCalc

variable (E : HermitianEncoding ℋ)

/-- APP-COMPOSE. The spectral functional calculus `f(A) x := ∑ᵢ ⟪ψᵢ, x⟫ f(ςᵢ) ψᵢ` of a function
`f : ℝ → ℂ`, through the eigenbasis `ψᵢ` of `A|_{ran Π}` (SVT-3). For `x ∈ ran Π` and a polynomial
`p` this is `p(A) x` (`aeval_eq_funCalc`). -/
noncomputable def funCalc (f : ℝ → ℂ) (x : ℋ) : ℋ :=
  ∑ i, (inner ℂ (eigenVec E i) x * f (eigenValue E i)) • eigenVec E i

/-- APP-COMPOSE. `p(A) x = p(A) x` through the functional calculus, for `x ∈ ran Π`. -/
theorem aeval_eq_funCalc (p : ℂ[X]) (x : ℋ) (hx : E.P x = x) :
    aeval E.encoded p x = funCalc E (fun t => p.eval (t : ℂ)) x :=
  aeval_apply_eq_sum E p x hx

/-- APP-COMPOSE. `f(A) x − g(A) x = (f − g)(A) x`. -/
theorem funCalc_sub (f g : ℝ → ℂ) (x : ℋ) :
    funCalc E f x - funCalc E g x = funCalc E (f - g) x := by
  rw [funCalc, funCalc, funCalc, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, mul_sub, sub_smul]

/-- APP-COMPOSE (Parseval). `‖f(A) x‖² = ∑ᵢ ‖⟪ψᵢ, x⟫‖² ‖f(ςᵢ)‖²`. -/
theorem norm_funCalc_sq (f : ℝ → ℂ) (x : ℋ) :
    ‖funCalc E f x‖ ^ 2 = ∑ i, ‖inner ℂ (eigenVec E i) x‖ ^ 2 * ‖f (eigenValue E i)‖ ^ 2 := by
  rw [funCalc, norm_sum_smul_eigenVec_sq]
  exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, mul_pow]

/-- APP-COMPOSE (Parseval). `‖x‖² = ∑ᵢ ‖⟪ψᵢ, x⟫‖²` for `x ∈ ran Π`. -/
theorem norm_sq_eq_sum_inner_eigenVec (x : ℋ) (hx : E.P x = x) :
    ‖x‖ ^ 2 = ∑ i, ‖inner ℂ (eigenVec E i) x‖ ^ 2 := by
  conv_lhs => rw [sum_repr_eigenVec E x hx]
  exact norm_sum_smul_eigenVec_sq E _

/-- APP-COMPOSE. `‖f(A) x‖ ≤ M ‖x‖` for `x ∈ ran Π` when `‖f(ςᵢ)‖ ≤ M` on the spectrum. -/
theorem norm_funCalc_le (f : ℝ → ℂ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ i, ‖f (eigenValue E i)‖ ≤ M)
    (x : ℋ) (hx : E.P x = x) : ‖funCalc E f x‖ ≤ M * ‖x‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg hM0 (norm_nonneg x))
  rw [norm_funCalc_sq, mul_pow, norm_sq_eq_sum_inner_eigenVec E x hx, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm (M ^ 2)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hM i) 2) (sq_nonneg _)

/-- APP-COMPOSE. `m ‖x‖ ≤ ‖f(A) x‖` for `x ∈ ran Π` when `m ≤ ‖f(ςᵢ)‖` for every eigenvalue
`ςᵢ` in the support of `x` (`⟪ψᵢ, x⟫ ≠ 0`). -/
theorem norm_funCalc_ge_of_support (f : ℝ → ℂ) (m : ℝ) (x : ℋ) (hx : E.P x = x)
    (hm : ∀ i, inner ℂ (eigenVec E i) x ≠ 0 → m ≤ ‖f (eigenValue E i)‖) :
    m * ‖x‖ ≤ ‖funCalc E f x‖ := by
  rcases le_or_gt 0 m with hm0 | hm0
  · refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [norm_funCalc_sq, mul_pow, norm_sq_eq_sum_inner_eigenVec E x hx, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm (m ^ 2)]
    by_cases hi : inner ℂ (eigenVec E i) x = 0
    · rw [hi, norm_zero]
      simp
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 (hm i hi) 2) (sq_nonneg _)
  · exact (mul_nonpos_iff.mpr (Or.inr ⟨hm0.le, norm_nonneg x⟩)).trans (norm_nonneg _)

/-- APP-COMPOSE. `m ‖x‖ ≤ ‖f(A) x‖` for `x ∈ ran Π` when `m ≤ ‖f(ςᵢ)‖` on the spectrum. -/
theorem norm_funCalc_ge (f : ℝ → ℂ) (m : ℝ) (hm : ∀ i, m ≤ ‖f (eigenValue E i)‖) (x : ℋ)
    (hx : E.P x = x) : m * ‖x‖ ≤ ‖funCalc E f x‖ :=
  norm_funCalc_ge_of_support E f m x hx fun i _ => hm i

/-- APP-COMPOSE. `‖f(A) x‖ = ‖x‖` for `x ∈ ran Π` when `f` is unimodular on the spectrum. -/
theorem norm_funCalc_eq_of_unimodular (f : ℝ → ℂ) (hf : ∀ i, ‖f (eigenValue E i)‖ = 1) (x : ℋ)
    (hx : E.P x = x) : ‖funCalc E f x‖ = ‖x‖ := by
  refine le_antisymm ?_ ?_
  · have h := norm_funCalc_le E f 1 zero_le_one (fun i => (hf i).le) x hx
    rwa [one_mul] at h
  · have h := norm_funCalc_ge E f 1 (fun i => (hf i).ge) x hx
    rwa [one_mul] at h

/-- APP-COMPOSE. `‖f(A) x − g(A) x‖ ≤ η ‖x‖` for `x ∈ ran Π` when `‖f(ςᵢ) − g(ςᵢ)‖ ≤ η` on the
spectrum. -/
theorem norm_funCalc_sub_le (f g : ℝ → ℂ) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : ∀ i, ‖f (eigenValue E i) - g (eigenValue E i)‖ ≤ η) (x : ℋ) (hx : E.P x = x) :
    ‖funCalc E f x - funCalc E g x‖ ≤ η * ‖x‖ := by
  rw [funCalc_sub]
  exact norm_funCalc_le E (f - g) η hη0 (fun i => hη i) x hx

/-- APP-COMPOSE (lower bound of the polynomial functional calculus, companion of SVT-4
`norm_aeval_apply_le`). `m ‖x‖ ≤ ‖p(A) x‖` for `x ∈ ran Π` when `m ≤ ‖p(ςᵢ)‖` for every
eigenvalue `ςᵢ` of `A`. -/
theorem norm_aeval_apply_ge (p : ℂ[X]) (m : ℝ) (hm : ∀ i, m ≤ ‖p.eval (eigenValue E i : ℂ)‖)
    (x : ℋ) (hx : E.P x = x) : m * ‖x‖ ≤ ‖aeval E.encoded p x‖ := by
  rw [aeval_eq_funCalc E p x hx]
  exact norm_funCalc_ge E _ m hm x hx

/-- APP-COMPOSE. The lower bound only needs the eigenvalues in the support of `x`. -/
theorem norm_aeval_apply_ge_of_support (p : ℂ[X]) (m : ℝ) (x : ℋ) (hx : E.P x = x)
    (hm : ∀ i, inner ℂ (eigenVec E i) x ≠ 0 → m ≤ ‖p.eval (eigenValue E i : ℂ)‖) :
    m * ‖x‖ ≤ ‖aeval E.encoded p x‖ := by
  rw [aeval_eq_funCalc E p x hx]
  exact norm_funCalc_ge_of_support E _ m x hx hm

/-- APP-COMPOSE (approximation lemma). `‖p(A) x − f(A) x‖ ≤ η ‖x‖` for `x ∈ ran Π` when
`‖p(ςᵢ) − f(ςᵢ)‖ ≤ η` on the spectrum: a pointwise certificate for `p ≈ f` on `[-1, 1]`
transfers to the operators. -/
theorem norm_aeval_sub_funCalc_le (p : ℂ[X]) (f : ℝ → ℂ) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : ∀ i, ‖p.eval (eigenValue E i : ℂ) - f (eigenValue E i)‖ ≤ η) (x : ℋ)
    (hx : E.P x = x) : ‖aeval E.encoded p x - funCalc E f x‖ ≤ η * ‖x‖ := by
  rw [aeval_eq_funCalc E p x hx]
  exact norm_funCalc_sub_le E _ f η hη0 hη x hx

end FunCalc

/-! ### The amplitude-amplification instance of a register circuit -/

section RegisterAA

variable {m : ℕ} [NeZero m]

/-- APP-COMPOSE. `(|0⟩⟨0| ⊗ B) v = |0⟩ ⊗ B (⟨0| v)`. -/
theorem atZero_apply (B : L ℋ) (v : Reg m ℋ) : atZero B v = inj 0 (B (proj 0 v)) := by
  rw [atZero_eq_mul_reg0, Module.End.mul_apply, reg0_apply, selectOp_inj]

/-- APP-COMPOSE. The good component of `W (|0⟩ ⊗ b)` is `|0⟩ ⊗ B W₀₀ b`. -/
theorem atZero_apply_inj (B : L ℋ) (W : L (Reg m ℋ)) (b : ℋ) :
    atZero B (W (inj 0 b)) = inj 0 (B (regTopLeft W b)) :=
  atZero_apply B _

/-- APP-COMPOSE. `|0⟩ ⊗ b` is a unit vector when `b` is. -/
theorem norm_inj_zero (b : ℋ) (hb1 : ‖b‖ = 1) : ‖(inj 0 b : Reg m ℋ)‖ = 1 := by
  rw [norm_inj, hb1]

variable (E : HermitianEncoding ℋ)

/-- APP-COMPOSE. On `b ∈ ran Π`, the `(0,0)` block of the compressed circuit `(1 ⊗ Π) W (1 ⊗ Π)`
is `Π W₀₀ b`. -/
theorem regTopLeft_regP_apply (W : L (Reg m ℋ)) (b : ℋ) (hb : E.P b = b) :
    regTopLeft (regP E * W * regP E) b = E.P (regTopLeft W b) := by
  rw [regP, regTopLeft_selectOp_const_mul_mul, Module.End.mul_apply, Module.End.mul_apply, hb]

/-- APP-COMPOSE. The (unnormalised) good vector on the system: `((⟨0| ⊗ Π) W (|0⟩ ⊗ Π)) b`, the
`(0,0)` block of the compressed circuit applied to `b` (what the Route A theorems compute). -/
noncomputable def regGood (W : L (Reg m ℋ)) (b : ℋ) : ℋ := regTopLeft (regP E * W * regP E) b

/-- APP-COMPOSE. The initial good amplitude `a = ‖(|0⟩⟨0| ⊗ Π) W (|0⟩ ⊗ b)‖`. -/
noncomputable def regAmp (W : L (Reg m ℋ)) (b : ℋ) : ℝ := ‖regGood E W b‖

/-- APP-COMPOSE. The normalised good state `ψ_G = |0⟩ ⊗ (regGood / a)` (GSLW Thm 27's
`Π U ψ₀ / ‖Π U ψ₀‖`). -/
noncomputable def regGoodState (W : L (Reg m ℋ)) (b : ℋ) : Reg m ℋ :=
  ((regAmp E W b : ℝ) : ℂ)⁻¹ • inj 0 (regGood E W b)

variable (W : L (Reg m ℋ)) (b : ℋ)

/-- APP-COMPOSE. `(|0⟩⟨0| ⊗ Π) W (|0⟩ ⊗ b) = |0⟩ ⊗ regGood E W b` for `b ∈ ran Π`. -/
theorem atZero_P_apply (hb : E.P b = b) :
    atZero E.P (W (inj 0 b)) = inj 0 (regGood E W b) := by
  rw [atZero_apply_inj, regGood, regTopLeft_regP_apply E W b hb]

theorem regAmp_eq_norm_inj : regAmp E W b = ‖(inj 0 (regGood E W b) : Reg m ℋ)‖ := by
  rw [regAmp, norm_inj]

theorem regAmp_nonneg : 0 ≤ regAmp E W b := norm_nonneg _

theorem inj_regGood_ne_zero (h : 0 < regAmp E W b) :
    (inj 0 (regGood E W b) : Reg m ℋ) ≠ 0 := by
  rw [← norm_pos_iff, ← regAmp_eq_norm_inj]
  exact h

/-- APP-COMPOSE. `‖ψ_G‖ = 1` when `a > 0`. -/
theorem norm_regGoodState (h : 0 < regAmp E W b) : ‖regGoodState E W b‖ = 1 := by
  rw [regGoodState, regAmp_eq_norm_inj]
  exact norm_normalize _ (inj_regGood_ne_zero E W b h)

/-- APP-COMPOSE (the hypothesis `G (U ψ₀) = a ψ_G` of APP-1). -/
theorem atZero_P_apply_eq_smul (hb : E.P b = b) (h : 0 < regAmp E W b) :
    atZero E.P (W (inj 0 b)) = ((regAmp E W b : ℝ) : ℂ) • regGoodState E W b := by
  rw [atZero_P_apply E W b hb, regGoodState, regAmp_eq_norm_inj]
  exact eq_norm_smul_normalize _ (inj_regGood_ne_zero E W b h)

/-- APP-COMPOSE. `ψ_G` lies in the good subspace: `(|0⟩⟨0| ⊗ Π) ψ_G = ψ_G`. -/
theorem atZero_P_regGoodState (hb : E.P b = b) (h : 0 < regAmp E W b) :
    atZero E.P (regGoodState E W b) = regGoodState E W b :=
  aa_G_ψG (atZero_isProjective E.hP) h (atZero_P_apply_eq_smul E W b hb h)

end RegisterAA

/-! ### Fixed-point amplitude amplification of a register circuit (APP-1 instantiated) -/

section RegisterAACircuit

variable {m : ℕ} [NeZero m] (E : HermitianEncoding ℋ) {W : L (Reg m ℋ)}
  (hW : W ∈ unitary (L (Reg m ℋ))) {b : ℋ} (hb1 : ‖b‖ = 1)

/-- APP-COMPOSE. The fixed-point amplitude amplification circuit of APP-1 for the register
circuit `W`, initial state `|0⟩ ⊗ b` and good projector `|0⟩⟨0| ⊗ Π`: the two-term LCU
`lcu2 U_Φ̃ U_{−Φ̃}` of the alternating sequences built from `W`, on `Anc (Reg m ℋ)` (one more
ancilla qubit), with `21` uses of `W`/`W†` (`aaCircuit_oracleCount`). -/
noncomputable def regAACircuit : L (Anc (Reg m ℋ)) :=
  aaCircuit hW (atZero_isProjective (m := m) E.hP) (norm_inj_zero b hb1)

/-- APP-COMPOSE. The circuit is unitary. -/
theorem regAACircuit_mem_unitary : regAACircuit E hW hb1 ∈ unitary (L (Anc (Reg m ℋ))) :=
  aaCircuit_mem_unitary _ _ _

/-- APP-COMPOSE (exact; `fixedPointAA_apply`). The good-subspace, ancilla-`0` block of the circuit
maps `|0⟩ ⊗ b` exactly onto `ψ_G`, scaled by `Re[P_Φ̃](a)`. -/
theorem regAA_apply (hb : E.P b = b) (h : 0 < regAmp E W b) :
    topLeft (blockDiag (atZero E.P) 0 * regAACircuit E hW hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) =
      ((rePoly (qspPoly (sign21Phases.map (↑))).1).eval ((regAmp E W b : ℝ) : ℂ)) •
        regGoodState E W b :=
  fixedPointAA_apply hW _ _ (norm_regGoodState E W b h) h (atZero_P_apply_eq_smul E W b hb h)

/-- APP-COMPOSE (`fixedPointAA_bound`). For an initial amplitude `a ≥ 0.15` the good-subspace
output is `sign21Scale · ψ_G ≈ 0.8924 ψ_G` up to `10⁻¹² + 0.0236`. -/
theorem regAA_bound (hb : E.P b = b) (ha : 0.15 ≤ regAmp E W b) :
    ‖topLeft (blockDiag (atZero E.P) 0 * regAACircuit E hW hb1 * blockDiag (rankOne (inj 0 b)) 0)
        (inj 0 b) - (sign21Scale : ℂ) • regGoodState E W b‖ ≤ sign21Eps + 0.0236 :=
  fixedPointAA_bound hW _ _ (norm_regGoodState E W b (by linarith)) (by linarith)
    (atZero_P_apply_eq_smul E W b hb (by linarith)) ha

/-- APP-COMPOSE (`fixedPointAA_amplitude`). For an initial amplitude `a ≥ 0.15` the norm of the
ancilla-`0`, good-subspace component of the output state is at least `0.869`. -/
theorem regAA_amplitude (hb : E.P b = b) (ha : 0.15 ≤ regAmp E W b) :
    0.869 ≤ ‖blockDiag (atZero E.P) 0 (regAACircuit E hW hb1 (inl (inj 0 b)))‖ :=
  fixedPointAA_amplitude hW _ _ (norm_regGoodState E W b (by linarith)) (by linarith)
    (atZero_P_apply_eq_smul E W b hb (by linarith)) ha

end RegisterAACircuit

end QSVT.Examples
