/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Encoding.Register

/-!
# `m`-term linear combination of unitaries (formal-spec ENC-3, GSLW Lemma 52)

The LCU circuit on the `m`-dimensional ancilla register `Reg m ℋ` of `QSVT.Encoding.Register`
with state-preparation matrix `V : Matrix (Fin m) (Fin m) ℂ` and unitaries `W k : L ℋ`:

`lcu V W = (Vᴴ ⊗ 1) (∑ₖ |k⟩⟨k| ⊗ Wₖ) (V ⊗ 1) = matOp Vᴴ * selectOp W * matOp V`.

It is unitary when `V` and all `Wₖ` are (`lcu_mem_unitary`), and its top-left block is

`topLeft (lcu V W) = ∑ₖ |V k 0|² • Wₖ` (`topLeft_lcu`),

i.e. the LCU block-encodes `∑ₖ wₖ Wₖ` whenever the first column of `V` is `(√wₖ)ₖ`
(`topLeft_lcu_of_real`).

## State preparation by a Householder reflection

For a unit vector `u : Fin m → ℂ` with real first coordinate, `householder u` is the
Householder reflection `1 − 2 d d† / (d† d)` along `d := u − e₀` (the identity when `d = 0`).
It is unitary for every `u` (`householder_mem_unitaryGroup`, no normalization needed) and maps
`e₀ ↦ u` when `∑ₖ ‖uₖ‖² = 1` and `(u 0).im = 0` (`householder_mulVec_single`,
`householder_apply_zero`). The real-first-coordinate restriction is harmless here because LCU
weights enter as `√wₖ ≥ 0`; a general complex `u` can be handled by first rotating the phase of
`u 0`, which is not needed in this project.

## Main statements

* `topLeft_lcu_householder`: for weights `w ≥ 0` with `∑ w = 1`,
  `topLeft (lcu (householder (√w)) W) = ∑ₖ wₖ • Wₖ` (Route A of GSLW Lemma 52).
* `lcu_complex`: complex coefficients `c` with `∑ ‖cₖ‖ = 1` are absorbed into the unitaries,
  `topLeft (lcu (householder (√‖c‖)) (fun k => phase (cₖ) • Wₖ)) = ∑ₖ cₖ • Wₖ`, where
  `phase z = z / ‖z‖` (`1` for `z = 0`) is a unit scalar, so `phase (cₖ) • Wₖ` is unitary
  (`smul_mem_unitary_of_norm_eq_one`).

For `m = 2`, `V = H` and `w = (1/2, 1/2)` this recovers `QSVT.Encoding.lcu2` (GSLW Cor 18).

## Mathlib API used

`Matrix.vecMulVec`, `Matrix.vecMulVec_mul_vecMulVec`, `Matrix.vecMulVec_mulVec`,
`Matrix.conjTranspose_vecMulVec`, `dotProduct_single`, `single_dotProduct`,
`dotProduct_star_self_eq_zero`, `star_dotProduct`, `Matrix.mulVec_single_one`,
`Matrix.mem_unitaryGroup_iff`, `Complex.conj_mul'`, `Complex.conj_eq_iff_im`,
`Unitary.smul_mem_of_mem`.
-/

namespace QSVT.Encoding

open QuantumState Matrix

universe u

variable {ℋ : Type u} [Qudit ℋ] {m : ℕ}

/-! ### The LCU circuit -/

/-- ENC-3. The `m`-term LCU circuit with state-preparation matrix `V` and unitaries `W k`:
`lcu V W = (Vᴴ ⊗ 1) (∑ₖ |k⟩⟨k| ⊗ Wₖ) (V ⊗ 1)`. -/
noncomputable def lcu (V : Matrix (Fin m) (Fin m) ℂ) (W : Fin m → L ℋ) : L (Reg m ℋ) :=
  matOp Vᴴ * selectOp W * matOp V

section lcu

variable (V : Matrix (Fin m) (Fin m) ℂ) (W : Fin m → L ℋ)

/-- ENC-3. The LCU circuit is unitary when `V` and all `W k` are. -/
theorem lcu_mem_unitary (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hW : ∀ k, W k ∈ unitary (L ℋ)) : lcu V W ∈ unitary (L (Reg m ℋ)) :=
  mul_mem (mul_mem (matOp_mem_unitary Vᴴ (Unitary.star_mem hV)) (selectOp_mem_unitary W hW))
    (matOp_mem_unitary V hV)

/-- ENC-3 / GSLW Lemma 52. The top-left block of the LCU circuit is `∑ₖ |V k 0|² • Wₖ`. -/
theorem topLeft_lcu [NeZero m] :
    topLeft (lcu V W) = ∑ k, (star (V k 0) * V k 0) • W k := by
  refine LinearMap.ext fun x => ?_
  simp only [topLeft_apply, lcu, Module.End.mul_apply, proj_matOp, proj_selectOp, proj_inj,
    smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_smul,
    Matrix.conjTranspose_apply, smul_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- ENC-3. If the first column of `V` is `(√wₖ)ₖ` with `wₖ ≥ 0`, the LCU circuit
block-encodes `∑ₖ wₖ • Wₖ`. -/
theorem topLeft_lcu_of_real [NeZero m] (w : Fin m → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hV0 : ∀ k, V k 0 = ((Real.sqrt (w k) : ℝ) : ℂ)) :
    topLeft (lcu V W) = ∑ k, (w k : ℂ) • W k := by
  rw [topLeft_lcu]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hV0, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hw k)]

end lcu

/-! ### Householder reflections -/

/-- ENC-3. The Householder reflection `1 − 2 d d† / (d† d)` along `d` (the identity for
`d = 0`). -/
noncomputable def reflection (d : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - (2 / (star d ⬝ᵥ d)) • vecMulVec d (star d)

section reflection

variable (d : Fin m → ℂ)

@[simp] theorem reflection_zero : reflection (0 : Fin m → ℂ) = 1 := by
  simp [reflection]

/-- `star (d† d) = d† d`. -/
theorem star_dotProduct_self_star : star (star d ⬝ᵥ d) = star d ⬝ᵥ d :=
  (star_dotProduct d d).symm

/-- `d† d = ∑ₖ ‖dₖ‖²` as a complex number. -/
theorem star_dotProduct_self_eq_sum_norm_sq : star d ⬝ᵥ d = ((∑ k, ‖d k‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ k, star (d k) * d k = ((‖d k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp only [dotProduct, Pi.star_apply, h, Complex.ofReal_sum]

/-- `d† d ≠ 0` for `d ≠ 0`. -/
theorem star_dotProduct_self_ne_zero {d : Fin m → ℂ} (hd : d ≠ 0) : star d ⬝ᵥ d ≠ 0 := by
  rw [star_dotProduct_self_eq_sum_norm_sq, Complex.ofReal_ne_zero]
  intro h
  apply hd
  funext k
  have hk := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg ‖d k‖).mp h k
    (Finset.mem_univ k)
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hk)

/-- A unit vector `u` (`∑ₖ ‖uₖ‖² = 1`) satisfies `u† u = 1`. -/
theorem star_dotProduct_self_eq_one {u : Fin m → ℂ} (hu : ∑ k, ‖u k‖ ^ 2 = 1) :
    star u ⬝ᵥ u = 1 := by
  rw [star_dotProduct_self_eq_sum_norm_sq, hu, Complex.ofReal_one]

/-- A Householder reflection is Hermitian. -/
theorem reflection_conjTranspose : (reflection d)ᴴ = reflection d := by
  rw [reflection, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
    conjTranspose_vecMulVec, star_star, star_div₀, star_ofNat, star_dotProduct_self_star]

/-- A Householder reflection squares to the identity. -/
theorem reflection_mul_self : reflection d * reflection d = 1 := by
  by_cases hd : d = 0
  · subst hd
    rw [reflection_zero, one_mul]
  · have hs : star d ⬝ᵥ d ≠ 0 := star_dotProduct_self_ne_zero hd
    have hMM : vecMulVec d (star d) * vecMulVec d (star d) =
        (star d ⬝ᵥ d) • vecMulVec d (star d) := by
      rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    have hc : 2 / (star d ⬝ᵥ d) * (star d ⬝ᵥ d) = 2 := div_mul_cancel₀ 2 hs
    have key : ((2 / (star d ⬝ᵥ d)) • vecMulVec d (star d)) *
        ((2 / (star d ⬝ᵥ d)) • vecMulVec d (star d)) =
          (2 / (star d ⬝ᵥ d) * 2) • vecMulVec d (star d) := by
      rw [smul_mul_assoc, mul_smul_comm, hMM, smul_smul, smul_smul, mul_assoc, hc]
    rw [reflection, sub_mul, mul_sub, mul_sub, key]
    simp only [one_mul, mul_one]
    rw [mul_two, add_smul]
    abel

/-- ENC-3. A Householder reflection is unitary (for every `d`, including `d = 0`). -/
theorem reflection_mem_unitaryGroup : reflection d ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, reflection_conjTranspose,
    reflection_mul_self]

/-- `(1 − 2 d d†/(d†d)) x = x − (2 (d† x)/(d†d)) d`. -/
theorem reflection_mulVec (x : Fin m → ℂ) :
    reflection d *ᵥ x = x - (2 / (star d ⬝ᵥ d) * (star d ⬝ᵥ x)) • d := by
  rw [reflection, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

end reflection

section householder

variable [NeZero m]

/-- ENC-3. State preparation by a Householder reflection: the reflection along `u − e₀`, which
maps `e₀ ↦ u` for unit vectors `u` with real first coordinate (`householder_mulVec_single`). -/
noncomputable def householder (u : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  reflection (u - Pi.single 0 1)

variable (u : Fin m → ℂ)

/-- ENC-3. `householder u` is unitary for every `u`. -/
theorem householder_mem_unitaryGroup : householder u ∈ Matrix.unitaryGroup (Fin m) ℂ :=
  reflection_mem_unitaryGroup _

/-- ENC-3. `householder u` maps `e₀` to `u` when `u` is a unit vector with real first
coordinate. -/
theorem householder_mulVec_single (hu : ∑ k, ‖u k‖ ^ 2 = 1) (h0 : (u 0).im = 0) :
    householder u *ᵥ Pi.single 0 1 = u := by
  set e : Fin m → ℂ := Pi.single 0 1 with he
  set d : Fin m → ℂ := u - e with hd
  have hue : u = e + d := by rw [hd, add_sub_cancel]
  have hconj : star (u 0) = u 0 := by
    rw [Complex.star_def, Complex.conj_eq_iff_im.mpr h0]
  rw [householder, ← he, ← hd, reflection_mulVec, he, dotProduct_single, mul_one, ← he]
  by_cases hd0 : d = 0
  · rw [hd0, smul_zero, sub_zero, hue, hd0, add_zero]
  · have hs0 : star d ⬝ᵥ d ≠ 0 := star_dotProduct_self_ne_zero hd0
    have hstar_e : star e = e := by
      rw [he, Pi.star_single, star_one]
    have hd00 : star d 0 = u 0 - 1 := by
      rw [Pi.star_apply, hd, Pi.sub_apply, he, Pi.single_eq_same, star_sub, star_one, hconj]
    have hs : star d ⬝ᵥ d = 2 - 2 * u 0 := by
      rw [hd, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        star_dotProduct_self_eq_one hu, hstar_e, he, dotProduct_single, single_dotProduct,
        single_dotProduct, Pi.single_eq_same, Pi.star_apply, hconj, mul_one, one_mul, one_mul]
      ring
    have hcoef : 2 / (star d ⬝ᵥ d) * star d 0 = -1 := by
      have hne : (2 : ℂ) - 2 * u 0 ≠ 0 := hs ▸ hs0
      rw [hs, hd00, div_mul_eq_mul_div, div_eq_iff hne]
      ring
    rw [hcoef, neg_one_smul, sub_neg_eq_add, hue]

/-- ENC-3. The first column of `householder u` is `u`. -/
theorem householder_apply_zero (hu : ∑ k, ‖u k‖ ^ 2 = 1) (h0 : (u 0).im = 0) (k : Fin m) :
    householder u k 0 = u k := by
  have h := congrFun (householder_mulVec_single u hu h0) k
  rwa [mulVec_single_one, col_apply] at h

end householder

/-! ### LCU with prescribed nonnegative weights (Route A) -/

/-- The square roots of nonnegative weights form a unit vector. -/
theorem sum_norm_sq_ofReal_sqrt (w : Fin m → ℝ) (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    ∑ k, ‖((Real.sqrt (w k) : ℝ) : ℂ)‖ ^ 2 = 1 := by
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw _), hsum]

section weights

variable [NeZero m] (w : Fin m → ℝ) (W : Fin m → L ℋ)

/-- ENC-3 / GSLW Lemma 52. The state-preparation matrix `householder (√w)` has first column
`√w`, so the LCU circuit block-encodes `∑ₖ wₖ • Wₖ`. -/
theorem topLeft_lcu_householder (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    topLeft (lcu (householder fun k => ((Real.sqrt (w k) : ℝ) : ℂ)) W) =
      ∑ k, (w k : ℂ) • W k :=
  topLeft_lcu_of_real _ W w hw fun k =>
    householder_apply_zero _ (sum_norm_sq_ofReal_sqrt w hw hsum) (Complex.ofReal_im _) k

/-- ENC-3. The LCU circuit with the Householder state preparation is unitary. -/
theorem lcu_householder_mem_unitary (hW : ∀ k, W k ∈ unitary (L ℋ)) :
    lcu (householder fun k => ((Real.sqrt (w k) : ℝ) : ℂ)) W ∈ unitary (L (Reg m ℋ)) :=
  lcu_mem_unitary _ W (householder_mem_unitaryGroup _) hW

/-- ENC-3. Existence form: every probability vector `w` is realized by some unitary `V`. -/
theorem lcu_weights (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    ∃ V ∈ Matrix.unitaryGroup (Fin m) ℂ, topLeft (lcu V W) = ∑ k, (w k : ℂ) • W k :=
  ⟨_, householder_mem_unitaryGroup _, topLeft_lcu_householder w W hw hsum⟩

end weights

/-! ### Complex coefficients -/

/-- The phase `z / ‖z‖` of a complex number (`1` for `z = 0`). -/
noncomputable def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / ‖z‖

@[simp] theorem norm_phase (z : ℂ) : ‖phase z‖ = 1 := by
  unfold phase
  split_ifs with h
  · exact norm_one
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr h)]

/-- `‖z‖ • phase z = z`. -/
theorem norm_mul_phase (z : ℂ) : (‖z‖ : ℂ) * phase z = z := by
  unfold phase
  split_ifs with h
  · rw [h, norm_zero, Complex.ofReal_zero, zero_mul]
  · rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))]

/-- A unit scalar is a unitary element of `ℂ`. -/
theorem mem_unitary_of_norm_eq_one {α : ℂ} (hα : ‖α‖ = 1) : α ∈ unitary ℂ := by
  have h : star α * α = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hα, Complex.ofReal_one, one_pow]
  exact Unitary.mem_iff.mpr ⟨h, by rw [mul_comm]; exact h⟩

/-- ENC-3. A unit scalar times a unitary operator is unitary. -/
theorem smul_mem_unitary_of_norm_eq_one {α : ℂ} (hα : ‖α‖ = 1) {U : L ℋ}
    (hU : U ∈ unitary (L ℋ)) : α • U ∈ unitary (L ℋ) :=
  Unitary.smul_mem_of_mem (mem_unitary_of_norm_eq_one hα) hU

section complex

variable [NeZero m] (c : Fin m → ℂ) (W : Fin m → L ℋ)

/-- ENC-3. Complex coefficients `c` with `∑ ‖cₖ‖ = 1`: absorbing the phases into the
unitaries, the LCU circuit with weights `‖cₖ‖` block-encodes `∑ₖ cₖ • Wₖ`. -/
theorem lcu_complex (hc : ∑ k, ‖c k‖ = 1) :
    topLeft (lcu (householder fun k => ((Real.sqrt ‖c k‖ : ℝ) : ℂ))
      fun k => phase (c k) • W k) = ∑ k, c k • W k := by
  rw [topLeft_lcu_householder (fun k => ‖c k‖) _ (fun k => norm_nonneg _) hc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, norm_mul_phase]

/-- ENC-3. The LCU circuit of `lcu_complex` is unitary. -/
theorem lcu_complex_mem_unitary (hW : ∀ k, W k ∈ unitary (L ℋ)) :
    lcu (householder fun k => ((Real.sqrt ‖c k‖ : ℝ) : ℂ)) (fun k => phase (c k) • W k) ∈
      unitary (L (Reg m ℋ)) :=
  lcu_householder_mem_unitary _ _ fun k => smul_mem_unitary_of_norm_eq_one (norm_phase _) (hW k)

end complex

end QSVT.Encoding
