/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.SVD
import QSVT.SVT.TwoVector

/-!
# The two-frame lemma for the singular value transformation (formal-spec SVT-7, core)

Let `E` be a projected unitary encoding (`U`, `Π`, `Π̃`, `A = Π̃ U Π`) and let `ψ = rv E i`,
`ψ̃ = lv E i`, `σ = σ E i` be a pair of singular vectors with singular value `σ ∈ [0, 1]`
(`QSVT.SVT.SVD`). With `s = √(1 - σ²)` define the two normalised "perpendicular" vectors
(GSLW, proof of Thm 17, eqs. (29)–(30))
```
ψ̃⊥ = (1 - Π̃) U ψ / s     (`lvt`: the frame after `U`, in `ker Π̃`)
ψ⊥  = (1 - Π) U† ψ̃ / s    (`rvp`: the frame after `U†`, in `ker Π`)
```
Then `U` maps the `Π`-frame `{ψ, ψ⊥}` to the `Π̃`-frame `{ψ̃, ψ̃⊥}` and `U†` maps it back, both
as the reflection `R(σ)` acts on the standard basis, while the phase operators act diagonally:
```
U  ψ  = σ ψ̃ + s ψ̃⊥      U  ψ⊥  = s ψ̃ - σ ψ̃⊥
U† ψ̃  = σ ψ + s ψ⊥      U† ψ̃⊥ = s ψ - σ ψ⊥
e^{iφ(2Π̃-I)} ψ̃ = e^{iφ} ψ̃    e^{iφ(2Π̃-I)} ψ̃⊥ = e^{-iφ} ψ̃⊥
e^{iφ(2Π-I)} ψ  = e^{iφ} ψ    e^{iφ(2Π-I)} ψ⊥  = e^{-iφ} ψ⊥
```
(`U_rv`, `U_rvp`, `U_adjoint_lv`, `U_adjoint_lvt`, `phaseOp_P'_lv`, `phaseOp_P'_lvt`,
`phaseOp_P_rv`, `phaseOp_P_rvp`). These relations hold for **every** `i`, including the
endpoints: for `σ = 0` one has `ψ̃ = 0`, `ψ⊥ = 0`, `ψ̃⊥ = U ψ`; for `σ = 1` one has `s = 0`,
`ψ̃⊥ = ψ⊥ = 0` (as `(0 : ℂ)⁻¹ = 0`) and `U ψ = ψ̃`, `U† ψ̃ = ψ` by Pythagoras
(`unitary_apply_eq_of_proj_apply`). Consequently the alternating sequence acts on `ψ` as the QSP
sequence `seqR Φ σ` acts on the first basis vector, landing in the `Π`-frame for even length and
in the `Π̃`-frame for odd length (`altSeq_apply_rv`):
```
U_Φ ψ = (seqR Φ σ)₀₀ ψ + (seqR Φ σ)₁₀ ψ⊥    (Φ.length even)
U_Φ ψ = (seqR Φ σ)₀₀ ψ̃ + (seqR Φ σ)₁₀ ψ̃⊥   (Φ.length odd)
```
Projecting gives the vector form of GSLW Thm 17: `Π̃ U_Φ ψ = P_Φ(σ) ψ̃` for odd length and
`Π U_Φ ψ = P_Φ(σ) ψ` for even length (`proj_altSeq_apply_rv_odd_eval`,
`proj_altSeq_apply_rv_even_eval`), with no case distinction on `σ`.

The Hermitian special case (`Π̃ = Π`, `A† = A`) is `QSVT.SVT.TwoVector`, whose proofs are
followed step by step.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### A Pythagoras lemma for the endpoint `σ = 1` -/

/-- A unitary `V` with `Π V ψ = χ` and `‖χ‖ = ‖ψ‖` satisfies `V ψ = χ`
(`‖V ψ‖ = ‖ψ‖ = ‖Π V ψ‖` forces `(1 - Π) V ψ = 0` by Pythagoras). -/
theorem unitary_apply_eq_of_proj_apply {P : L ℋ} (hP : IsProjective P) {V : L ℋ}
    (hV : V ∈ unitary (L ℋ)) {ψ χ : ℋ} (hn : ‖χ‖ = ‖ψ‖) (hPV : P (V ψ) = χ) : V ψ = χ := by
  have hV1 : V† * V = 1 := Unitary.star_mul_self_of_mem hV
  have hVV : inner ℂ (V ψ) (V ψ) = inner ℂ ψ ψ := by
    rw [← LinearMap.adjoint_inner_left V ψ (V ψ), ← Module.End.mul_apply, hV1,
      Module.End.one_apply]
  have hχ : inner ℂ χ χ = inner ℂ ψ ψ := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hn]
  have hpy := hP.inner_self_eq_add (V ψ)
  rw [hVV, hPV, hχ] at hpy
  have hw : inner ℂ ((1 - P) (V ψ)) ((1 - P) (V ψ)) = 0 := by linear_combination -hpy
  rw [inner_self_eq_zero, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
  rw [hw, hPV]

section TwoFrame

variable (E : ProjUnitaryEncoding ℋ)

/-! ### The two perpendicular vectors -/

/-- SVT-7. GSLW's `ψ̃⊥ = (1 - Π̃) U ψ / √(1 - σ²)`: the normalised component of `U ψ` orthogonal
to `ran Π̃` (the `Π̃`-frame, after `U`). -/
noncomputable def lvt (i : svIndex E) : ℋ :=
  ((Real.sqrt (1 - σ E i ^ 2) : ℂ)⁻¹) • ((1 - E.P') (E.U (rv E i)))

/-- SVT-7. GSLW's `ψ⊥ = (1 - Π) U† ψ̃ / √(1 - σ²)`: the normalised component of `U† ψ̃`
orthogonal to `ran Π` (the `Π`-frame, after `U†`). -/
noncomputable def rvp (i : svIndex E) : ℋ :=
  ((Real.sqrt (1 - σ E i ^ 2) : ℂ)⁻¹) • ((1 - E.P) ((E.U†) (lv E i)))

/-- SVT-7 (R0). `Π̃ ψ̃⊥ = 0`. -/
theorem P'_lvt (i : svIndex E) : E.P' (lvt E i) = 0 := by
  rw [lvt, map_smul, E.hP'.apply_one_sub_apply, smul_zero]

/-- SVT-7 (R0). `Π ψ⊥ = 0`. -/
theorem P_rvp (i : svIndex E) : E.P (rvp E i) = 0 := by
  rw [rvp, map_smul, E.hP.apply_one_sub_apply, smul_zero]

/-- SVT-7. `Π̃ U ψ = Π̃ U Π ψ = A ψ = σ ψ̃`. -/
theorem P'_U_rv (i : svIndex E) : E.P' (E.U (rv E i)) = (σ E i : ℂ) • lv E i := by
  calc E.P' (E.U (rv E i)) = E.P' (E.U (E.P (rv E i))) := by rw [P_rv]
    _ = E.encoded (rv E i) := rfl
    _ = (σ E i : ℂ) • lv E i := A_rv E i

/-- SVT-7. `Π U† ψ̃ = Π U† Π̃ ψ̃ = A† ψ̃ = σ ψ`. -/
theorem P_U_adjoint_lv (i : svIndex E) : E.P ((E.U†) (lv E i)) = (σ E i : ℂ) • rv E i := by
  calc E.P ((E.U†) (lv E i)) = E.P ((E.U†) (E.P' (lv E i))) := by rw [P'_lv]
    _ = ((E.encoded)†) (lv E i) := by rw [E.encoded_adjoint]; rfl
    _ = (σ E i : ℂ) • rv E i := A_adjoint_lv E i

/-! ### The endpoint `σ = 1` -/

/-- SVT-7 (endpoint). `√(1 - σ²) = 0` (in `ℂ`) when `σ = 1`. -/
theorem ofReal_sqrt_eq_zero_of_σ_eq_one {i : svIndex E} (h : σ E i = 1) :
    (Real.sqrt (1 - σ E i ^ 2) : ℂ) = 0 := by
  rw [h, one_pow, sub_self, Real.sqrt_zero, Complex.ofReal_zero]

/-- SVT-7 (endpoint). `ψ̃⊥ = 0` when `σ = 1`. -/
theorem lvt_of_σ_eq_one {i : svIndex E} (h : σ E i = 1) : lvt E i = 0 := by
  rw [lvt, ofReal_sqrt_eq_zero_of_σ_eq_one E h, inv_zero, zero_smul]

/-- SVT-7 (endpoint). `ψ⊥ = 0` when `σ = 1`. -/
theorem rvp_of_σ_eq_one {i : svIndex E} (h : σ E i = 1) : rvp E i = 0 := by
  rw [rvp, ofReal_sqrt_eq_zero_of_σ_eq_one E h, inv_zero, zero_smul]

/-- SVT-7 (endpoint). For `σ = 1`, `U ψ = ψ̃` (`‖U ψ‖ = 1 = ‖Π̃ U ψ‖`). -/
theorem U_rv_of_σ_eq_one {i : svIndex E} (h : σ E i = 1) : E.U (rv E i) = lv E i := by
  have h0 : σ E i ≠ 0 := by rw [h]; exact one_ne_zero
  refine unitary_apply_eq_of_proj_apply E.hP' E.hU ?_ ?_
  · rw [norm_lv E h0, norm_rv]
  · rw [P'_U_rv, h, Complex.ofReal_one, one_smul]

/-- SVT-7 (endpoint). For `σ = 1`, `U† ψ̃ = ψ` (`‖U† ψ̃‖ = 1 = ‖Π U† ψ̃‖`). -/
theorem U_adjoint_lv_of_σ_eq_one {i : svIndex E} (h : σ E i = 1) :
    (E.U†) (lv E i) = rv E i := by
  have h0 : σ E i ≠ 0 := by rw [h]; exact one_ne_zero
  refine unitary_apply_eq_of_proj_apply E.hP E.U_adjoint_mem_unitary ?_ ?_
  · rw [norm_rv, norm_lv E h0]
  · rw [P_U_adjoint_lv, h, Complex.ofReal_one, one_smul]

/-! ### The frame relations (R1)–(R5), valid for every `i` -/

/-- SVT-7 (R1). `U ψ = σ ψ̃ + √(1 - σ²) ψ̃⊥`. -/
theorem U_rv (i : svIndex E) :
    E.U (rv E i) = (σ E i : ℂ) • lv E i + (Real.sqrt (1 - σ E i ^ 2) : ℂ) • lvt E i := by
  rcases (σ_sq_le_one E i).lt_or_eq with h | h
  · rw [lvt, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero h), one_smul, LinearMap.sub_apply,
      Module.End.one_apply, P'_U_rv, add_sub_cancel]
  · have h1 := σ_eq_one_of_sq_eq_one E h
    rw [ofReal_sqrt_eq_zero_of_σ_eq_one E h1, zero_smul, add_zero, U_rv_of_σ_eq_one E h1, h1,
      Complex.ofReal_one, one_smul]

/-- SVT-7 (R2). `U† ψ̃ = σ ψ + √(1 - σ²) ψ⊥`. -/
theorem U_adjoint_lv (i : svIndex E) :
    (E.U†) (lv E i) = (σ E i : ℂ) • rv E i + (Real.sqrt (1 - σ E i ^ 2) : ℂ) • rvp E i := by
  rcases (σ_sq_le_one E i).lt_or_eq with h | h
  · rw [rvp, smul_smul, mul_inv_cancel₀ (ofReal_sqrt_ne_zero h), one_smul, LinearMap.sub_apply,
      Module.End.one_apply, P_U_adjoint_lv, add_sub_cancel]
  · have h1 := σ_eq_one_of_sq_eq_one E h
    rw [ofReal_sqrt_eq_zero_of_σ_eq_one E h1, zero_smul, add_zero, U_adjoint_lv_of_σ_eq_one E h1,
      h1, Complex.ofReal_one, one_smul]

/-- SVT-7 (R3). `U ψ⊥ = √(1 - σ²) ψ̃ - σ ψ̃⊥` (from `ψ̃ = U U† ψ̃`). -/
theorem U_rvp (i : svIndex E) :
    E.U (rvp E i) = (Real.sqrt (1 - σ E i ^ 2) : ℂ) • lv E i - (σ E i : ℂ) • lvt E i := by
  rcases (σ_sq_le_one E i).lt_or_eq with h | h
  · have h1 : E.U ((E.U†) (lv E i)) = lv E i := by
      rw [← Module.End.mul_apply, E.U_mul_U_adjoint, Module.End.one_apply]
    rw [U_adjoint_lv E i, map_add, map_smul, map_smul, U_rv E i] at h1
    refine smul_right_injective ℋ (ofReal_sqrt_ne_zero h) ?_
    have h2 : (Real.sqrt (1 - σ E i ^ 2) : ℂ) • E.U (rvp E i) =
        lv E i - (σ E i : ℂ) • ((σ E i : ℂ) • lv E i +
          (Real.sqrt (1 - σ E i ^ 2) : ℂ) • lvt E i) :=
      eq_sub_of_add_eq' h1
    change (Real.sqrt (1 - σ E i ^ 2) : ℂ) • E.U (rvp E i) =
      (Real.sqrt (1 - σ E i ^ 2) : ℂ) •
        ((Real.sqrt (1 - σ E i ^ 2) : ℂ) • lv E i - (σ E i : ℂ) • lvt E i)
    rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' h.le]
    module
  · have h1 := σ_eq_one_of_sq_eq_one E h
    rw [rvp_of_σ_eq_one E h1, lvt_of_σ_eq_one E h1, ofReal_sqrt_eq_zero_of_σ_eq_one E h1,
      map_zero, zero_smul, smul_zero, sub_zero]

/-- SVT-7 (R4). `U† ψ̃⊥ = √(1 - σ²) ψ - σ ψ⊥` (from `ψ = U† U ψ`). -/
theorem U_adjoint_lvt (i : svIndex E) :
    (E.U†) (lvt E i) = (Real.sqrt (1 - σ E i ^ 2) : ℂ) • rv E i - (σ E i : ℂ) • rvp E i := by
  rcases (σ_sq_le_one E i).lt_or_eq with h | h
  · have h1 : (E.U†) (E.U (rv E i)) = rv E i := by
      rw [← Module.End.mul_apply, E.U_adjoint_mul_U, Module.End.one_apply]
    rw [U_rv E i, map_add, map_smul, map_smul, U_adjoint_lv E i] at h1
    refine smul_right_injective ℋ (ofReal_sqrt_ne_zero h) ?_
    have h2 : (Real.sqrt (1 - σ E i ^ 2) : ℂ) • (E.U†) (lvt E i) =
        rv E i - (σ E i : ℂ) • ((σ E i : ℂ) • rv E i +
          (Real.sqrt (1 - σ E i ^ 2) : ℂ) • rvp E i) :=
      eq_sub_of_add_eq' h1
    change (Real.sqrt (1 - σ E i ^ 2) : ℂ) • (E.U†) (lvt E i) =
      (Real.sqrt (1 - σ E i ^ 2) : ℂ) •
        ((Real.sqrt (1 - σ E i ^ 2) : ℂ) • rv E i - (σ E i : ℂ) • rvp E i)
    rw [h2, smul_sub, smul_smul, smul_smul, ofReal_sqrt_mul_self' h.le]
    module
  · have h1 := σ_eq_one_of_sq_eq_one E h
    rw [lvt_of_σ_eq_one E h1, rvp_of_σ_eq_one E h1, ofReal_sqrt_eq_zero_of_σ_eq_one E h1,
      map_zero, zero_smul, smul_zero, sub_zero]

/-- SVT-7 (R5). `e^{iφ(2Π̃-I)} ψ̃ = e^{iφ} ψ̃`. -/
theorem phaseOp_P'_lv (i : svIndex E) (φ : ℝ) :
    phaseOp E.P' φ (lv E i) = Complex.exp (Complex.I * φ) • lv E i :=
  phaseOp_apply_of_proj_eq φ (P'_lv E i)

/-- SVT-7 (R5). `e^{iφ(2Π̃-I)} ψ̃⊥ = e^{-iφ} ψ̃⊥`. -/
theorem phaseOp_P'_lvt (i : svIndex E) (φ : ℝ) :
    phaseOp E.P' φ (lvt E i) = Complex.exp (-(Complex.I * φ)) • lvt E i :=
  phaseOp_apply_of_proj_eq_zero φ (P'_lvt E i)

/-- SVT-7 (R5). `e^{iφ(2Π-I)} ψ = e^{iφ} ψ`. -/
theorem phaseOp_P_rv (i : svIndex E) (φ : ℝ) :
    phaseOp E.P φ (rv E i) = Complex.exp (Complex.I * φ) • rv E i :=
  phaseOp_apply_of_proj_eq φ (P_rv E i)

/-- SVT-7 (R5). `e^{iφ(2Π-I)} ψ⊥ = e^{-iφ} ψ⊥`. -/
theorem phaseOp_P_rvp (i : svIndex E) (φ : ℝ) :
    phaseOp E.P φ (rvp E i) = Complex.exp (-(Complex.I * φ)) • rvp E i :=
  phaseOp_apply_of_proj_eq_zero φ (P_rvp E i)

/-! ### The induction lemma -/

/-- SVT-7 (induction lemma, GSLW Thm 17 proof). The alternating sequence acts on the right
singular vector `ψ = rv E i` as the QSP sequence `seqR Φ σ` acts on the first standard basis
vector, in the `Π`-frame `{ψ, ψ⊥}` for even `Φ.length` and in the `Π̃`-frame `{ψ̃, ψ̃⊥}` for odd
`Φ.length`:
```
U_Φ ψ = (seqR Φ σ)₀₀ ψ + (seqR Φ σ)₁₀ ψ⊥    (Φ.length even)
U_Φ ψ = (seqR Φ σ)₀₀ ψ̃ + (seqR Φ σ)₁₀ ψ̃⊥   (Φ.length odd)
```
Valid for every `i` (no restriction on `σ`). -/
theorem altSeq_apply_rv (Φ : List ℝ) (i : svIndex E) :
    altSeq E Φ (rv E i) =
      (seqR Φ (σ E i)) 0 0 • (if Even Φ.length then rv E i else lv E i) +
        (seqR Φ (σ E i)) 1 0 • (if Even Φ.length then rvp E i else lvt E i) := by
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    have hlen : Even (φ :: Φ).length ↔ ¬ Even Φ.length := by
      rw [List.length_cons]
      exact Nat.even_add_one
    rw [altSeq_cons, Module.End.mul_apply, ih, seqR_cons, phaseZ_mul_Rref_mul_apply_zero_zero,
      phaseZ_mul_Rref_mul_apply_one_zero]
    by_cases h : Even Φ.length
    · have h' : ¬ Even (φ :: Φ).length := fun h2 => hlen.mp h2 h
      rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_right h', ite_eq_right h',
        Module.End.mul_apply, map_add, map_smul, map_smul, U_rv E i, U_rvp E i]
      simp only [map_add, map_sub, map_smul, phaseOp_P'_lv E i, phaseOp_P'_lvt E i]
      module
    · have h' : Even (φ :: Φ).length := hlen.mpr h
      rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_left h', ite_eq_left h',
        Module.End.mul_apply, map_add, map_smul, map_smul, U_adjoint_lv E i, U_adjoint_lvt E i]
      simp only [map_add, map_sub, map_smul, phaseOp_P_rv E i, phaseOp_P_rvp E i]
      module

/-! ### The headline: projections of `U_Φ ψ` -/

/-- SVT-7 (vector form, odd length). `Π̃ U_Φ ψ = (seqR Φ σ)₀₀ ψ̃` for odd `Φ.length`, for every
`i` (for `σ = 0` both sides vanish: `ψ̃ = 0` and `P_Φ(0) = 0` for odd `P_Φ`). -/
theorem proj_altSeq_apply_rv_odd {Φ : List ℝ} (hodd : Odd Φ.length) (i : svIndex E) :
    E.P' (altSeq E Φ (rv E i)) = (seqR Φ (σ E i)) 0 0 • lv E i := by
  have h : ¬ Even Φ.length := Nat.not_even_iff_odd.mpr hodd
  rw [altSeq_apply_rv, ite_eq_right h, ite_eq_right h, map_add, map_smul, map_smul, P'_lv,
    P'_lvt, smul_zero, add_zero]

/-- SVT-7 (vector form, even length). `Π U_Φ ψ = (seqR Φ σ)₀₀ ψ` for even `Φ.length`, for
every `i`. -/
theorem proj_altSeq_apply_rv_even {Φ : List ℝ} (heven : Even Φ.length) (i : svIndex E) :
    E.P (altSeq E Φ (rv E i)) = (seqR Φ (σ E i)) 0 0 • rv E i := by
  rw [altSeq_apply_rv, ite_eq_left heven, ite_eq_left heven, map_add, map_smul, map_smul, P_rv,
    P_rvp, smul_zero, add_zero]

/-- SVT-7 (vector form, odd length, polynomial). `Π̃ U_Φ ψ = P_Φ(σ) ψ̃` with
`(P_Φ, Q_Φ) = qspPoly Φ` (GSLW Thm 17 on one singular vector, odd case). -/
theorem proj_altSeq_apply_rv_odd_eval {Φ : List ℝ} (hodd : Odd Φ.length) (i : svIndex E) :
    E.P' (altSeq E Φ (rv E i)) = ((qspPoly Φ).1.eval (σ E i : ℂ)) • lv E i := by
  rw [proj_altSeq_apply_rv_odd E hodd i, seqR_apply_zero_zero (σ_mem_Icc_neg_one_one E i) Φ]

/-- SVT-7 (vector form, even length, polynomial). `Π U_Φ ψ = P_Φ(σ) ψ` with
`(P_Φ, Q_Φ) = qspPoly Φ` (GSLW Thm 17 on one singular vector, even case). -/
theorem proj_altSeq_apply_rv_even_eval {Φ : List ℝ} (heven : Even Φ.length) (i : svIndex E) :
    E.P (altSeq E Φ (rv E i)) = ((qspPoly Φ).1.eval (σ E i : ℂ)) • rv E i := by
  rw [proj_altSeq_apply_rv_even E heven i, seqR_apply_zero_zero (σ_mem_Icc_neg_one_one E i) Φ]

end TwoFrame

end QSVT.SVT
