/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.QET
import QSVT.SVT.RealPoly
import QSVT.Encoding.LCUm
import QSVT.Polynomial.ChebCoeff

/-!
# Route A: the exact Chebyshev-LCU implementation of a polynomial (formal-spec CERT-A)

Let `E : HermitianEncoding ℋ` with encoded operator `A = Π U Π = A†` and let
`f = ∑_{k<m} c_k T_k` be a polynomial given by its Chebyshev coefficients `c : Fin m → ℂ`.
Route A implements `f(A)` *exactly* (no numerics, no phase-finding) by

1. the closed-form phases of QSP-4: `chebUnitary E k = U_{chebPhases k}` satisfies
   `Π U_{chebPhases k} Π = T_k(A) Π` (SVT-3, `qet_chebyshev`), using `k` queries to `U`/`U†`;
2. the `m`-term LCU of ENC-3 with the Householder state preparation and the normalised
   coefficients `cNorm c k = c_k / ‖c‖₁`, the phases of the `c_k` being absorbed into the
   unitaries: `chebLCU E c = lcu (householder √‖cNorm c‖) (fun k => phase (cNorm c k) • U_k)`.

Compressing by `regP E = 1 ⊗ Π` on both sides and taking the `(0,0)` block gives
```
regTopLeft (regP E * chebLCU E c * regP E) = ‖c‖₁⁻¹ • (f(A) Π)
```
with zero error (`regTopLeft_regP_chebLCU_regP`). The computable front end `chebCoeffs l`
(POLY-6, `ChebQC.ofMonomials`) turns a polynomial `l : PolyQC` in the monomial basis into its
Chebyshev coefficients, and `routeA` is the resulting end-to-end statement for
`PolyQC.toPoly l`.

## Contents

* Register lemmas (ENC-2/3 helpers): `selectOp_const_mul_matOp`, `selectOp_const_mul_lcu_mul`,
  `regTopLeft_selectOp_const_mul_mul`, `lcu_adjoint`.
* `chebUnitary`, `chebUnitary_mem_unitary`, `P_chebUnitary_P`.
* `l1`, `l1_nonneg`, `cNorm`, `sum_norm_cNorm`.
* `regP`, `regP_isProjective`, `chebLCU`, `chebLCU_mem_unitary`, `regP_chebLCU_regP_eq`,
  `regTopLeft_regP_chebLCU_regP` (CERT-A main theorem).
* `chebEncoding` (a `ProjUnitaryEncoding (Reg m ℋ)`), `chebEncoding_regTopLeft_encoded`, and for
  real coefficients `chebHermitianEncoding` (a `HermitianEncoding (Reg m ℋ)`).
* `chebCoeffs`, `sum_C_chebCoeffs_mul_T`, `routeA`.
* `routeA_queries`, `routeA_queries_eq` (the query count `∑_{k<m} k = m(m-1)/2`).

## Resource count

`chebLCU E c` on `Reg m ℋ` uses the ancilla register `ℂ^m`, two ancilla gates `householder`
(`V ⊗ 1` and `Vᴴ ⊗ 1`), and `∑_{k<m} k = m(m-1)/2` controlled uses of `U`/`U†` in total, since
`altSeq (chebPhases k)` uses `k` of them (`chebPhases_length`); see `routeA_queries`. The
circuit-level formalisation of this count is IR-2.

## Mathlib API used

`Fin.sum_univ_eq_sum_range`, `Finset.sum_range_id`, `Algebra.smul_def`, `Polynomial.aeval_C`,
`Finset.smul_sum`, `Finset.sum_mul`, `smul_mul_assoc`, `mul_smul_comm`, `star_smul`
(`StarModule ℂ (L ℋ)`), `LinearMap.isSelfAdjoint_iff'`, `Complex.conj_eq_iff_im`,
`Complex.div_ofReal_im`, `Real.norm_of_nonneg`, `Complex.norm_real`.
-/

namespace QSVT.Pipeline

open QSVT.SVT QSVT.Encoding QSVT.QSP QSVT.Poly QuantumState
open Polynomial
open scoped Matrix
-- Only `T` is opened: `Polynomial.Chebyshev.C` (third kind) would shadow `Polynomial.C`.
open Polynomial.Chebyshev (T)

universe u

variable {ℋ : Type u} [Qudit ℋ] {m : ℕ}

/-! ### Register lemmas (helpers for ENC-2/3; candidates for `QSVT.Encoding.LCUm`) -/

section Register

variable (P : L ℋ) (V : Matrix (Fin m) (Fin m) ℂ) (W : Fin m → L ℋ)

/-- CERT-A (ENC-2 helper). `1 ⊗ P` commutes with every ancilla gate `V ⊗ 1`. -/
theorem selectOp_const_mul_matOp :
    (selectOp fun _ : Fin m => P) * matOp V = matOp V * (selectOp fun _ : Fin m => P) :=
  LinearMap.ext fun v => ext_reg fun j => by
    simp only [Module.End.mul_apply, proj_selectOp, proj_matOp, map_sum, map_smul]

/-- CERT-A (ENC-3 helper). Compressing the LCU circuit by `1 ⊗ P` on both sides compresses
every unitary: `(1 ⊗ P) lcu V W (1 ⊗ P) = lcu V (fun k => P Wₖ P)`. -/
theorem selectOp_const_mul_lcu_mul :
    (selectOp fun _ : Fin m => P) * lcu V W * (selectOp fun _ : Fin m => P) =
      lcu V fun k => P * W k * P := by
  set S : L (Reg m ℋ) := selectOp fun _ : Fin m => P with hS
  have hA : S * matOp Vᴴ = matOp Vᴴ * S := selectOp_const_mul_matOp P Vᴴ
  have hB : matOp V * S = S * matOp V := (selectOp_const_mul_matOp P V).symm
  calc S * (matOp Vᴴ * selectOp W * matOp V) * S
      = (S * matOp Vᴴ) * selectOp W * (matOp V * S) := by simp only [mul_assoc]
    _ = (matOp Vᴴ * S) * selectOp W * (S * matOp V) := by rw [hA, hB]
    _ = matOp Vᴴ * (S * selectOp W * S) * matOp V := by simp only [mul_assoc]
    _ = lcu V fun k => P * W k * P := by rw [hS, selectOp_const_mul_selectOp_mul, lcu]

/-- CERT-A (ENC-3 helper). The adjoint of the LCU circuit is the LCU circuit of the adjoints,
with the same state preparation: `(lcu V W)† = lcu V (fun k => Wₖ†)`. -/
theorem lcu_adjoint : (lcu V W)† = lcu V fun k => (W k)† := by
  rw [lcu, lcu, ← LinearMap.star_eq_adjoint, star_mul, star_mul]
  simp only [LinearMap.star_eq_adjoint, matOp_adjoint, selectOp_adjoint,
    Matrix.conjTranspose_conjTranspose, mul_assoc]

variable [NeZero m]

/-- CERT-A (ENC-2 helper). The `(0,0)` block of `(1 ⊗ P) T (1 ⊗ P)` is `P (T₀₀) P`. -/
theorem regTopLeft_selectOp_const_mul_mul (T : L (Reg m ℋ)) :
    regTopLeft ((selectOp fun _ : Fin m => P) * T * (selectOp fun _ : Fin m => P)) =
      P * regTopLeft T * P :=
  LinearMap.ext fun x => by
    simp only [regTopLeft_apply, Module.End.mul_apply, selectOp_inj, proj_selectOp]

end Register

/-! ### The Chebyshev unitaries `U_{chebPhases k}` -/

section ChebUnitary

variable (E : HermitianEncoding ℋ)

/-- CERT-A. The alternating phase sequence with the closed-form Chebyshev phases of QSP-4:
`chebUnitary E k = U_{chebPhases k}`, using `k` queries to `U`/`U†`. -/
noncomputable def chebUnitary (k : ℕ) : L ℋ := altSeq E.toProjUnitaryEncoding (chebPhases k)

/-- CERT-A. `U_{chebPhases k}` is unitary. -/
theorem chebUnitary_mem_unitary (k : ℕ) : chebUnitary E k ∈ unitary (L ℋ) :=
  altSeq_mem_unitary _ _

/-- CERT-A (= SVT-3 `qet_chebyshev`). `Π U_{chebPhases k} Π = T_k(A) Π`. -/
theorem P_chebUnitary_P (k : ℕ) :
    E.P * chebUnitary E k * E.P = aeval E.encoded (T ℂ k) * E.P :=
  qet_chebyshev E k

end ChebUnitary

/-! ### Coefficient normalisation -/

section Coefficients

variable (c : Fin m → ℂ)

/-- CERT-A. The `ℓ¹` norm `‖c‖₁ = ∑ₖ ‖cₖ‖` of a coefficient vector. -/
noncomputable def l1 : ℝ := ∑ k, ‖c k‖

theorem l1_nonneg : 0 ≤ l1 c := Finset.sum_nonneg fun k _ => norm_nonneg (c k)

/-- CERT-A. The normalised coefficients `cₖ / ‖c‖₁`. -/
noncomputable def cNorm (k : Fin m) : ℂ := c k / (l1 c : ℂ)

/-- CERT-A. The normalised coefficients have `ℓ¹` norm `1` when `‖c‖₁ ≠ 0`. -/
theorem sum_norm_cNorm (h : l1 c ≠ 0) : ∑ k, ‖cNorm c k‖ = 1 := by
  have h1 : ∀ k, ‖cNorm c k‖ = ‖c k‖ * (l1 c)⁻¹ := fun k => by
    rw [cNorm, norm_div, Complex.norm_real, Real.norm_of_nonneg (l1_nonneg c), div_eq_mul_inv]
  simp only [h1, ← Finset.sum_mul]
  exact mul_inv_cancel₀ h

/-- CERT-A. The normalised coefficients of a real coefficient vector are real. -/
theorem cNorm_im_eq_zero (hc : ∀ k, (c k).im = 0) (k : Fin m) : (cNorm c k).im = 0 := by
  rw [cNorm, Complex.div_ofReal_im, hc k, zero_div]

end Coefficients

/-- CERT-A. The phase `z / ‖z‖` of a real number is real. -/
theorem phase_im_eq_zero {z : ℂ} (hz : z.im = 0) : (phase z).im = 0 := by
  unfold phase
  split_ifs with h
  · exact Complex.one_im
  · rw [Complex.div_ofReal_im, hz, zero_div]

/-! ### The Route A circuit -/

section RegP

variable (E : HermitianEncoding ℋ)

/-- CERT-A. The compressing projector `1 ⊗ Π` on the register `Reg m ℋ`. -/
noncomputable def regP : L (Reg m ℋ) := selectOp fun _ : Fin m => E.P

/-- CERT-A. `1 ⊗ Π` is an orthogonal projection. -/
theorem regP_isProjective : IsProjective (regP (m := m) E) := selectOp_const_isProjective E.hP

end RegP

section RouteA

variable [NeZero m] (E : HermitianEncoding ℋ) (c : Fin m → ℂ)

/-- CERT-A. The Route A unitary: the `m`-term LCU (ENC-3, Householder state preparation) of
the Chebyshev unitaries `U_{chebPhases k}` with the normalised coefficients `cNorm c`, whose
phases are absorbed into the unitaries. It uses `∑_{k<m} k` queries to `U`/`U†`
(`routeA_queries`). -/
noncomputable def chebLCU : L (Reg m ℋ) :=
  lcu (householder fun k => ((Real.sqrt ‖cNorm c k‖ : ℝ) : ℂ))
    fun k => phase (cNorm c k) • chebUnitary E k

/-- CERT-A. The Route A unitary is unitary. -/
theorem chebLCU_mem_unitary : chebLCU E c ∈ unitary (L (Reg m ℋ)) :=
  lcu_complex_mem_unitary _ _ fun k => chebUnitary_mem_unitary E k

/-- CERT-A. Compressing the Route A unitary by `1 ⊗ Π` replaces every `U_{chebPhases k}` by
`T_k(A) Π` (SVT-3). -/
theorem regP_chebLCU_regP_eq :
    regP E * chebLCU E c * regP E =
      lcu (householder fun k => ((Real.sqrt ‖cNorm c k‖ : ℝ) : ℂ))
        fun k => phase (cNorm c k) • (aeval E.encoded (T ℂ k) * E.P) := by
  rw [regP, chebLCU, selectOp_const_mul_lcu_mul]
  congr 1
  funext k
  rw [mul_smul_comm, smul_mul_assoc, P_chebUnitary_P]

/-- CERT-A (main theorem). The `(0,0)` block of the compressed Route A unitary is
`‖c‖₁⁻¹ • f(A) Π` for `f = ∑ₖ cₖ T_k`, exactly:
```
(⟨0| ⊗ Π) chebLCU E c (|0⟩ ⊗ Π) = ‖c‖₁⁻¹ • (∑ₖ cₖ T_k)(A) Π.
```
-/
theorem regTopLeft_regP_chebLCU_regP (h : l1 c ≠ 0) :
    regTopLeft (regP E * chebLCU E c * regP E) =
      ((l1 c : ℂ)⁻¹) • (aeval E.encoded (∑ k, C (c k) * T ℂ (k : ℕ)) * E.P) := by
  rw [regP_chebLCU_regP_eq, lcu_complex _ _ (sum_norm_cNorm c h)]
  simp only [map_sum, map_mul, aeval_C, ← Algebra.smul_def, Finset.sum_mul, smul_mul_assoc,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cNorm, div_eq_inv_mul]

/-! ### Packaging as an encoding on `Reg m ℋ` -/

/-- CERT-A. The Route A circuit as a projected unitary encoding on `Reg m ℋ`: the unitary is
`chebLCU E c` and both projections are `1 ⊗ Π`. Its encoded operator has `(0,0)` block
`‖c‖₁⁻¹ • f(A) Π` (`chebEncoding_regTopLeft_encoded`). -/
noncomputable def chebEncoding : ProjUnitaryEncoding (Reg m ℋ) where
  U := chebLCU E c
  hU := chebLCU_mem_unitary E c
  P := regP E
  P' := regP E
  hP := regP_isProjective E
  hP' := regP_isProjective E

@[simp] theorem chebEncoding_U : (chebEncoding E c).U = chebLCU E c := rfl

@[simp] theorem chebEncoding_P : (chebEncoding E c).P = regP E := rfl

@[simp] theorem chebEncoding_P' : (chebEncoding E c).P' = regP E := rfl

/-- CERT-A. The `(0,0)` block of the encoded operator of `chebEncoding E c` is
`‖c‖₁⁻¹ • f(A) Π` for `f = ∑ₖ cₖ T_k`. -/
theorem chebEncoding_regTopLeft_encoded (h : l1 c ≠ 0) :
    regTopLeft (chebEncoding E c).encoded =
      ((l1 c : ℂ)⁻¹) • (aeval E.encoded (∑ k, C (c k) * T ℂ (k : ℕ)) * E.P) :=
  regTopLeft_regP_chebLCU_regP E c h

/-- CERT-A. `T_k` has real coefficients: `(T_k)^* = T_k`. -/
theorem conjP_T (k : ℕ) : conjP (T ℂ k) = T ℂ k := by
  rw [← rePoly_chebyshev k, conjP_rePoly]

/-- CERT-A. `T_k(A) Π` is self-adjoint for a Hermitian encoding. -/
theorem aeval_T_mul_P_adjoint (k : ℕ) :
    (aeval E.encoded (T ℂ k) * E.P)† = aeval E.encoded (T ℂ k) * E.P := by
  rw [← LinearMap.star_eq_adjoint, star_mul, E.hP.isSelfAdjoint.star_eq,
    LinearMap.star_eq_adjoint, aeval_adjoint, conjP_T, P_mul_aeval]

/-- CERT-A. For real coefficients the Route A circuit is a *Hermitian* encoding on `Reg m ℋ`:
the compressed operator `(1 ⊗ Π) chebLCU E c (1 ⊗ Π)` is self-adjoint, because each
`phase (cNorm c k) • T_k(A) Π` is (real phase, real polynomial, `Π` commutes with `T_k(A)`). -/
noncomputable def chebHermitianEncoding (hc : ∀ k, (c k).im = 0) :
    HermitianEncoding (Reg m ℋ) where
  toProjUnitaryEncoding := chebEncoding E c
  P'_eq := rfl
  encoded_selfAdjoint := by
    rw [chebEncoding_P', chebEncoding_U, chebEncoding_P, regP_chebLCU_regP_eq,
      LinearMap.isSelfAdjoint_iff', lcu_adjoint]
    congr 1
    funext k
    rw [← LinearMap.star_eq_adjoint, star_smul, LinearMap.star_eq_adjoint,
      aeval_T_mul_P_adjoint, Complex.star_def,
      Complex.conj_eq_iff_im.mpr (phase_im_eq_zero (cNorm_im_eq_zero c hc k))]

@[simp] theorem chebHermitianEncoding_toProjUnitaryEncoding (hc : ∀ k, (c k).im = 0) :
    (chebHermitianEncoding E c hc).toProjUnitaryEncoding = chebEncoding E c := rfl

/-- CERT-A. The `(0,0)` block of the encoded operator of `chebHermitianEncoding E c hc`. -/
theorem chebHermitianEncoding_regTopLeft_encoded (hc : ∀ k, (c k).im = 0) (h : l1 c ≠ 0) :
    regTopLeft (chebHermitianEncoding E c hc).encoded =
      ((l1 c : ℂ)⁻¹) • (aeval E.encoded (∑ k, C (c k) * T ℂ (k : ℕ)) * E.P) :=
  regTopLeft_regP_chebLCU_regP E c h

end RouteA

/-! ### Computable input: Chebyshev coefficients of a `PolyQC` -/

/-- CERT-A. The Chebyshev coefficients of a polynomial `l : PolyQC` in the monomial basis, as a
vector indexed by `Fin (ofMonomials l).length` (computed by POLY-6 `ChebQC.ofMonomials`). -/
noncomputable def chebCoeffs (l : PolyQC) : Fin (ChebQC.ofMonomials l).length → ℂ :=
  fun k => QC.toC ((ChebQC.ofMonomials l).getD k 0)

/-- CERT-A. `∑ₖ (chebCoeffs l)ₖ T_k = ∑ᵢ lᵢ Xⁱ` (POLY-6 `toPoly_ofMonomials`). -/
theorem sum_C_chebCoeffs_mul_T (l : PolyQC) :
    ∑ k : Fin (ChebQC.ofMonomials l).length, C (chebCoeffs l k) * T ℂ (k : ℕ) =
      PolyQC.toPoly l := by
  rw [← ChebQC.toPoly_ofMonomials, ChebQC.toPoly]
  exact Fin.sum_univ_eq_sum_range
    (fun k => C (QC.toC ((ChebQC.ofMonomials l).getD k 0)) * T ℂ k) _

section RouteA

variable (E : HermitianEncoding ℋ)

/-- CERT-A (Route A, end to end). For a polynomial `l : PolyQC` in the monomial basis with
Chebyshev coefficients `c = chebCoeffs l` (POLY-6) and a Hermitian encoding `E` of `A`,
```
(⟨0| ⊗ Π) chebLCU E c (|0⟩ ⊗ Π) = ‖c‖₁⁻¹ • l(A) Π
```
exactly, using `∑_{k < length} k` queries to `U`/`U†` (`routeA_queries`). -/
theorem routeA (l : PolyQC) [NeZero (ChebQC.ofMonomials l).length]
    (h : l1 (chebCoeffs l) ≠ 0) :
    regTopLeft (regP E * chebLCU E (chebCoeffs l) * regP E) =
      ((l1 (chebCoeffs l) : ℂ)⁻¹) • (aeval E.encoded (PolyQC.toPoly l) * E.P) := by
  rw [regTopLeft_regP_chebLCU_regP E _ h, sum_C_chebCoeffs_mul_T]

end RouteA

/-! ### Resource count -/

/-- CERT-A. The number of uses of `U` and `U†` in `chebLCU E c` for `c : Fin m → ℂ`:
the `k`-th branch `altSeq E (chebPhases k)` uses `k` of them (`chebPhases_length`), so the
select operator uses `∑_{k<m} k` controlled queries in total. (Statement of the count only;
the circuit-level formalisation is IR-2.) -/
def routeA_queries (m : ℕ) : ℕ := ∑ k ∈ Finset.range m, k

/-- CERT-A. `routeA_queries m = m (m - 1) / 2` (Gauss sum). -/
theorem routeA_queries_eq (m : ℕ) : routeA_queries m = m * (m - 1) / 2 :=
  Finset.sum_range_id m

end QSVT.Pipeline
