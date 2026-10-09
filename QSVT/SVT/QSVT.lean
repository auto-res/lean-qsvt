/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.TwoFrame

/-!
# QSVT: the quantum singular value transformation (formal-spec SVT-7, GSLW Theorem 17)

Let `E : ProjUnitaryEncoding ℋ` with `U`, `Π`, `Π̃` and encoded operator `A = Π̃ U Π`, and let
`Φ` be a phase list with QSP polynomial `P_Φ = (qspPoly Φ).1` (QSP-3). The quantum singular
value transformation theorem (GSLW Thm 17) states
```
Π̃ U_Φ Π = P_Φ^{(SV)}(A)     (Φ.length odd,  `qsvt_odd`)
Π  U_Φ Π = P_Φ^{(SV)}(A)     (Φ.length even, `qsvt_even`)
```
where `U_Φ = altSeq E Φ` is the alternating phase sequence (SVT-1) and
`P^{(SV)}(A) = svTransform P E` is the SVD-free singular value transformation of SVT-5.

The proof assembles the two preceding modules. Both sides are supported on `ran Π` (right
factor `Π`, `svTransform_mul_P`), so by `ext_mul_P_of_rv` (`QSVT.SVT.SVD`) it suffices to compare
them on the right singular vectors `ψᵢ`: the two-frame lemma gives `Π̃ U_Φ ψᵢ = P_Φ(σᵢ) ψ̃ᵢ`
resp. `Π U_Φ ψᵢ = P_Φ(σᵢ) ψᵢ` (`proj_altSeq_apply_rv_odd_eval`, `proj_altSeq_apply_rv_even_eval`,
`QSVT.SVT.TwoFrame`), while `svTransform P_Φ E ψᵢ` is the same vector because `P_Φ` has the
parity of `Φ.length` (`hasParity_fst`, `svTransform_apply_rv_of_isOdd/isEven`).

For a Hermitian encoding (`Π̃ = Π`, `A† = A`) the theorem specialises to the eigenvalue
transformation `qet` of SVT-3 through `svTransform_eq_aeval` (`qsvt_hermitian`, `qet_of_qsvt`).
The single-phase instance `Π̃ e^{iφ(2Π̃-I)} U Π = e^{iφ} A` is `qsvt_single`.

## Resource count

`altSeq E Φ` contains exactly `Φ.length` uses of `U` or `U†` (alternating, starting with `U`
from the right) and `Φ.length` phase operators; the circuit-level count is IR-2.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.QSP QSVT.Poly Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

section QSVT

variable (E : ProjUnitaryEncoding ℋ)

/-- SVT-7 (QSVT, GSLW Thm 17, odd case). For a projected unitary encoding `E` with encoded
operator `A = Π̃ U Π` and a phase list `Φ` of odd length,
```
Π̃ U_Φ Π = P_Φ^{(SV)}(A) = svTransform P_Φ E,
```
where `U_Φ = altSeq E Φ` and `P_Φ = (qspPoly Φ).1` is the (odd) QSP polynomial of `Φ`. -/
theorem qsvt_odd {Φ : List ℝ} (hodd : Odd Φ.length) :
    E.P' * altSeq E Φ * E.P = svTransform (qspPoly Φ).1 E := by
  rw [← svTransform_mul_P E (qspPoly Φ).1]
  refine ext_mul_P_of_rv E fun i => ?_
  rw [Module.End.mul_apply, proj_altSeq_apply_rv_odd_eval E hodd i,
    svTransform_apply_rv_of_isOdd E ((hasParity_fst Φ).isOdd hodd) i]

/-- SVT-7 (QSVT, GSLW Thm 17, even case). For a phase list `Φ` of even length,
```
Π U_Φ Π = P_Φ^{(SV)}(A) = svTransform P_Φ E,
```
with `P_Φ = (qspPoly Φ).1` the (even) QSP polynomial of `Φ`. -/
theorem qsvt_even {Φ : List ℝ} (heven : Even Φ.length) :
    E.P * altSeq E Φ * E.P = svTransform (qspPoly Φ).1 E := by
  rw [← svTransform_mul_P E (qspPoly Φ).1]
  refine ext_mul_P_of_rv E fun i => ?_
  rw [Module.End.mul_apply, proj_altSeq_apply_rv_even_eval E heven i,
    svTransform_apply_rv_of_isEven E ((hasParity_fst Φ).isEven heven) i]

/-- SVT-7 (QSVT, both parities). `Π_out U_Φ Π = P_Φ^{(SV)}(A)` with `Π_out = Π` for even
`Φ.length` and `Π_out = Π̃` for odd `Φ.length`. -/
theorem qsvt (Φ : List ℝ) :
    (if Even Φ.length then E.P else E.P') * altSeq E Φ * E.P = svTransform (qspPoly Φ).1 E := by
  by_cases h : Even Φ.length
  · rw [ite_eq_left h]
    exact qsvt_even E h
  · rw [ite_eq_right h]
    exact qsvt_odd E (Nat.not_even_iff_odd.mp h)

/-- SVT-7 (QSVT, odd case, vector form). `Π̃ U_Φ (Π x) = P_Φ^{(SV)}(A) (Π x)` for every `x`. -/
theorem qsvt_odd_apply {Φ : List ℝ} (hodd : Odd Φ.length) (x : ℋ) :
    E.P' (altSeq E Φ (E.P x)) = svTransform (qspPoly Φ).1 E (E.P x) := by
  have h := LinearMap.congr_fun (qsvt_odd E hodd) x
  rwa [← svTransform_mul_P E (qspPoly Φ).1] at h

/-- SVT-7 (QSVT, even case, vector form). `Π U_Φ (Π x) = P_Φ^{(SV)}(A) (Π x)` for every `x`. -/
theorem qsvt_even_apply {Φ : List ℝ} (heven : Even Φ.length) (x : ℋ) :
    E.P (altSeq E Φ (E.P x)) = svTransform (qspPoly Φ).1 E (E.P x) := by
  have h := LinearMap.congr_fun (qsvt_even E heven) x
  rwa [← svTransform_mul_P E (qspPoly Φ).1] at h

/-- SVT-7 (single phase, GSLW Def 15 with `n = 1`). `Π̃ e^{iφ(2Π̃-I)} U Π = e^{iφ} A`, since
`P_{[φ]} = e^{iφ} X` and `svTransform X E = A`. -/
theorem qsvt_single (φ : ℝ) :
    E.P' * (phaseOp E.P' φ * E.U) * E.P = Complex.exp (Complex.I * φ) • E.encoded := by
  have h := qsvt_odd E (Φ := [φ]) odd_one
  rw [altSeq_one, qspPoly_cons, qspPoly_nil] at h
  simp only [mul_one, mul_zero, add_zero] at h
  rwa [C_mul', svTransform_smul, svTransform_X] at h

end QSVT

/-! ### The Hermitian specialisation: QSVT recovers QET (SVT-3) -/

section Hermitian

variable (E : HermitianEncoding ℋ)

/-- SVT-7 (Hermitian case). For a Hermitian encoding (`Π̃ = Π`) both parities read
`Π U_Φ Π = svTransform P_Φ E`. -/
theorem qsvt_hermitian (Φ : List ℝ) :
    E.P * altSeq E.toProjUnitaryEncoding Φ * E.P =
      svTransform (qspPoly Φ).1 E.toProjUnitaryEncoding := by
  rcases Nat.even_or_odd Φ.length with h | h
  · exact qsvt_even E.toProjUnitaryEncoding h
  · have h' := qsvt_odd E.toProjUnitaryEncoding h
    rwa [E.P'_eq] at h'

/-- SVT-7 ⇒ SVT-3. For a Hermitian encoding the general QSVT theorem gives back the eigenvalue
transformation `Π U_Φ Π = P_Φ(A) Π` of `qet`, via `svTransform_eq_aeval`. -/
theorem qet_of_qsvt (Φ : List ℝ) :
    E.P * altSeq E.toProjUnitaryEncoding Φ * E.P =
      Polynomial.aeval E.encoded (qspPoly Φ).1 * E.P := by
  rw [qsvt_hermitian E Φ, svTransform_eq_aeval E]

end Hermitian

end QSVT.SVT
