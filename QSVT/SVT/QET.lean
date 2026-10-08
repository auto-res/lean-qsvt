/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import QSVT.SVT.TwoVector
import QSVT.SVT.EigenBasis
import QSVT.QSP.Chebyshev

/-!
# QET: eigenvalue transformation for Hermitian block encodings (formal-spec SVT-3)

Let `E : HermitianEncoding ℋ` with `U`, `Π` and encoded operator `A = Π U Π = A†`, and let
`Φ` be a phase list with QSP polynomial `P_Φ = (qspPoly Φ).1`. The quantum eigenvalue
transformation (QET, GSLW Thm 17 in the Hermitian case `Π̃ = Π`) states
```
Π U_Φ Π = P_Φ(A) Π          (`qet`)
```
where `U_Φ = altSeq E Φ` is the alternating phase sequence (SVT-1).

The proof assembles the two preceding modules: on each eigenvector `ψᵢ` of `A|_{ran Π}`
(`QSVT.SVT.EigenBasis`) the two-vector lemma gives `Π U_Φ ψᵢ = P_Φ(ςᵢ) ψᵢ`
(`proj_altSeq_apply_eigen_eval`, `QSVT.SVT.TwoVector`), while `P_Φ(A) ψᵢ = P_Φ(ςᵢ) ψᵢ`
(`aeval_eigenVec`); the extensionality principle `ext_mul_P_of_eigenVec` then upgrades the
pointwise agreement to the operator identity after `Π`.

The Chebyshev instance (`qet_chebyshev`) uses the phases of QSP-4: `P_{chebPhases d} = T_d`
as polynomials over `ℂ` (`qspPoly_chebPhases`), because both agree on the infinite set
`[-1, 1] ⊆ ℝ ⊆ ℂ` (`Polynomial.eq_of_infinite_eval_eq`).

## Resource count

`altSeq E Φ` contains exactly `Φ.length` uses of `U` or `U†` (alternating, starting with
`U` from the right), and `Φ.length` phase operators `e^{iφ(2Π-I)}`. The circuit-level
formalisation of this count is IR-2; nothing is proved about it here.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

section QET

variable (E : HermitianEncoding ℋ)

/-- SVT-3 (QET, GSLW Thm 17 for Hermitian encodings with `Π̃ = Π`). For a Hermitian projected
unitary encoding `E` with encoded operator `A = Π U Π` and any phase list `Φ`,
```
Π U_Φ Π = P_Φ(A) Π,
```
where `U_Φ = altSeq E Φ` and `P_Φ = (qspPoly Φ).1` is the QSP polynomial of `Φ` (QSP-3).
The alternating sequence `U_Φ` uses `U` and `U†` a total of `Φ.length` times (IR-2 will
formalise this resource count). -/
theorem qet (Φ : List ℝ) :
    E.P * altSeq E.toProjUnitaryEncoding Φ * E.P =
      Polynomial.aeval E.encoded (qspPoly Φ).1 * E.P := by
  refine ext_mul_P_of_eigenVec E fun i => ?_
  rw [Module.End.mul_apply, aeval_eigenVec,
    proj_altSeq_apply_eigen_eval E (P_eigenVec E i) (encoded_eigenVec E i)
      (eigenValue_mem_Icc E i) Φ]

/-- SVT-3 (QET, vector form). `Π U_Φ (Π x) = P_Φ(A) (Π x)` for every `x`. -/
theorem qet_apply (Φ : List ℝ) (x : ℋ) :
    E.P (altSeq E.toProjUnitaryEncoding Φ (E.P x)) =
      Polynomial.aeval E.encoded (qspPoly Φ).1 (E.P x) :=
  LinearMap.congr_fun (qet E Φ) x

end QET

/-! ### The Chebyshev instance -/

/-- SVT-3 (Chebyshev instance, polynomial identity). The QSP polynomial of the phases
`chebPhases d` of QSP-4 is the Chebyshev polynomial `T_d` over `ℂ`: both agree on the infinite
set `[-1, 1]` (`seqR_chebPhases`, `seqR_apply_zero_zero`), hence everywhere. -/
theorem qspPoly_chebPhases (d : ℕ) :
    (qspPoly (chebPhases d)).1 = Polynomial.Chebyshev.T ℂ d := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injOn_mapsTo (f := ((↑) : ℝ → ℂ)) (s := Set.Icc (-1 : ℝ) 1)
    Complex.ofReal_injective.injOn (fun x hx => ?_) (Set.Icc_infinite (by norm_num))
  change (qspPoly (chebPhases d)).1.eval (x : ℂ) = (Polynomial.Chebyshev.T ℂ d).eval (x : ℂ)
  rw [← seqR_apply_zero_zero hx, seqR_chebPhases hx]

section QET

variable (E : HermitianEncoding ℋ)

/-- SVT-3 (QET, Chebyshev instance; GSLW Thm 17 with the phases of Lemma 9). For a Hermitian
encoding `E` and the phases `chebPhases d`,
```
Π U_{chebPhases d} Π = T_d(A) Π,
```
using `d` queries to `U`/`U†` in total. -/
theorem qet_chebyshev (d : ℕ) :
    E.P * altSeq E.toProjUnitaryEncoding (chebPhases d) * E.P =
      Polynomial.aeval E.encoded (Polynomial.Chebyshev.T ℂ d) * E.P := by
  rw [qet E (chebPhases d), qspPoly_chebPhases]

end QET

end QSVT.SVT
