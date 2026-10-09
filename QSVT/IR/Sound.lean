/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.IR.Denote

/-!
# Soundness of the IR denotation (formal-spec IR-1)

For a well-scaled program `e` over a Hermitian oracle encoding `E₀` of `A₀ = Π U₀ Π`, the base
block of the denotation is the specified polynomial of the oracle operator:
```
base E₀ e = compress e (denote E₀ e).encoded = (scale e)⁻¹ • (spec e)(A₀) Π     (`base_eq_smul`)
```
equivalently `base E₀ e = (normSpec e)(A₀) Π` (`base_eq`). This is the composition theorem for
the two step combinators (GSLW Cor 18 for `qsvtReal`, CERT-A for `chebLCU`), and it justifies
the recursive definition of `spec` in `QSVT.IR.Expr`.

## Proof

The induction needs a stronger statement, `compress_aeval_mul_P`: for *every* polynomial `q`,
```
compress e (q(Aₑ) Πₑ) = (q.comp (normSpec e))(A₀) Π        (Aₑ, Πₑ the encoded operator and
                                                             projector of `denote E₀ e`)
```
because a step applies QET-type identities to polynomials of the *inner* encoded operator. Both
steps produce an encoded operator of the form `|0⟩⟨0| ⊗ (r(Aₑ) Πₑ)` with projector
`|0⟩⟨0| ⊗ Πₑ` (SVT-8 `qsvtReal_encoded`, and `chebEnc0_encoded` with the corrected projector of
`QSVT.IR.Denote`), so a polynomial of it is `|0⟩⟨0| ⊗ (q(r(Aₑ) Πₑ) Πₑ)` by
`aeval_blockDiag_zero_mul` / `aeval_atZero_mul`, whose `(0,0)` block is `(q.comp r)(Aₑ) Πₑ`
(`aeval_aeval_mul_P`, using that `Πₑ` commutes with polynomials of `Aₑ`, SVT-8 `P_mul_aeval`).
The induction hypothesis then applies to the polynomial `q.comp r`.

## Mathlib API used

`Polynomial.aeval_comp`, `Polynomial.comp_assoc`, `Polynomial.mul_comp`, `Polynomial.C_comp`,
`Polynomial.X_comp`, `Polynomial.aeval_X`, `Polynomial.aeval_C`, `Algebra.smul_def`,
`Commute.mul_pow`, `IsIdempotentElem.pow_succ_eq`, `Polynomial.induction_on'`.
-/

namespace QSVT.IR

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP QSVT.Pipeline Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### Polynomials of `p(A) Π` -/

section Helpers

variable (E : HermitianEncoding ℋ)

/-- IR-1 (helper). `(p(A) Π)ⁿ Π = p(A)ⁿ Π`, since `Π` commutes with `p(A)` and `Π² = Π`. -/
theorem aeval_mul_P_pow_mul_P (r : ℂ[X]) (n : ℕ) :
    (aeval E.encoded r * E.P) ^ n * E.P = aeval E.encoded r ^ n * E.P := by
  have hcomm : Commute (aeval E.encoded r) E.P := (P_mul_aeval E r).symm
  rw [hcomm.mul_pow, mul_assoc, ← pow_succ, E.hP.isIdempotentElem.pow_succ_eq]

/-- IR-1 (helper). `q(p(A) Π) Π = (q ∘ p)(A) Π` for a Hermitian encoding. -/
theorem aeval_aeval_mul_P (r q : ℂ[X]) :
    aeval (aeval E.encoded r * E.P) q * E.P = aeval E.encoded (q.comp r) * E.P := by
  rw [aeval_comp]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, add_mul, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, mul_assoc, aeval_mul_P_pow_mul_P, mul_assoc]

/-- IR-1 (helper). `a • (f(A) Π) = (C a * f)(A) Π`. -/
theorem smul_aeval_mul_P (a : ℂ) (f : ℂ[X]) :
    a • (aeval E.encoded f * E.P) = aeval E.encoded (C a * f) * E.P := by
  rw [map_mul, aeval_C, Algebra.smul_def, mul_assoc]

end Helpers

/-! ### The soundness theorem -/

variable (E₀ : HermitianEncoding ℋ)

/-- IR-1 (soundness, polynomial form). For a well-scaled program `e` and every polynomial `q`,
the base block of `q(Aₑ) Πₑ` (with `Aₑ`, `Πₑ` the encoded operator and projector of
`denote E₀ e`) is `(q.comp (normSpec e))(A₀) Π`. -/
theorem compress_aeval_mul_P :
    ∀ (e : Expr), WellScaled e → ∀ q : ℂ[X],
      compress e (aeval (denote E₀ e).encoded q * (denote E₀ e).P) =
        aeval E₀.encoded (q.comp (normSpec e)) * E₀.P
  | .oracle, _, q => by
    rw [normSpec_oracle, comp_X]
    rfl
  | .qsvtReal Φ e, he, q => by
    have ih := compress_aeval_mul_P e he (q.comp (rePoly (qspPoly Φ).1))
    change compress e (topLeft (aeval ((denote E₀ e).qsvtReal Φ).encoded q *
      ((denote E₀ e).qsvtReal Φ).P)) = _
    rw [qsvtReal_encoded, qsvtReal_P, aeval_blockDiag_zero_mul, topLeft_blockDiag,
      aeval_aeval_mul_P, ih, normSpec_qsvtReal, comp_assoc]
  | .chebLCU c₀ c e, ⟨hc, he⟩, q => by
    have ih := compress_aeval_mul_P e he (q.comp (C ((chebScale c₀ c : ℂ)⁻¹) * chebPoly c₀ c))
    have hl1 : l1 (chebCoeffC c₀ c) ≠ 0 := by rw [l1_chebCoeffC]; exact hc
    unfold chebPoly at ih
    change compress e (regTopLeft
      (aeval (chebEnc0 (denote E₀ e) (chebCoeffC c₀ c) (chebCoeffC_im c₀ c)).encoded q *
        (chebEnc0 (denote E₀ e) (chebCoeffC c₀ c) (chebCoeffC_im c₀ c)).P)) = _
    rw [chebEnc0_encoded _ _ _ hl1, chebEnc0_P, aeval_atZero_mul, regTopLeft_atZero,
      l1_chebCoeffC, smul_aeval_mul_P, aeval_aeval_mul_P, ih, normSpec_chebLCU, comp_assoc,
      mul_comp, C_comp, chebPoly]

/-- IR-1. The *base block* of a program: the operator block-encoded by `denote E₀ e` on the
base space `ℋ`, i.e. `(⟨0| ⊗ I) (Πₑ Uₑ Πₑ) (|0⟩ ⊗ I)` with all ancillas in `|0⟩`. -/
noncomputable def base (e : Expr) : L ℋ := compress e (denote E₀ e).encoded

@[simp] theorem base_oracle : base E₀ .oracle = E₀.encoded := rfl

/-- IR-1 (soundness). The base block of a well-scaled program is the encoded polynomial of the
oracle operator: `base E₀ e = (normSpec e)(A₀) Π`. -/
theorem base_eq {e : Expr} (he : WellScaled e) :
    base E₀ e = aeval E₀.encoded (normSpec e) * E₀.P := by
  have h := compress_aeval_mul_P E₀ e he X
  rwa [aeval_X, X_comp, encoded_mul_P] at h

/-- IR-1 (soundness, GSLW form). `base E₀ e = (scale e)⁻¹ • (spec e)(A₀) Π`: the program
block-encodes `spec e (A₀)` with subnormalisation `scale e`. -/
theorem base_eq_smul {e : Expr} (he : WellScaled e) :
    base E₀ e = ((scale e : ℂ)⁻¹) • (aeval E₀.encoded (spec e) * E₀.P) := by
  rw [base_eq E₀ he, normSpec, smul_aeval_mul_P]

/-- IR-1 (sanity check). One QSVT step on the oracle block-encodes `Re[P_Φ](A₀) Π`, recovering
SVT-8 `topLeft_qsvtReal_encoded` (GSLW Cor 18). -/
theorem base_qsvtReal_oracle (Φ : List ℝ) :
    base E₀ (.qsvtReal Φ .oracle) = aeval E₀.encoded (rePoly (qspPoly Φ).1) * E₀.P := by
  rw [base_eq E₀ (e := .qsvtReal Φ .oracle) trivial, normSpec_qsvtReal, normSpec_oracle, comp_X]

end QSVT.IR
