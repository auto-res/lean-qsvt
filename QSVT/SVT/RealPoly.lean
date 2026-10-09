/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.QET
import QSVT.Encoding.LCU

/-!
# Real polynomials via the LCU of `U_Φ` and `U_{−Φ}` (formal-spec SVT-8, GSLW Cor 18)

Let `E : HermitianEncoding ℋ` with encoded operator `A = Π U Π = A†` and let `Φ` be a phase
list with QSP polynomial `P = P_Φ = (qspPoly Φ).1`. By QET (SVT-3), `Π U_Φ Π = P(A) Π`, and
since negating all phases conjugates the polynomial (`qspPoly_neg`, QSP-3 (iv)),
`Π U_{−Φ} Π = P^*(A) Π`. The two-term LCU of ENC-3 with the ancilla projector `|0⟩⟨0| ⊗ Π`
on both sides therefore encodes the *real part* `Re[P] = (P + P^*)/2` of `P`:
```
(|0⟩⟨0| ⊗ Π) lcu2 U_Φ U_{−Φ} (|0⟩⟨0| ⊗ Π) = |0⟩⟨0| ⊗ (Re[P](A) Π)        (`qet_real`)
```
which is GSLW Cor 18 in the Hermitian case `Π̃ = Π` (in GSLW's notation,
`(⟨+| ⊗ Π)(|0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ})(|+⟩ ⊗ Π) = Re[P](A)`).

## Contents

* `rePoly p = (1/2) • (p + conjP p)`, the coefficientwise real part, with `coeff_rePoly`,
  `conjP_rePoly`, `rePoly_eq_self_of_real`, `rePoly_map_ofReal`, `rePoly_chebyshev`,
  `natDegree_rePoly_le`, `eval_rePoly_ofReal`.
* Helpers for a Hermitian encoding: `P_mul_aeval` (`Π` commutes with `p(A)`), `aeval_adjoint`
  (`p(A)† = p^*(A)`), `aeval_rePoly_isSelfAdjoint`.
* `qet_real` / `topLeft_qet_real`: the Cor 18 identity above.
* `HermitianEncoding.qsvtReal E Φ : HermitianEncoding (Anc ℋ)`, the first encoding
  *combinator*: the LCU circuit together with the projection `|0⟩⟨0| ⊗ Π` is again a Hermitian
  encoding, of `Re[P_Φ](A)` (`qsvtReal_encoded`, `qsvtReal_encoded_chebyshev`).

## Resource count

`lcu2 U_Φ U_{−Φ}` uses one ancilla qubit, two ancilla Hadamards, and `Φ.length` controlled
uses of `U`/`U†` (`U_Φ` and `U_{−Φ}` run on the two branches of the ancilla; GSLW Cor 18 and
Lemma 19). The circuit-level formalisation of this count is IR-2.

## Mathlib API used

`Polynomial.induction_on'`, `Polynomial.aeval_monomial`, `Polynomial.map_monomial`,
`Algebra.algebraMap_eq_smul_one`, `Algebra.commute_algebraMap_left`, `algebraMap_star_comm`
(for the `StarModule ℂ (L ℋ)` instance), `LinearMap.isSelfAdjoint_iff'`,
`Polynomial.Chebyshev.map_T`, `Complex.add_conj`.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The real part of a polynomial -/

/-- SVT-8 (GSLW Cor 18). The coefficientwise real part `Re[p] = (p + p^*)/2` of a polynomial
over `ℂ`, where `p^* = conjP p` is the coefficientwise conjugate. -/
noncomputable def rePoly (p : Polynomial ℂ) : Polynomial ℂ := (1 / 2 : ℂ) • (p + conjP p)

/-- SVT-8. `Re[p]` has coefficients `Re(pₖ)`. -/
theorem coeff_rePoly (p : Polynomial ℂ) (k : ℕ) :
    (rePoly p).coeff k = ((p.coeff k).re : ℂ) := by
  rw [rePoly, Polynomial.coeff_smul, Polynomial.coeff_add, conjP, Polynomial.coeff_map,
    Complex.add_conj, smul_eq_mul]
  push_cast
  ring

/-- SVT-8. `Re[p]` has real coefficients: `(Re[p])^* = Re[p]`. -/
theorem conjP_rePoly (p : Polynomial ℂ) : conjP (rePoly p) = rePoly p := by
  ext k
  rw [conjP, Polynomial.coeff_map, coeff_rePoly, Complex.conj_ofReal]

/-- SVT-8. A polynomial with real coefficients is its own real part. -/
theorem rePoly_eq_self_of_real {p : Polynomial ℂ} (h : ∀ k, (p.coeff k).im = 0) :
    rePoly p = p := by
  ext k
  rw [coeff_rePoly]
  apply Complex.ext <;> simp [h k]

/-- SVT-8. A real polynomial viewed over `ℂ` is its own real part. -/
theorem rePoly_map_ofReal (q : Polynomial ℝ) :
    rePoly (q.map (algebraMap ℝ ℂ)) = q.map (algebraMap ℝ ℂ) :=
  rePoly_eq_self_of_real fun k => by
    rw [Polynomial.coeff_map, Complex.coe_algebraMap, Complex.ofReal_im]

/-- SVT-8. The Chebyshev polynomials have real coefficients: `Re[T_d] = T_d`. -/
theorem rePoly_chebyshev (d : ℕ) :
    rePoly (Polynomial.Chebyshev.T ℂ d) = Polynomial.Chebyshev.T ℂ d := by
  rw [← Polynomial.Chebyshev.map_T (algebraMap ℝ ℂ) d, rePoly_map_ofReal]

theorem natDegree_conjP_le (p : Polynomial ℂ) : (conjP p).natDegree ≤ p.natDegree :=
  Polynomial.natDegree_map_le

/-- SVT-8. `deg Re[p] ≤ deg p`. -/
theorem natDegree_rePoly_le (p : Polynomial ℂ) : (rePoly p).natDegree ≤ p.natDegree :=
  (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_add_le _ _).trans (max_le le_rfl (natDegree_conjP_le p)))

/-- SVT-8. On the real line, `Re[p]` evaluates to the real part of `p`:
`Re[p](x) = Re(p(x))` for `x : ℝ`. -/
theorem eval_rePoly_ofReal (p : Polynomial ℂ) (x : ℝ) :
    (rePoly p).eval (x : ℂ) = ((p.eval (x : ℂ)).re : ℂ) := by
  rw [rePoly, Polynomial.eval_smul, Polynomial.eval_add, eval_conjP_ofReal, Complex.add_conj,
    smul_eq_mul]
  push_cast
  ring

/-- SVT-8. The first QSP polynomial of the negated phases is `P^*` (QSP-3 (iv), first
component). -/
theorem qspPoly_neg_fst (Φ : List ℝ) : (qspPoly (Φ.map Neg.neg)).1 = conjP (qspPoly Φ).1 := by
  rw [qspPoly_neg]

/-! ### Polynomials in the encoded operator of a Hermitian encoding -/

section Hermitian

variable (E : HermitianEncoding ℋ)

/-- `Π` and `A` commute (both products equal `A`). -/
theorem commute_P_encoded : Commute E.P E.encoded :=
  (P_mul_encoded E).trans (encoded_mul_P E).symm

/-- `Π Aⁿ = Aⁿ Π`. -/
theorem P_mul_pow (n : ℕ) : E.P * E.encoded ^ n = E.encoded ^ n * E.P :=
  ((commute_P_encoded E).pow_right n).eq

/-- SVT-8. `Π` commutes with every polynomial in `A`: `Π p(A) = p(A) Π`. -/
theorem P_mul_aeval (p : Polynomial ℂ) :
    E.P * Polynomial.aeval E.encoded p = Polynomial.aeval E.encoded p * E.P := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, add_mul, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm, smul_mul_assoc, P_mul_pow]

/-- SVT-8. The adjoint of a polynomial in the self-adjoint operator `A` is the conjugate
polynomial in `A`: `p(A)† = p^*(A)`. -/
theorem aeval_adjoint (p : Polynomial ℂ) :
    (Polynomial.aeval E.encoded p)† = Polynomial.aeval E.encoded (conjP p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, conjP_add, map_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, ← LinearMap.star_eq_adjoint, star_mul, star_pow,
      ← algebraMap_star_comm, LinearMap.star_eq_adjoint, E.encoded_adjoint_eq, conjP,
      Polynomial.map_monomial, Polynomial.aeval_monomial, Complex.star_def]
    exact ((Algebra.commute_algebraMap_left _ _).eq).symm

/-- SVT-8. `Re[p](A)` is self-adjoint. -/
theorem aeval_rePoly_isSelfAdjoint (p : Polynomial ℂ) :
    IsSelfAdjoint (Polynomial.aeval E.encoded (rePoly p)) := by
  rw [LinearMap.isSelfAdjoint_iff', aeval_adjoint, conjP_rePoly]

/-! ### GSLW Cor 18 for Hermitian encodings -/

/-- SVT-8 (GSLW Cor 18, Hermitian case `Π̃ = Π`). Compressing the two-term LCU of `U_Φ` and
`U_{−Φ}` by `|0⟩⟨0| ⊗ Π` on both sides gives `|0⟩⟨0| ⊗ (Re[P_Φ](A) Π)`:
```
(|0⟩⟨0| ⊗ Π) lcu2 U_Φ U_{−Φ} (|0⟩⟨0| ⊗ Π) = |0⟩⟨0| ⊗ (Re[P_Φ](A) Π),
```
where `P_Φ = (qspPoly Φ).1` and `Re[P_Φ] = rePoly P_Φ`. The circuit uses one ancilla qubit and
`Φ.length` (controlled) uses of `U`/`U†`. -/
theorem qet_real (Φ : List ℝ) :
    blockDiag E.P 0 *
        lcu2 (altSeq E.toProjUnitaryEncoding Φ)
          (altSeq E.toProjUnitaryEncoding (Φ.map Neg.neg)) *
        blockDiag E.P 0 =
      blockDiag (Polynomial.aeval E.encoded (rePoly (qspPoly Φ).1) * E.P) 0 := by
  rw [proj_lcu2_proj, qet E Φ, qet E (Φ.map Neg.neg), qspPoly_neg_fst, rePoly, map_smul,
    map_add, smul_mul_assoc, add_mul]

/-- SVT-8 (GSLW Cor 18, `(0,0)` block). `(⟨0| ⊗ Π) lcu2 U_Φ U_{−Φ} (|0⟩ ⊗ Π) = Re[P_Φ](A) Π`. -/
theorem topLeft_qet_real (Φ : List ℝ) :
    topLeft (blockDiag E.P 0 *
        lcu2 (altSeq E.toProjUnitaryEncoding Φ)
          (altSeq E.toProjUnitaryEncoding (Φ.map Neg.neg)) *
        blockDiag E.P 0) =
      Polynomial.aeval E.encoded (rePoly (qspPoly Φ).1) * E.P := by
  rw [qet_real, topLeft_blockDiag]

end Hermitian

/-! ### Packaging as a Hermitian encoding on `Anc ℋ` -/

/-- ENC-2. `|0⟩⟨0| ⊗ Π` is an orthogonal projection when `Π` is (generalises
`anc0_isProjective`, the case `Π = 1`). -/
theorem blockDiag_isProjective {P : L ℋ} (hP : IsProjective P) : IsProjective (blockDiag P 0) := by
  have h1 : blockDiag P 0 * blockDiag P 0 = blockDiag P 0 := by
    rw [blockDiag_mul, hP.mul_self, zero_mul]
  have h2 : (blockDiag P 0)† = blockDiag P 0 := by
    rw [blockDiag_adjoint, hP.adjoint_eq, map_zero]
  exact isProjective_iff_isStarProjection.mpr ⟨h1, h2⟩

/-- SVT-8 (GSLW Cor 18). The Hermitian encoding of `Re[P_Φ](A)` on `ℋ` with one ancilla qubit:
the unitary is the LCU circuit `lcu2 U_Φ U_{−Φ}` on `Anc ℋ` and both projections are
`|0⟩⟨0| ⊗ Π`. Its encoded operator is `|0⟩⟨0| ⊗ (Re[P_Φ](A) Π)` (`qsvtReal_encoded`). -/
noncomputable def _root_.QSVT.Encoding.HermitianEncoding.qsvtReal (E : HermitianEncoding ℋ)
    (Φ : List ℝ) : HermitianEncoding (Anc ℋ) where
  U := lcu2 (altSeq E.toProjUnitaryEncoding Φ) (altSeq E.toProjUnitaryEncoding (Φ.map Neg.neg))
  hU := lcu2_mem_unitary _ _ (altSeq_mem_unitary _ _) (altSeq_mem_unitary _ _)
  P := blockDiag E.P 0
  P' := blockDiag E.P 0
  hP := blockDiag_isProjective E.hP
  hP' := blockDiag_isProjective E.hP
  P'_eq := rfl
  encoded_selfAdjoint := by
    rw [qet_real, LinearMap.isSelfAdjoint_iff', blockDiag_adjoint, map_zero,
      ← LinearMap.star_eq_adjoint, star_mul, E.hP.isSelfAdjoint.star_eq,
      (aeval_rePoly_isSelfAdjoint E _).star_eq, P_mul_aeval]

section Hermitian

variable (E : HermitianEncoding ℋ)

@[simp] theorem qsvtReal_U (Φ : List ℝ) :
    (E.qsvtReal Φ).U =
      lcu2 (altSeq E.toProjUnitaryEncoding Φ) (altSeq E.toProjUnitaryEncoding (Φ.map Neg.neg)) :=
  rfl

@[simp] theorem qsvtReal_P (Φ : List ℝ) : (E.qsvtReal Φ).P = blockDiag E.P 0 := rfl

@[simp] theorem qsvtReal_P' (Φ : List ℝ) : (E.qsvtReal Φ).P' = blockDiag E.P 0 := rfl

/-- SVT-8 (GSLW Cor 18). The encoded operator of `E.qsvtReal Φ` is `|0⟩⟨0| ⊗ (Re[P_Φ](A) Π)`. -/
theorem qsvtReal_encoded (Φ : List ℝ) :
    (E.qsvtReal Φ).encoded =
      blockDiag (Polynomial.aeval E.encoded (rePoly (qspPoly Φ).1) * E.P) 0 :=
  qet_real E Φ

/-- SVT-8. The `(0,0)` block of the encoded operator of `E.qsvtReal Φ` is `Re[P_Φ](A) Π`. -/
theorem topLeft_qsvtReal_encoded (Φ : List ℝ) :
    topLeft (E.qsvtReal Φ).encoded = Polynomial.aeval E.encoded (rePoly (qspPoly Φ).1) * E.P := by
  rw [qsvtReal_encoded, topLeft_blockDiag]

/-- SVT-8 (Chebyshev instance). With the phases of QSP-4, `E.qsvtReal (chebPhases d)` encodes
`|0⟩⟨0| ⊗ (T_d(A) Π)`, since `T_d` has real coefficients. -/
theorem qsvtReal_encoded_chebyshev (d : ℕ) :
    (E.qsvtReal (chebPhases d)).encoded =
      blockDiag (Polynomial.aeval E.encoded (Polynomial.Chebyshev.T ℂ d) * E.P) 0 := by
  rw [qsvtReal_encoded, qspPoly_chebPhases, rePoly_chebyshev]

end Hermitian

end QSVT.SVT
