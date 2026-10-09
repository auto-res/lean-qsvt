/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.RealPoly

/-!
# QSVTTest.RealPoly

Regression tests for SVT-8 (GSLW Cor 18, `QSVT.SVT.RealPoly`): the real part of a polynomial,
statement-level instances of `qet_real` / `qsvtReal_encoded` for a single phase, and the axiom
audit.
-/

-- `#print axioms` audits are the whole point of a test file.
set_option linter.hashCommand false

open QuantumState QSVT.Encoding QSVT.SVT QSVT.QSP

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The real part of a polynomial -/

/-- The coefficients of `Re[p]` are the real parts of the coefficients of `p`. -/
example (p : Polynomial ℂ) (k : ℕ) : (rePoly p).coeff k = ((p.coeff k).re : ℂ) :=
  coeff_rePoly p k

/-- `Re[X] = X`. -/
example : rePoly (Polynomial.X : Polynomial ℂ) = Polynomial.X :=
  rePoly_eq_self_of_real fun k => by
    rw [Polynomial.coeff_X]
    split_ifs <;> simp

/-- `Re[i] = 0`. -/
example : rePoly (Polynomial.C Complex.I) = 0 := by
  ext k
  rw [coeff_rePoly, Polynomial.coeff_C, Polynomial.coeff_zero]
  split_ifs <;> simp

/-- `Re[(1 + i) X²] = X²`. -/
example : rePoly (Polynomial.C (1 + Complex.I) * Polynomial.X ^ 2) = Polynomial.X ^ 2 := by
  ext k
  rw [coeff_rePoly, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> simp

/-- `Re[p]` evaluated at a real point is the real part of `p` there. -/
example (p : Polynomial ℂ) (x : ℝ) : (rePoly p).eval (x : ℂ) = ((p.eval (x : ℂ)).re : ℂ) :=
  eval_rePoly_ofReal p x

/-- `Re[T_2] = T_2`. -/
example : rePoly (Polynomial.Chebyshev.T ℂ 2) = Polynomial.Chebyshev.T ℂ 2 :=
  rePoly_chebyshev 2

/-! ### GSLW Cor 18 for a single phase -/

/-- Cor 18 for `Φ = [φ]`, `(0,0)` block:
`(⟨0| ⊗ Π) lcu2 U_[φ] U_[−φ] (|0⟩ ⊗ Π) = Re[P_[φ]](A) Π`. -/
example (E : HermitianEncoding ℋ) (φ : ℝ) :
    topLeft (blockDiag E.P 0 *
        lcu2 (altSeq E.toProjUnitaryEncoding [φ]) (altSeq E.toProjUnitaryEncoding [-φ]) *
        blockDiag E.P 0) =
      Polynomial.aeval E.encoded (rePoly (qspPoly [φ]).1) * E.P :=
  topLeft_qet_real E [φ]

/-- The combinator `qsvtReal` for a single phase encodes `|0⟩⟨0| ⊗ (Re[P_[φ]](A) Π)`. -/
example (E : HermitianEncoding ℋ) (φ : ℝ) :
    (E.qsvtReal [φ]).encoded =
      blockDiag (Polynomial.aeval E.encoded (rePoly (qspPoly [φ]).1) * E.P) 0 :=
  qsvtReal_encoded E [φ]

/-- The projection of `E.qsvtReal Φ` is `|0⟩⟨0| ⊗ Π`. -/
example (E : HermitianEncoding ℋ) (Φ : List ℝ) : (E.qsvtReal Φ).P = blockDiag E.P 0 := rfl

/-- The encoded operator of `E.qsvtReal Φ` is self-adjoint (a field of `HermitianEncoding`). -/
example (E : HermitianEncoding ℋ) (Φ : List ℝ) : IsSelfAdjoint (E.qsvtReal Φ).encoded :=
  (E.qsvtReal Φ).encoded_selfAdjoint

/-- The Chebyshev instance for `d = 1`: `E.qsvtReal (chebPhases 1)` encodes `|0⟩⟨0| ⊗ (A Π)`. -/
example (E : HermitianEncoding ℋ) :
    (E.qsvtReal (chebPhases 1)).encoded = blockDiag E.encoded 0 := by
  rw [qsvtReal_encoded_chebyshev]
  simp [encoded_mul_P]

/-! ### Axiom audit: the library must not introduce axioms beyond Lean's standard three. -/

/-- info: 'QSVT.SVT.qet_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qet_real

/-- info: 'QSVT.SVT.qsvtReal_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.qsvtReal_encoded

/-- info: 'QSVT.SVT.aeval_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.aeval_adjoint

/-- info: 'QSVT.SVT.coeff_rePoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QSVT.SVT.coeff_rePoly
