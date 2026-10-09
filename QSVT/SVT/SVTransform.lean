/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.EigenBasis
import QSVT.Polynomial.SqrtPart

/-!
# Singular value transformation without an SVD (formal-spec SVT-5, design decision D3)

For a projected unitary encoding `E` with encoded operator `A = Π̃ U Π` and a polynomial
`p = p_even + p_odd` (`QSVT.Poly.evenPart`, `QSVT.Poly.oddPart`), write
`p_even = R(X²)` and `p_odd = X · S(X²)` (`QSVT.Poly.evenRoot`, `QSVT.Poly.oddRoot`).
The polynomial singular value transformation (GSLW Def 16) is then

  `svTransform p E = Π R(A†A) Π + A S(A†A)`,

which needs no singular value decomposition.  On a singular vector `ψ` of `A` with singular
value `ς` it acts as `ψ ↦ R(ς²) ψ = p_even(ς) ψ` resp. `ψ ↦ ς S(ς²) ψ̃ = p_odd(ς) ψ̃` (SVT-6).

* `svTransform`: the definition; `svTransform_add`, `svTransform_smul` (linearity in `p`),
  `svTransform_of_isEven`, `svTransform_of_isOdd`, `svTransform_one`, `svTransform_X`,
  `svTransform_X_sq`.
* `svTransform_eq_aeval`: for a Hermitian encoding (`Π̃ = Π`, `A† = A`) the transformation is
  the eigenvalue transformation of SVT-3: `svTransform p E = p(A) Π`.

The file also records the additivity/homogeneity of `evenPart`, `oddPart`, `evenRoot`,
`oddRoot` (namespace `QSVT.Poly`); these belong in `QSVT.Polynomial.Parity`/`SqrtPart`.

## Mathlib facts used

`Polynomial.aeval_comp` (valid for a noncommutative target algebra), `Polynomial.aeval_X_pow`,
`Polynomial.induction_on'`, `Polynomial.aeval_monomial`, `Algebra.commutes`,
`Commute.mul_right`, `Commute.pow_right`.
-/

namespace QSVT.Poly

open Polynomial

/-! ### Additivity and homogeneity of the parity decomposition (POLY-2, POLY-3) -/

theorem evenPart_add (p q : ℂ[X]) : evenPart (p + q) = evenPart p + evenPart q := by
  ext k
  simp only [coeff_evenPart, coeff_add]
  split_ifs <;> simp

theorem oddPart_add (p q : ℂ[X]) : oddPart (p + q) = oddPart p + oddPart q := by
  ext k
  simp only [coeff_oddPart, coeff_add]
  split_ifs <;> simp

theorem evenPart_smul (c : ℂ) (p : ℂ[X]) : evenPart (c • p) = c • evenPart p := by
  ext k
  simp only [coeff_evenPart, coeff_smul, smul_eq_mul]
  split_ifs <;> simp

theorem oddPart_smul (c : ℂ) (p : ℂ[X]) : oddPart (c • p) = c • oddPart p := by
  ext k
  simp only [coeff_oddPart, coeff_smul, smul_eq_mul]
  split_ifs <;> simp

theorem evenRoot_add (p q : ℂ[X]) : evenRoot (p + q) = evenRoot p + evenRoot q := by
  ext k
  simp only [coeff_evenRoot, coeff_add]

theorem oddRoot_add (p q : ℂ[X]) : oddRoot (p + q) = oddRoot p + oddRoot q := by
  ext k
  simp only [coeff_oddRoot, coeff_add]

theorem evenRoot_smul (c : ℂ) (p : ℂ[X]) : evenRoot (c • p) = c • evenRoot p := by
  ext k
  simp only [coeff_evenRoot, coeff_smul]

theorem oddRoot_smul (c : ℂ) (p : ℂ[X]) : oddRoot (c • p) = c • oddRoot p := by
  ext k
  simp only [coeff_oddRoot, coeff_smul]

@[simp]
theorem evenRoot_zero : evenRoot (0 : ℂ[X]) = 0 := by
  ext k
  simp only [coeff_evenRoot, coeff_zero]

@[simp]
theorem oddRoot_zero : oddRoot (0 : ℂ[X]) = 0 := by
  ext k
  simp only [coeff_oddRoot, coeff_zero]

/-- `evenRoot 1 = 1`, since `1 = 1.comp (X ^ 2)`. -/
@[simp]
theorem evenRoot_one : evenRoot (1 : ℂ[X]) = 1 := by
  simpa using evenRoot_comp_X_sq (1 : ℂ[X])

/-- `evenRoot (X ^ 2) = X`, since `X ^ 2 = X.comp (X ^ 2)`. -/
@[simp]
theorem evenRoot_X_sq : evenRoot (X ^ 2 : ℂ[X]) = X := by
  simpa using evenRoot_comp_X_sq (X : ℂ[X])

/-- `oddRoot X = 1`, since `X = X * 1.comp (X ^ 2)`. -/
@[simp]
theorem oddRoot_X : oddRoot (X : ℂ[X]) = 1 := by
  simpa using oddRoot_X_mul_comp_X_sq (1 : ℂ[X])

/-- POLY-2. An even polynomial has vanishing odd part. -/
theorem IsEven.oddPart_eq_zero {p : ℂ[X]} (h : IsEven p) : oddPart p = 0 :=
  oddPart_eq_of_add h isOdd_zero (add_zero p)

/-- POLY-2. An odd polynomial has vanishing even part. -/
theorem IsOdd.evenPart_eq_zero {p : ℂ[X]} (h : IsOdd p) : evenPart p = 0 :=
  evenPart_eq_of_add isEven_zero h (zero_add p)

theorem isEven_X_sq : IsEven (X ^ 2 : ℂ[X]) := by
  simpa using isEven_comp_X_sq (X : ℂ[X])

end QSVT.Poly

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.Poly Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- SVT-5. The polynomial singular value transformation (GSLW Def 16), defined without an SVD:
with `p = R(X²) + X · S(X²)` (`R = evenRoot (evenPart p)`, `S = oddRoot (oddPart p)`),

  `svTransform p E = Π R(A†A) Π + A S(A†A)`. -/
noncomputable def svTransform (p : ℂ[X]) (E : ProjUnitaryEncoding ℋ) : L ℋ :=
  E.P * aeval (E.encoded† * E.encoded) (evenRoot (evenPart p)) * E.P
    + E.encoded * aeval (E.encoded† * E.encoded) (oddRoot (oddPart p))

variable (E : ProjUnitaryEncoding ℋ)

/-! ### Linearity in the polynomial -/

/-- SVT-5. `svTransform` is additive in `p`. -/
theorem svTransform_add (p q : ℂ[X]) :
    svTransform (p + q) E = svTransform p E + svTransform q E := by
  simp only [svTransform, evenPart_add, oddPart_add, evenRoot_add, oddRoot_add, map_add, mul_add,
    add_mul]
  abel

/-- SVT-5. `svTransform` is `ℂ`-homogeneous in `p`. -/
theorem svTransform_smul (c : ℂ) (p : ℂ[X]) : svTransform (c • p) E = c • svTransform p E := by
  simp only [svTransform, evenPart_smul, oddPart_smul, evenRoot_smul, oddRoot_smul, map_smul,
    mul_smul_comm, smul_mul_assoc, smul_add]

@[simp]
theorem svTransform_zero : svTransform 0 E = 0 := by
  simp only [svTransform, evenPart_eq_of_add isEven_zero isOdd_zero (add_zero (0 : ℂ[X])),
    oddPart_eq_of_add isEven_zero isOdd_zero (add_zero (0 : ℂ[X])), evenRoot_zero, oddRoot_zero,
    map_zero, mul_zero, zero_mul, add_zero]

/-! ### Even and odd polynomials -/

/-- SVT-5. For even `p = R(X²)`: `svTransform p E = Π R(A†A) Π`. -/
theorem svTransform_of_isEven {p : ℂ[X]} (h : IsEven p) :
    svTransform p E = E.P * aeval (E.encoded† * E.encoded) (evenRoot p) * E.P := by
  rw [svTransform, h.evenPart_eq, h.oddPart_eq_zero, oddRoot_zero, map_zero, mul_zero, add_zero]

/-- SVT-5. For odd `p = X · S(X²)`: `svTransform p E = A S(A†A)`. -/
theorem svTransform_of_isOdd {p : ℂ[X]} (h : IsOdd p) :
    svTransform p E = E.encoded * aeval (E.encoded† * E.encoded) (oddRoot p) := by
  rw [svTransform, h.oddPart_eq, h.evenPart_eq_zero, evenRoot_zero, map_zero, mul_zero, zero_mul,
    zero_add]

/-- SVT-5. `svTransform 1 E = Π`. -/
@[simp]
theorem svTransform_one : svTransform 1 E = E.P := by
  rw [svTransform_of_isEven E isEven_one, evenRoot_one, map_one, mul_one, E.hP.mul_self]

/-- SVT-5. `svTransform X E = A`. -/
@[simp]
theorem svTransform_X : svTransform X E = E.encoded := by
  rw [svTransform_of_isOdd E isOdd_X, oddRoot_X, map_one, mul_one]

/-- SVT-5. `svTransform X² E = Π A†A Π`. -/
theorem svTransform_X_sq : svTransform (X ^ 2) E = E.P * (E.encoded† * E.encoded) * E.P := by
  rw [svTransform_of_isEven E isEven_X_sq, evenRoot_X_sq, aeval_X]

/-! ### Consistency with the eigenvalue transformation (SVT-3) -/

/-- SVT-5. `Π A† = A†` (adjoint of `A Π = A`). -/
theorem P_mul_encoded_adjoint : E.P * E.encoded† = E.encoded† := by
  rw [← LinearMap.star_eq_adjoint, ← E.hP.isSelfAdjoint.star_eq, ← star_mul, E.encoded_mul_P]

/-- SVT-5. `Π` commutes with `A†A` (both `Π A† = A†` and `A Π = A` hold for every encoding). -/
theorem commute_P_adjoint_mul_encoded : Commute E.P (E.encoded† * E.encoded) := by
  change E.P * (E.encoded† * E.encoded) = E.encoded† * E.encoded * E.P
  rw [← mul_assoc, P_mul_encoded_adjoint, mul_assoc, E.encoded_mul_P]

/-- SVT-5. `Π` commutes with every polynomial in `A†A`. -/
theorem commute_P_aeval (R : ℂ[X]) : Commute E.P (aeval (E.encoded† * E.encoded) R) := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]
    have h0 : Commute E.P (algebraMap ℂ (L ℋ) a) := (Algebra.commutes a E.P).symm
    exact h0.mul_right ((commute_P_adjoint_mul_encoded E).pow_right n)

/-- SVT-5. `Π R(A†A) Π = R(A†A) Π`. -/
theorem P_mul_aeval_mul_P (R : ℂ[X]) :
    E.P * aeval (E.encoded† * E.encoded) R * E.P = aeval (E.encoded† * E.encoded) R * E.P := by
  rw [(commute_P_aeval E R).eq, mul_assoc, E.hP.mul_self]

/-- SVT-5. `A S(A†A) Π = A S(A†A)`. -/
theorem encoded_mul_aeval_mul_P (S : ℂ[X]) :
    E.encoded * aeval (E.encoded† * E.encoded) S * E.P =
      E.encoded * aeval (E.encoded† * E.encoded) S := by
  rw [mul_assoc, ← (commute_P_aeval E S).eq, ← mul_assoc, E.encoded_mul_P]

/-- SVT-5. The singular value transformation is supported on `ran Π`:
`svTransform p E * Π = svTransform p E`. -/
theorem svTransform_mul_P (p : ℂ[X]) : svTransform p E * E.P = svTransform p E := by
  rw [svTransform, add_mul, mul_assoc, E.hP.mul_self, encoded_mul_aeval_mul_P]

/-- SVT-5. For a Hermitian encoding (`Π̃ = Π`, `A† = A`) the SVD-free singular value
transformation is the eigenvalue transformation of SVT-3: `svTransform p E = p(A) Π`. -/
theorem svTransform_eq_aeval (E : HermitianEncoding ℋ) (p : ℂ[X]) :
    svTransform p E.toProjUnitaryEncoding = aeval E.encoded p * E.P := by
  have hAA : E.encoded† * E.encoded = E.encoded * E.encoded := by rw [E.encoded_adjoint_eq]
  have hcomp : ∀ R : ℂ[X], aeval E.encoded (R.comp (X ^ 2)) = aeval (E.encoded† * E.encoded) R :=
    fun R => by rw [aeval_comp, aeval_X_pow, sq, hAA]
  have heven : aeval E.encoded (evenPart p) =
      aeval (E.encoded† * E.encoded) (evenRoot (evenPart p)) := by
    conv_lhs => rw [(isEven_evenPart p).eq_evenRoot_comp]
    exact hcomp _
  have hodd : aeval E.encoded (oddPart p) =
      E.encoded * aeval (E.encoded† * E.encoded) (oddRoot (oddPart p)) := by
    conv_lhs => rw [(isOdd_oddPart p).eq_X_mul_oddRoot_comp]
    rw [map_mul, aeval_X, hcomp]
  calc svTransform p E.toProjUnitaryEncoding
      = aeval (E.encoded† * E.encoded) (evenRoot (evenPart p)) * E.P
          + E.encoded * aeval (E.encoded† * E.encoded) (oddRoot (oddPart p)) * E.P := by
        rw [svTransform, P_mul_aeval_mul_P, encoded_mul_aeval_mul_P]
    _ = aeval E.encoded (evenPart p) * E.P + aeval E.encoded (oddPart p) * E.P := by
        rw [heven, hodd]
    _ = aeval E.encoded p * E.P := by rw [← add_mul, ← map_add, evenPart_add_oddPart]

end QSVT.SVT
