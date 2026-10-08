/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.Complex.Basic

/-!
# Polynomial parity (formal-spec POLY-1, POLY-2)

* `IsEven P` : all odd-degree coefficients vanish.
* `IsOdd P`  : all even-degree coefficients vanish.
* `evenPart P`, `oddPart P` : the even/odd parts of `P`, with
  `evenPart P + oddPart P = P`, `IsEven (evenPart P)`, `IsOdd (oddPart P)`.

The even/odd parts are defined by filtering the coefficient `Finsupp`, so the
coefficient lemmas are definitional-style `simp` facts and the decomposition is
proved coefficientwise.
-/

namespace QSVT.Poly

open Polynomial

/-- A polynomial is even if every odd-degree coefficient vanishes. -/
def IsEven (P : ℂ[X]) : Prop := ∀ k, Odd k → P.coeff k = 0

/-- A polynomial is odd if every even-degree coefficient vanishes. -/
def IsOdd (P : ℂ[X]) : Prop := ∀ k, Even k → P.coeff k = 0

/-- The even part of a polynomial: keep exactly the even-degree coefficients. -/
noncomputable def evenPart (P : ℂ[X]) : ℂ[X] :=
  ⟨⟨P.toFinsupp.coeff.filter Even⟩⟩

/-- The odd part of a polynomial: keep exactly the odd-degree coefficients. -/
noncomputable def oddPart (P : ℂ[X]) : ℂ[X] :=
  ⟨⟨P.toFinsupp.coeff.filter Odd⟩⟩

@[simp]
theorem coeff_evenPart (P : ℂ[X]) (k : ℕ) :
    (evenPart P).coeff k = if Even k then P.coeff k else 0 := by
  simp only [evenPart, Polynomial.coeff_ofFinsupp, Finsupp.filter_apply, Polynomial.toFinsupp_apply]

@[simp]
theorem coeff_oddPart (P : ℂ[X]) (k : ℕ) :
    (oddPart P).coeff k = if Odd k then P.coeff k else 0 := by
  simp only [oddPart, Polynomial.coeff_ofFinsupp, Finsupp.filter_apply, Polynomial.toFinsupp_apply]

theorem evenPart_add_oddPart (P : ℂ[X]) : evenPart P + oddPart P = P := by
  ext k
  rw [coeff_add, coeff_evenPart, coeff_oddPart]
  rcases Nat.even_or_odd k with hk | hk
  · simp [hk, Nat.not_odd_iff_even.mpr hk]
  · simp [hk, Nat.not_even_iff_odd.mpr hk]

theorem isEven_evenPart (P : ℂ[X]) : IsEven (evenPart P) := by
  intro k hk
  rw [coeff_evenPart, ite_eq_right (Nat.not_even_iff_odd.mpr hk)]

theorem isOdd_oddPart (P : ℂ[X]) : IsOdd (oddPart P) := by
  intro k hk
  rw [coeff_oddPart, ite_eq_right (Nat.not_odd_iff_even.mpr hk)]

/-- The even/odd decomposition is unique: if `P = E + O` with `E` even and `O` odd,
then `E = evenPart P` and `O = oddPart P`. -/
theorem evenPart_eq_of_add {P E O : ℂ[X]} (hE : IsEven E) (hO : IsOdd O) (h : E + O = P) :
    evenPart P = E := by
  ext k
  rw [coeff_evenPart, ← h, coeff_add]
  rcases Nat.even_or_odd k with hk | hk
  · rw [ite_eq_left hk, hO k hk, add_zero]
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hk), hE k hk]

theorem oddPart_eq_of_add {P E O : ℂ[X]} (hE : IsEven E) (hO : IsOdd O) (h : E + O = P) :
    oddPart P = O := by
  ext k
  rw [coeff_oddPart, ← h, coeff_add]
  rcases Nat.even_or_odd k with hk | hk
  · rw [ite_eq_right (Nat.not_odd_iff_even.mpr hk), hO k hk]
  · rw [ite_eq_left hk, hE k hk, zero_add]

theorem IsEven.evenPart_eq {P : ℂ[X]} (hP : IsEven P) : evenPart P = P := by
  ext k
  rw [coeff_evenPart]
  split_ifs with hk
  · rfl
  · exact (hP k (Nat.not_even_iff_odd.mp hk)).symm

theorem IsOdd.oddPart_eq {P : ℂ[X]} (hP : IsOdd P) : oddPart P = P := by
  ext k
  rw [coeff_oddPart]
  split_ifs with hk
  · rfl
  · exact (hP k (Nat.not_odd_iff_even.mp hk)).symm

end QSVT.Poly
