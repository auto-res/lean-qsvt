/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Polynomial parity (formal-spec POLY-1, POLY-2)

* `IsEven P` : all odd-degree coefficients vanish.
* `IsOdd P`  : all even-degree coefficients vanish.
* `HasParity P n` : `P` is even when `n` is even and odd when `n` is odd.
* `evenPart P`, `oddPart P` : the even/odd parts of `P`, with
  `evenPart P + oddPart P = P`, `IsEven (evenPart P)`, `IsOdd (oddPart P)`.
* Closure lemmas: `IsEven.add`, `IsEven.sub`, `IsEven.C_mul`, `IsEven.X_mul` (gives an odd
  polynomial), `IsEven.one_sub_X_sq_mul`, the `IsOdd` analogues, and the `HasParity` versions
  (`HasParity.add`, `HasParity.X_mul`, `HasParity.add_two`, ...).

The even/odd parts are defined by filtering the coefficient `Finsupp`, so the
coefficient lemmas are definitional-style `simp` facts and the decomposition is
proved coefficientwise.  The representation `P = R.comp (X^2)` (POLY-3) is in
`QSVT.Polynomial.SqrtPart`.
-/

namespace QSVT.Poly

open Polynomial

/-- POLY-1. A polynomial is even if every odd-degree coefficient vanishes. -/
def IsEven (P : ℂ[X]) : Prop := ∀ k, Odd k → P.coeff k = 0

/-- POLY-1. A polynomial is odd if every even-degree coefficient vanishes. -/
def IsOdd (P : ℂ[X]) : Prop := ∀ k, Even k → P.coeff k = 0

/-- POLY-1. `HasParity P n`: `P` is even when `n` is even and odd when `n` is odd. -/
def HasParity (P : ℂ[X]) (n : ℕ) : Prop :=
  (Even n → IsEven P) ∧ (Odd n → IsOdd P)

theorem HasParity.isEven {P : ℂ[X]} {n : ℕ} (h : HasParity P n) (hn : Even n) : IsEven P :=
  h.1 hn

theorem HasParity.isOdd {P : ℂ[X]} {n : ℕ} (h : HasParity P n) (hn : Odd n) : IsOdd P :=
  h.2 hn

theorem IsEven.hasParity {P : ℂ[X]} (h : IsEven P) {n : ℕ} (hn : Even n) : HasParity P n :=
  ⟨fun _ => h, fun hn' => absurd hn (Nat.not_even_iff_odd.mpr hn')⟩

theorem IsOdd.hasParity {P : ℂ[X]} (h : IsOdd P) {n : ℕ} (hn : Odd n) : HasParity P n :=
  ⟨fun hn' => absurd hn' (Nat.not_even_iff_odd.mpr hn), fun _ => h⟩

/-! ### Even and odd parts (POLY-2) -/

/-- POLY-2. The even part of a polynomial: keep exactly the even-degree coefficients. -/
noncomputable def evenPart (P : ℂ[X]) : ℂ[X] :=
  ⟨⟨P.toFinsupp.coeff.filter Even⟩⟩

/-- POLY-2. The odd part of a polynomial: keep exactly the odd-degree coefficients. -/
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

/-- POLY-2. `evenPart P + oddPart P = P`. -/
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

/-- POLY-2. The even/odd decomposition is unique: if `P = E + O` with `E` even and `O` odd,
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

/-! ### Closure lemmas for `IsEven` / `IsOdd` -/

theorem isEven_one : IsEven (1 : ℂ[X]) := by
  intro k hk
  rw [Polynomial.coeff_one, ite_eq_right]
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hk) ⟨0, rfl⟩

theorem isEven_zero : IsEven (0 : ℂ[X]) := fun _ _ => Polynomial.coeff_zero _

theorem isOdd_zero : IsOdd (0 : ℂ[X]) := fun _ _ => Polynomial.coeff_zero _

theorem isEven_C (a : ℂ) : IsEven (C a) := by
  intro k hk
  rw [Polynomial.coeff_C, ite_eq_right]
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hk) ⟨0, rfl⟩

theorem isOdd_X : IsOdd (X : ℂ[X]) := by
  intro k hk
  rw [Polynomial.coeff_X]
  split_ifs with h
  · subst h
    exact absurd hk (by decide)
  · rfl

theorem IsEven.add {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P + Q) := by
  intro k hk
  rw [Polynomial.coeff_add, hP k hk, hQ k hk, add_zero]

theorem IsOdd.add {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsOdd Q) : IsOdd (P + Q) := by
  intro k hk
  rw [Polynomial.coeff_add, hP k hk, hQ k hk, add_zero]

theorem IsEven.sub {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P - Q) := by
  intro k hk
  rw [Polynomial.coeff_sub, hP k hk, hQ k hk, sub_zero]

theorem IsOdd.sub {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsOdd Q) : IsOdd (P - Q) := by
  intro k hk
  rw [Polynomial.coeff_sub, hP k hk, hQ k hk, sub_zero]

theorem IsEven.neg {P : ℂ[X]} (hP : IsEven P) : IsEven (-P) := by
  intro k hk
  rw [Polynomial.coeff_neg, hP k hk, neg_zero]

theorem IsOdd.neg {P : ℂ[X]} (hP : IsOdd P) : IsOdd (-P) := by
  intro k hk
  rw [Polynomial.coeff_neg, hP k hk, neg_zero]

theorem IsEven.C_mul {P : ℂ[X]} (hP : IsEven P) (a : ℂ) : IsEven (C a * P) := by
  intro k hk
  rw [Polynomial.coeff_C_mul, hP k hk, mul_zero]

theorem IsOdd.C_mul {P : ℂ[X]} (hP : IsOdd P) (a : ℂ) : IsOdd (C a * P) := by
  intro k hk
  rw [Polynomial.coeff_C_mul, hP k hk, mul_zero]

/-- Multiplying an even polynomial by `X` gives an odd one. -/
theorem IsEven.X_mul {P : ℂ[X]} (hP : IsEven P) : IsOdd (X * P) := by
  intro k hk
  rcases k with _ | m
  · exact Polynomial.coeff_X_mul_zero P
  · rw [Polynomial.coeff_X_mul]
    exact hP m (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hk))

/-- Multiplying an odd polynomial by `X` gives an even one. -/
theorem IsOdd.X_mul {P : ℂ[X]} (hP : IsOdd P) : IsEven (X * P) := by
  intro k hk
  rcases k with _ | m
  · exact absurd hk (by decide)
  · rw [Polynomial.coeff_X_mul]
    exact hP m (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hk))

/-- Multiplying by `1 - X²` preserves evenness. -/
theorem IsEven.one_sub_X_sq_mul {P : ℂ[X]} (hP : IsEven P) : IsEven ((1 - X ^ 2) * P) := by
  have h : (1 - X ^ 2) * P = P - X * (X * P) := by ring
  rw [h]
  exact hP.sub hP.X_mul.X_mul

/-- Multiplying by `1 - X²` preserves oddness. -/
theorem IsOdd.one_sub_X_sq_mul {P : ℂ[X]} (hP : IsOdd P) : IsOdd ((1 - X ^ 2) * P) := by
  have h : (1 - X ^ 2) * P = P - X * (X * P) := by ring
  rw [h]
  exact hP.sub hP.X_mul.X_mul

/-! ### Closure lemmas for `HasParity` -/

theorem hasParity_zero (n : ℕ) : HasParity (0 : ℂ[X]) n :=
  ⟨fun _ => isEven_zero, fun _ => isOdd_zero⟩

theorem hasParity_one : HasParity (1 : ℂ[X]) 0 :=
  isEven_one.hasParity (by decide)

theorem hasParity_C (a : ℂ) : HasParity (C a) 0 :=
  (isEven_C a).hasParity (by decide)

theorem hasParity_X : HasParity (X : ℂ[X]) 1 :=
  isOdd_X.hasParity odd_one

theorem HasParity.add {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P n) (hQ : HasParity Q n) :
    HasParity (P + Q) n :=
  ⟨fun hn => (hP.1 hn).add (hQ.1 hn), fun hn => (hP.2 hn).add (hQ.2 hn)⟩

theorem HasParity.sub {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P n) (hQ : HasParity Q n) :
    HasParity (P - Q) n :=
  ⟨fun hn => (hP.1 hn).sub (hQ.1 hn), fun hn => (hP.2 hn).sub (hQ.2 hn)⟩

theorem HasParity.neg {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) : HasParity (-P) n :=
  ⟨fun hn => (hP.1 hn).neg, fun hn => (hP.2 hn).neg⟩

theorem HasParity.C_mul {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) (a : ℂ) :
    HasParity (C a * P) n :=
  ⟨fun hn => (hP.1 hn).C_mul a, fun hn => (hP.2 hn).C_mul a⟩

/-- Multiplying by `X` shifts the parity by one. -/
theorem HasParity.X_mul {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) : HasParity (X * P) (n + 1) :=
  ⟨fun hn => (hP.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn))).X_mul,
    fun hn => (hP.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn))).X_mul⟩

/-- Parity only depends on `n` modulo `2`. -/
theorem HasParity.add_two {P : ℂ[X]} {n : ℕ} (hP : HasParity P n) : HasParity P (n + 2) :=
  ⟨fun hn => hP.1 ((Nat.even_add.mp hn).mpr even_two),
    fun hn => hP.2 ((Nat.odd_add.mp hn).mpr even_two)⟩

theorem HasParity.of_add_two {P : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 2)) : HasParity P n :=
  ⟨fun hn => hP.1 (Nat.even_add.mpr (iff_of_true hn even_two)),
    fun hn => hP.2 (Nat.odd_add.mpr (iff_of_true hn even_two))⟩

theorem hasParity_add_two_iff {P : ℂ[X]} {n : ℕ} : HasParity P (n + 2) ↔ HasParity P n :=
  ⟨HasParity.of_add_two, HasParity.add_two⟩

end QSVT.Poly
