/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import QSVT.Polynomial.Parity

/-!
# Even and odd polynomials as polynomials in `X²` (formal-spec POLY-3)

* `evenRoot P` : the polynomial with coefficients `k ↦ P.coeff (2k)` (Mathlib's
  `Polynomial.contract 2 P`), so that an even `P` is `(evenRoot P).comp (X ^ 2)`.
* `oddRoot P`  : coefficients `k ↦ P.coeff (2k + 1)`, so that an odd `P` is
  `X * (oddRoot P).comp (X ^ 2)`.

Both representations are stated in two equivalent forms, with `Polynomial.expand ℂ 2`
(`IsEven.eq_expand_evenRoot`) and with `comp (X ^ 2)` (`IsEven.eq_evenRoot_comp`);
`Polynomial.expand_eq_comp_X_pow` is `rfl`.  The spec's `sqrtPart` is `evenRoot`
(for even `P`) resp. `oddRoot` (for odd `P`).

Evaluation forms: `IsEven.eval_eq : P.eval x = (evenRoot P).eval (x ^ 2)` and
`IsOdd.eval_eq : P.eval x = x * (oddRoot P).eval (x ^ 2)`.
-/

namespace QSVT.Poly

open Polynomial

/-- POLY-3. `evenRoot P` collects the even-degree coefficients of `P`:
`(evenRoot P).coeff k = P.coeff (2 * k)`.  For even `P`, `P = (evenRoot P).comp (X ^ 2)`. -/
noncomputable def evenRoot (P : ℂ[X]) : ℂ[X] := contract 2 P

/-- POLY-3. `oddRoot P` collects the odd-degree coefficients of `P`:
`(oddRoot P).coeff k = P.coeff (2 * k + 1)`.  For odd `P`, `P = X * (oddRoot P).comp (X ^ 2)`. -/
noncomputable def oddRoot (P : ℂ[X]) : ℂ[X] := contract 2 P.divX

@[simp]
theorem coeff_evenRoot (P : ℂ[X]) (k : ℕ) : (evenRoot P).coeff k = P.coeff (2 * k) := by
  rw [evenRoot, coeff_contract two_ne_zero, mul_comm]

@[simp]
theorem coeff_oddRoot (P : ℂ[X]) (k : ℕ) : (oddRoot P).coeff k = P.coeff (2 * k + 1) := by
  rw [oddRoot, coeff_contract two_ne_zero, coeff_divX, mul_comm]

/-! ### Coefficients of `R.comp (X ^ 2)` -/

theorem coeff_comp_X_sq (R : ℂ[X]) (k : ℕ) :
    (R.comp (X ^ 2)).coeff k = if 2 ∣ k then R.coeff (k / 2) else 0 := by
  rw [← expand_eq_comp_X_pow, coeff_expand two_pos]

theorem coeff_comp_X_sq_two_mul (R : ℂ[X]) (k : ℕ) :
    (R.comp (X ^ 2)).coeff (2 * k) = R.coeff k := by
  rw [← expand_eq_comp_X_pow, coeff_expand_mul' two_pos]

theorem coeff_comp_X_sq_of_odd (R : ℂ[X]) {k : ℕ} (hk : Odd k) :
    (R.comp (X ^ 2)).coeff k = 0 := by
  rw [coeff_comp_X_sq, ite_eq_right]
  exact fun h => (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr h)

/-- POLY-3. `R.comp (X ^ 2)` is even. -/
theorem isEven_comp_X_sq (R : ℂ[X]) : IsEven (R.comp (X ^ 2)) :=
  fun _ hk => coeff_comp_X_sq_of_odd R hk

/-- POLY-3. `X * R.comp (X ^ 2)` is odd. -/
theorem isOdd_X_mul_comp_X_sq (R : ℂ[X]) : IsOdd (X * R.comp (X ^ 2)) :=
  (isEven_comp_X_sq R).X_mul

theorem natDegree_comp_X_sq (R : ℂ[X]) : (R.comp (X ^ 2)).natDegree = 2 * R.natDegree := by
  rw [← expand_eq_comp_X_pow, natDegree_expand, mul_comm]

/-! ### `evenRoot` / `oddRoot` invert the representation -/

@[simp]
theorem evenRoot_comp_X_sq (R : ℂ[X]) : evenRoot (R.comp (X ^ 2)) = R := by
  rw [evenRoot, ← expand_eq_comp_X_pow, contract_expand _ two_ne_zero]

@[simp]
theorem oddRoot_X_mul_comp_X_sq (R : ℂ[X]) : oddRoot (X * R.comp (X ^ 2)) = R := by
  ext k
  rw [coeff_oddRoot, coeff_X_mul, coeff_comp_X_sq_two_mul]

/-! ### The representation theorems -/

/-- POLY-3 (`expand` form). An even polynomial is `expand ℂ 2` of its `evenRoot`. -/
theorem IsEven.eq_expand_evenRoot {P : ℂ[X]} (h : IsEven P) : P = expand ℂ 2 (evenRoot P) := by
  ext k
  rw [coeff_expand two_pos, coeff_evenRoot]
  split_ifs with hk
  · rw [Nat.mul_div_cancel' hk]
  · exact h k (Nat.not_even_iff_odd.mp fun he => hk (even_iff_two_dvd.mp he))

/-- POLY-3. An even polynomial is a polynomial in `X ^ 2`: `P = (evenRoot P).comp (X ^ 2)`. -/
theorem IsEven.eq_evenRoot_comp {P : ℂ[X]} (h : IsEven P) : P = (evenRoot P).comp (X ^ 2) := by
  rw [← expand_eq_comp_X_pow]
  exact h.eq_expand_evenRoot

/-- POLY-3 (`expand` form). An odd polynomial is `X * expand ℂ 2 (oddRoot P)`. -/
theorem IsOdd.eq_X_mul_expand_oddRoot {P : ℂ[X]} (h : IsOdd P) :
    P = X * expand ℂ 2 (oddRoot P) := by
  ext k
  rcases k with _ | m
  · rw [coeff_X_mul_zero]
    exact h 0 (by decide)
  · rw [coeff_X_mul, coeff_expand two_pos, coeff_oddRoot]
    split_ifs with hm
    · rw [Nat.mul_div_cancel' hm]
    · exact h (m + 1) (Nat.even_add_one.mpr fun he => hm (even_iff_two_dvd.mp he))

/-- POLY-3. An odd polynomial is `X` times a polynomial in `X ^ 2`:
`P = X * (oddRoot P).comp (X ^ 2)`. -/
theorem IsOdd.eq_X_mul_oddRoot_comp {P : ℂ[X]} (h : IsOdd P) :
    P = X * (oddRoot P).comp (X ^ 2) := by
  rw [← expand_eq_comp_X_pow]
  exact h.eq_X_mul_expand_oddRoot

/-- POLY-3. `IsEven P ↔ ∃ R, P = R.comp (X ^ 2)`. -/
theorem isEven_iff_exists_comp_X_sq {P : ℂ[X]} : IsEven P ↔ ∃ R : ℂ[X], P = R.comp (X ^ 2) :=
  ⟨fun h => ⟨_, h.eq_evenRoot_comp⟩, fun ⟨R, hR⟩ => hR ▸ isEven_comp_X_sq R⟩

/-- POLY-3. `IsOdd P ↔ ∃ R, P = X * R.comp (X ^ 2)`. -/
theorem isOdd_iff_exists_X_mul_comp_X_sq {P : ℂ[X]} :
    IsOdd P ↔ ∃ R : ℂ[X], P = X * R.comp (X ^ 2) :=
  ⟨fun h => ⟨_, h.eq_X_mul_oddRoot_comp⟩, fun ⟨R, hR⟩ => hR ▸ isOdd_X_mul_comp_X_sq R⟩

/-! ### Degrees -/

theorem natDegree_evenRoot_le (P : ℂ[X]) : (evenRoot P).natDegree ≤ P.natDegree / 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_evenRoot]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem natDegree_oddRoot_le (P : ℂ[X]) : (oddRoot P).natDegree ≤ P.natDegree / 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_oddRoot]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- For even `P`, `deg P = 2 deg (evenRoot P)`. -/
theorem IsEven.natDegree_eq {P : ℂ[X]} (h : IsEven P) :
    P.natDegree = 2 * (evenRoot P).natDegree := by
  conv_lhs => rw [h.eq_evenRoot_comp]
  exact natDegree_comp_X_sq _

/-! ### Evaluation -/

/-- POLY-3. For even `P`, `P(x) = (evenRoot P)(x²)`. -/
theorem IsEven.eval_eq {P : ℂ[X]} (h : IsEven P) (x : ℂ) :
    P.eval x = (evenRoot P).eval (x ^ 2) := by
  conv_lhs => rw [h.eq_expand_evenRoot]
  rw [expand_eval]

/-- POLY-3. For odd `P`, `P(x) = x * (oddRoot P)(x²)`. -/
theorem IsOdd.eval_eq {P : ℂ[X]} (h : IsOdd P) (x : ℂ) :
    P.eval x = x * (oddRoot P).eval (x ^ 2) := by
  conv_lhs => rw [h.eq_X_mul_expand_oddRoot]
  rw [eval_mul, eval_X, expand_eval]

end QSVT.Poly
