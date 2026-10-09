/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.BigOperators
import QSVT.Polynomial.Chebyshev

/-!
# Computable Chebyshev coefficients (formal-spec POLY-6, `chebCoeff`)

The exact Chebyshev-LCU route (CERT-A) needs the Chebyshev coefficients of a *concrete* input
polynomial, so this module provides a computable layer below `ChebSeries`:

* `QC := ℚ × ℚ` : Gaussian rationals `(re, im)` with the embedding `QC.toC : QC → ℂ`; addition,
  negation and zero are the pointwise `Prod` instances, multiplication and one are `QC.mul`,
  `QC.one`, and `QC.smulQ` is the rational scalar action.  `QC.addList`/`QC.smulList` are the
  pointwise operations on coefficient lists (padding with zeros).
* `PolyQC := List QC` : a polynomial by its coefficient list (index = degree), with
  `PolyQC.toPoly : PolyQC → ℂ[X]` (Horner), `coeff_toPoly`, `toPoly_addList`, `toPoly_smulList`.
* `ChebQC := List QC` : a Chebyshev series by its coefficient list (index `k` ↦ coefficient of
  `T k`), with `ChebQC.toPoly`, `ChebQC.toSeries : ChebQC → ChebSeries` (`toSeries_toPoly`),
  `ChebQC.l1` and the computable rational bound `ChebQC.l1Bound` (`l1_le_l1Bound`,
  `supNorm_toPoly_le_l1Bound`).
* `ChebQC.ofMonomials : PolyQC → ChebQC` : the computable change of basis, by Horner's scheme
  with `ChebQC.mulX` (multiplication by `X` in the Chebyshev basis, from
  `2 X T_{k+1} = T_{k+2} + T_k` and `X T_0 = T_1`), and its correctness theorem
  `toPoly_ofMonomials : ChebQC.toPoly (ofMonomials l) = PolyQC.toPoly l`.

Everything in the computable layer (`QC` operations, `addList`, `smulList`, `mulX`,
`ofMonomials`, `l1Bound`) is free of `ℂ` and `Polynomial`, so it can be run with `#eval`.
-/

namespace QSVT.Poly

-- Only `T` is opened: `Polynomial.Chebyshev.C` (third kind) would shadow `Polynomial.C` lemmas.
open Polynomial
open Polynomial.Chebyshev (T T_zero T_one)

/-! ### Gaussian rationals -/

/-- POLY-6. Gaussian rationals `(re, im)`, the computable scalars of the Chebyshev conversion.
Addition, negation and zero are the pointwise `Prod` instances (which agree with `ℂ` under
`QC.toC`); multiplication and one are `QC.mul` and `QC.one`.  The `Prod` instances `Mul` and
`One` are also pointwise and must not be used. -/
abbrev QC := ℚ × ℚ

namespace QC

/-- POLY-6. The embedding `(a, b) ↦ a + b i` into `ℂ`. -/
noncomputable def toC (z : QC) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- POLY-6. Complex multiplication on Gaussian rationals. -/
def mul (z w : QC) : QC := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- POLY-6. Scalar multiplication by a rational. -/
def smulQ (q : ℚ) (z : QC) : QC := (q * z.1, q * z.2)

/-- POLY-6. The unit `1 + 0 i`. -/
def one : QC := (1, 0)

@[simp] theorem toC_zero : toC 0 = 0 := by simp [toC]

@[simp] theorem toC_one : toC one = 1 := by simp [toC, one]

theorem toC_add (z w : QC) : toC (z + w) = toC z + toC w := by
  simp only [toC, Prod.fst_add, Prod.snd_add, Rat.cast_add]
  ring

theorem toC_neg (z : QC) : toC (-z) = -toC z := by
  simp only [toC, Prod.fst_neg, Prod.snd_neg, Rat.cast_neg]
  ring

theorem toC_mul (z w : QC) : toC (mul z w) = toC z * toC w := by
  simp only [toC, mul, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
  linear_combination (-((z.2 : ℂ) * (w.2 : ℂ))) * Complex.I_sq

theorem toC_smulQ (q : ℚ) (z : QC) : toC (smulQ q z) = (q : ℂ) * toC z := by
  simp only [toC, smulQ, Rat.cast_mul]
  ring

/-- POLY-6. `‖a + b i‖ ≤ |a| + |b|`: the computable bound on the modulus. -/
theorem norm_toC_le (z : QC) : ‖toC z‖ ≤ ((|z.1| + |z.2| : ℚ) : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (toC z)
  have hre : (toC z).re = (z.1 : ℝ) := by simp [toC]
  have him : (toC z).im = (z.2 : ℝ) := by simp [toC]
  rw [hre, him] at h
  push_cast
  exact h

/-! #### Coefficient lists -/

/-- POLY-6. Pointwise addition of coefficient lists, padding the shorter one with zeros. -/
def addList : List QC → List QC → List QC
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addList l m

/-- POLY-6. Scalar multiplication of a coefficient list by a rational. -/
def smulList (q : ℚ) (l : List QC) : List QC := l.map (smulQ q)

@[simp] theorem addList_nil (m : List QC) : addList [] m = m := rfl

@[simp] theorem addList_nil_right (l : List QC) : addList l [] = l := by
  cases l <;> rfl

@[simp] theorem addList_cons_cons (a b : QC) (l m : List QC) :
    addList (a :: l) (b :: m) = (a + b) :: addList l m := rfl

theorem length_addList (l m : List QC) : (addList l m).length = max l.length m.length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      simp only [addList_cons_cons, List.length_cons, ih]
      omega

theorem getD_addList (l m : List QC) (i : ℕ) :
    (addList l m).getD i 0 = l.getD i 0 + m.getD i 0 := by
  induction l generalizing m i with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      cases i with
      | zero => simp
      | succ i =>
        rw [addList_cons_cons, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
        exact ih m i

@[simp] theorem smulList_nil (q : ℚ) : smulList q [] = [] := rfl

@[simp] theorem smulList_cons (q : ℚ) (a : QC) (l : List QC) :
    smulList q (a :: l) = smulQ q a :: smulList q l := rfl

@[simp] theorem length_smulList (q : ℚ) (l : List QC) : (smulList q l).length = l.length :=
  List.length_map ..

/-- A list sum of `f` over `l` as a `Finset` sum over the indices. -/
theorem sum_map_eq_sum_range {M : Type*} [AddCommMonoid M] (f : QC → M) :
    ∀ l : List QC, (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i 0)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      sum_map_eq_sum_range f l, add_comm]
    simp only [List.getD_cons_zero, List.getD_cons_succ]

end QC

/-! ### Polynomials in the monomial basis -/

/-- POLY-6. A polynomial with Gaussian-rational coefficients, as its coefficient list
(index = degree). -/
abbrev PolyQC := List QC

namespace PolyQC

open QC

/-- POLY-6. The polynomial `∑ᵢ lᵢ Xⁱ`, by Horner's scheme. -/
noncomputable def toPoly : PolyQC → ℂ[X]
  | [] => 0
  | a :: l => C (toC a) + X * toPoly l

@[simp] theorem toPoly_nil : toPoly [] = 0 := rfl

@[simp] theorem toPoly_cons (a : QC) (l : PolyQC) :
    toPoly (a :: l) = C (toC a) + X * toPoly l := rfl

/-- POLY-6. The `i`-th coefficient of `toPoly l` is `lᵢ` (zero beyond the list). -/
theorem coeff_toPoly (l : PolyQC) (i : ℕ) : (toPoly l).coeff i = toC (l.getD i 0) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i => simp [coeff_X_mul, ih]

/-- POLY-6. `deg (toPoly l) ≤ length l - 1`. -/
theorem natDegree_toPoly_le (l : PolyQC) : (toPoly l).natDegree ≤ l.length - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
    rw [coeff_toPoly, List.getD_eq_default _ _ (by omega), toC_zero]

theorem toPoly_addList (l m : PolyQC) : toPoly (addList l m) = toPoly l + toPoly m := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      rw [addList_cons_cons, toPoly_cons, toPoly_cons, toPoly_cons, ih, toC_add, Polynomial.C_add]
      ring

theorem toPoly_smulList (q : ℚ) (l : PolyQC) :
    toPoly (smulList q l) = C (q : ℂ) * toPoly l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [smulList_cons, toPoly_cons, toPoly_cons, ih, toC_smulQ, Polynomial.C_mul]
    ring

end PolyQC

/-! ### Chebyshev series with Gaussian-rational coefficients -/

/-- POLY-6. A Chebyshev series with Gaussian-rational coefficients, as its coefficient list
(index `k` ↦ coefficient of `T k`). -/
abbrev ChebQC := List QC

namespace ChebQC

open QC

/-- POLY-6. The polynomial `∑ₖ cₖ Tₖ`. -/
noncomputable def toPoly (c : ChebQC) : ℂ[X] :=
  ∑ k ∈ Finset.range c.length, C (toC (c.getD k 0)) * T ℂ k

/-- The shifted sum `∑ₖ cₖ T_{k₀+k}`, the structural-recursion form of `toPoly`. -/
noncomputable def toPolyFrom : ℕ → ChebQC → ℂ[X]
  | _, [] => 0
  | k₀, a :: c => C (toC a) * T ℂ k₀ + toPolyFrom (k₀ + 1) c

@[simp] theorem toPolyFrom_nil (k₀ : ℕ) : toPolyFrom k₀ [] = 0 := rfl

@[simp] theorem toPolyFrom_cons (k₀ : ℕ) (a : QC) (c : ChebQC) :
    toPolyFrom k₀ (a :: c) = C (toC a) * T ℂ k₀ + toPolyFrom (k₀ + 1) c := rfl

theorem toPolyFrom_eq_sum (k₀ : ℕ) (c : ChebQC) :
    toPolyFrom k₀ c =
      ∑ k ∈ Finset.range c.length, C (toC (c.getD k 0)) * T ℂ ((k₀ + k : ℕ) : ℤ) := by
  induction c generalizing k₀ with
  | nil => simp
  | cons a c ih =>
    rw [toPolyFrom_cons, ih, List.length_cons, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_right_comm k₀ 1 k, Nat.add_assoc]

theorem toPoly_eq_toPolyFrom (c : ChebQC) : toPoly c = toPolyFrom 0 c := by
  rw [toPoly, toPolyFrom_eq_sum]
  simp only [Nat.zero_add]

@[simp] theorem toPoly_nil : toPoly [] = 0 := by simp [toPoly]

@[simp] theorem toPoly_singleton (a : QC) : toPoly [a] = C (toC a) := by
  simp [toPoly]

theorem toPoly_cons (a : QC) (c : ChebQC) : toPoly (a :: c) = C (toC a) + toPolyFrom 1 c := by
  rw [toPoly_eq_toPolyFrom, toPolyFrom_cons, Nat.cast_zero, T_zero, mul_one, Nat.zero_add]

/-- POLY-6. `deg (∑ₖ cₖ Tₖ) ≤ length c - 1`. -/
theorem natDegree_toPoly_le (c : ChebQC) : (toPoly c).natDegree ≤ c.length - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_T k).le.trans ?_)
  have := Finset.mem_range.mp hk
  omega

theorem toPolyFrom_addList (k₀ : ℕ) (c d : ChebQC) :
    toPolyFrom k₀ (addList c d) = toPolyFrom k₀ c + toPolyFrom k₀ d := by
  induction c generalizing d k₀ with
  | nil => simp
  | cons a c ih =>
    cases d with
    | nil => simp
    | cons b d =>
      rw [addList_cons_cons, toPolyFrom_cons, toPolyFrom_cons, toPolyFrom_cons, ih, toC_add,
        Polynomial.C_add]
      ring

theorem toPolyFrom_smulList (k₀ : ℕ) (q : ℚ) (c : ChebQC) :
    toPolyFrom k₀ (smulList q c) = C (q : ℂ) * toPolyFrom k₀ c := by
  induction c generalizing k₀ with
  | nil => simp
  | cons a c ih =>
    rw [smulList_cons, toPolyFrom_cons, toPolyFrom_cons, ih, toC_smulQ, Polynomial.C_mul]
    ring

/-- POLY-6. `∑ₖ (cₖ + dₖ) Tₖ = ∑ₖ cₖ Tₖ + ∑ₖ dₖ Tₖ`. -/
theorem toPoly_addList (c d : ChebQC) : toPoly (addList c d) = toPoly c + toPoly d := by
  simp only [toPoly_eq_toPolyFrom, toPolyFrom_addList]

theorem toPoly_smulList (q : ℚ) (c : ChebQC) : toPoly (smulList q c) = C (q : ℂ) * toPoly c := by
  simp only [toPoly_eq_toPolyFrom, toPolyFrom_smulList]

/-- POLY-6. `2 X ∑ₖ cₖ T_{k₀+1+k} = ∑ₖ cₖ T_{k₀+2+k} + ∑ₖ cₖ T_{k₀+k}`, from
`2 X T_{k+1} = T_{k+2} + T_k`. -/
theorem two_mul_X_mul_toPolyFrom_succ (k₀ : ℕ) (c : ChebQC) :
    2 * X * toPolyFrom (k₀ + 1) c = toPolyFrom (k₀ + 2) c + toPolyFrom k₀ c := by
  induction c generalizing k₀ with
  | nil => simp
  | cons a c ih =>
    rw [toPolyFrom_cons, toPolyFrom_cons, toPolyFrom_cons]
    have h : 2 * X * toPolyFrom (k₀ + 1 + 1) c =
        toPolyFrom (k₀ + 2 + 1) c + toPolyFrom (k₀ + 1) c :=
      ih (k₀ + 1)
    linear_combination (C (toC a)) * two_mul_X_mul_T k₀ + h

/-! ### Multiplication by `X` and the change of basis -/

/-- POLY-6. Multiplication by `X` in the Chebyshev basis: `(mulX c)ₖ = (c_{k-1} + c_{k+1}) / 2`
for `k ≥ 2`, `(mulX c)₁ = c₀ + c₂ / 2`, `(mulX c)₀ = c₁ / 2`.  Implemented as the sum of the
shifted-up list `[0, c₀, c₁/2, c₂/2, …]` and the shifted-down list `[c₁/2, c₂/2, …]`. -/
def mulX : ChebQC → ChebQC
  | [] => []
  | a :: c => addList (0 :: a :: smulList (1 / 2) c) (smulList (1 / 2) c)

@[simp] theorem mulX_nil : mulX [] = [] := rfl

theorem mulX_cons (a : QC) (c : ChebQC) :
    mulX (a :: c) = addList (0 :: a :: smulList (1 / 2) c) (smulList (1 / 2) c) := rfl

theorem length_mulX_le : ∀ c : ChebQC, (mulX c).length ≤ c.length + 1
  | [] => by simp
  | a :: c => by
    rw [mulX_cons, length_addList]
    simp only [List.length_cons, length_smulList]
    omega

/-- POLY-6. `mulX` is multiplication by `X`: `∑ₖ (mulX c)ₖ Tₖ = X ∑ₖ cₖ Tₖ`. -/
theorem toPoly_mulX (c : ChebQC) : toPoly (mulX c) = X * toPoly c := by
  cases c with
  | nil => simp
  | cons a c =>
    rw [mulX_cons, toPoly_eq_toPolyFrom, toPoly_eq_toPolyFrom, toPolyFrom_addList, toPolyFrom_cons,
      toPolyFrom_cons, toPolyFrom_cons, toPolyFrom_smulList, toPolyFrom_smulList, toC_zero,
      Polynomial.C_0, zero_mul, zero_add]
    simp only [Nat.zero_add, Nat.reduceAdd, Nat.cast_zero, Nat.cast_one, T_zero, T_one, mul_one]
    have h := two_mul_X_mul_toPolyFrom_succ 0 c
    simp only [Nat.zero_add] at h
    have h2 : (C ((1 / 2 : ℚ) : ℂ) : ℂ[X]) * 2 = 1 := by
      rw [← Polynomial.C_ofNat, ← Polynomial.C_mul, ← Polynomial.C_1]
      congr 1
      norm_num
    linear_combination (-C ((1 / 2 : ℚ) : ℂ)) * h + (X * toPolyFrom 1 c) * h2

/-- POLY-6. Monomial → Chebyshev change of basis by Horner's scheme
`∑ᵢ lᵢ Xⁱ = l₀ + X (l₁ + X (l₂ + ⋯))`, with `mulX` for the multiplication by `X`. -/
def ofMonomials : PolyQC → ChebQC
  | [] => []
  | a :: l => addList [a] (mulX (ofMonomials l))

@[simp] theorem ofMonomials_nil : ofMonomials [] = [] := rfl

theorem ofMonomials_cons (a : QC) (l : PolyQC) :
    ofMonomials (a :: l) = addList [a] (mulX (ofMonomials l)) := rfl

/-- POLY-6. The Chebyshev coefficient list is no longer than the monomial one. -/
theorem length_ofMonomials_le : ∀ l : PolyQC, (ofMonomials l).length ≤ l.length
  | [] => le_rfl
  | a :: l => by
    rw [ofMonomials_cons, length_addList, List.length_singleton, List.length_cons]
    have h1 := length_mulX_le (ofMonomials l)
    have h2 := length_ofMonomials_le l
    omega

/-- POLY-6. Correctness of the change of basis: `∑ₖ (ofMonomials l)ₖ Tₖ = ∑ᵢ lᵢ Xⁱ`. -/
theorem toPoly_ofMonomials (l : PolyQC) : toPoly (ofMonomials l) = PolyQC.toPoly l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [ofMonomials_cons, toPoly_addList, toPoly_mulX, ih, PolyQC.toPoly_cons, toPoly_singleton]

/-! ### The `ChebSeries` and the `ℓ¹` bound -/

/-- Coefficients beyond the list vanish, so the support lies in `range c.length`. -/
theorem mem_range_of_toC_getD_ne_zero (c : ChebQC) (k : ℕ) (hk : toC (c.getD k 0) ≠ 0) :
    k ∈ Finset.range c.length :=
  Finset.mem_range.mpr <| Nat.lt_of_not_le fun h =>
    hk (by rw [List.getD_eq_default _ _ h, toC_zero])

/-- POLY-6. The `ChebSeries` (finitely supported `ℕ →₀ ℂ`) with coefficients `toC cₖ`. -/
noncomputable def toSeries (c : ChebQC) : ChebSeries :=
  ⟨Finsupp.onFinset (Finset.range c.length) (fun k => toC (c.getD k 0))
    (mem_range_of_toC_getD_ne_zero c)⟩

@[simp] theorem coeff_toSeries (c : ChebQC) (k : ℕ) : (toSeries c).coeff k = toC (c.getD k 0) :=
  rfl

/-- POLY-6. `toSeries` is compatible with `toPoly`. -/
theorem toSeries_toPoly (c : ChebQC) : (toSeries c).toPoly = toPoly c := by
  rw [ChebSeries.toPoly, toPoly]
  exact Finsupp.onFinset_sum (mem_range_of_toC_getD_ne_zero c) fun _ => by simp

/-- POLY-6. The `ℓ¹` norm `∑ₖ ‖cₖ‖` of the coefficients. -/
noncomputable def l1 (c : ChebQC) : ℝ := ∑ k ∈ Finset.range c.length, ‖toC (c.getD k 0)‖

theorem l1_toSeries (c : ChebQC) : (toSeries c).l1 = l1 c := by
  rw [ChebSeries.l1, l1]
  exact Finsupp.onFinset_sum (mem_range_of_toC_getD_ne_zero c) fun _ => norm_zero

/-- POLY-6. A computable rational upper bound `∑ₖ (|Re cₖ| + |Im cₖ|)` on `l1`. -/
def l1Bound (c : ChebQC) : ℚ := (c.map fun z => |z.1| + |z.2|).sum

theorem l1_le_l1Bound (c : ChebQC) : l1 c ≤ (l1Bound c : ℝ) := by
  rw [l1Bound, sum_map_eq_sum_range, Rat.cast_sum, l1]
  exact Finset.sum_le_sum fun k _ => norm_toC_le _

/-- POLY-6. `‖∑ₖ cₖ Tₖ‖_∞ ≤ ∑ₖ ‖cₖ‖`. -/
theorem supNorm_toPoly_le_l1 (c : ChebQC) : supNorm (toPoly c) ≤ l1 c := by
  rw [← toSeries_toPoly, ← l1_toSeries]
  exact ChebSeries.supNorm_toPoly_le_l1 _

/-- POLY-6. `‖∑ₖ cₖ Tₖ‖_∞ ≤ l1Bound c`, with a computable right-hand side. -/
theorem supNorm_toPoly_le_l1Bound (c : ChebQC) : supNorm (toPoly c) ≤ (l1Bound c : ℝ) :=
  (supNorm_toPoly_le_l1 c).trans (l1_le_l1Bound c)

end ChebQC

end QSVT.Poly
