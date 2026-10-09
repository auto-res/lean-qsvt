/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Polynomial.ChebCoeff
import QSVT.QSP.Poly

/-!
# QSP polynomials in the Chebyshev basis (formal-spec CERT-B, part 2: specification layer)

The QSP recursion `qspPoly` (QSP-3) rewritten on Chebyshev coefficient lists over `ℂ`.  This is
the *specification* of the certificate checker `QSVT.Certificate.check` (`PhaseCheck.lean`): the
interval computation there encloses, coefficient by coefficient, the exact complex lists defined
here, and the theorems here connect the lists back to `Polynomial ℂ`.

* `ChebC := List ℂ` : a Chebyshev series by its coefficient list (index `k` ↦ coefficient of
  `T k`), with `ChebC.toPoly c = ∑ₖ cₖ Tₖ`.
* Operations with their `toPoly` equations: `addC` (pointwise, zero padding), `smulC a` (scalar),
  `mulX` (multiplication by `X`, the rule `(mulX c)ₖ = (c_{k-1} + c_{k+1}) / 2`,
  `(mulX c)₁ = c₀ + c₂ / 2`, `(mulX c)₀ = c₁ / 2`, mirroring `ChebQC.mulX`), `oneSubXSq`
  (multiplication by `1 - X²`), `reC` (coefficientwise real part).
* `stepC φ P Q` : one QSP step `P' = e^{iφ}(X P + (1 - X²) Q)`, `Q' = e^{-iφ}(P - X Q)`, and
  `qspChebC : List ℝ → ChebC × ChebC` with the key theorem
  `toPoly_qspChebC : (toPoly (qspChebC Φ).1, toPoly (qspChebC Φ).2) = qspPoly Φ`.
* Bounds: `norm_eval_toPoly_le_l1 : ‖(toPoly c)(x)‖ ≤ ∑ₖ ‖cₖ‖` on `[-1, 1]` (POLY-5,
  `norm_eval_T_le_one`) with `l1 c = (c.map norm).sum`, and `eval_toPoly_reC` identifying
  `(toPoly (reC c))(x)` with the real part of `(toPoly c)(x)` at real `x`.
* `target t` : the real target `∑ₖ tₖ Tₖ` of a rational list `t : List ℚ` (`target_eq`,
  `eval_target_ofReal`).

Everything here is noncomputable (coefficients in `ℂ`); the computable interval layer is
`QSVT.Certificate.PhaseCheck`.
-/

namespace QSVT.Certificate

-- Only `T` is opened: `Polynomial.Chebyshev.C` (third kind) would shadow `Polynomial.C` lemmas.
open Polynomial
open Polynomial.Chebyshev (T T_zero T_one)
open QSVT.Poly QSVT.QSP

/-- CERT-B. A Chebyshev series with complex coefficients, as its coefficient list
(index `k` ↦ coefficient of `T k`). -/
abbrev ChebC := List ℂ

namespace ChebC

/-! ### `toPoly` -/

/-- CERT-B. The polynomial `∑ₖ cₖ Tₖ`. -/
noncomputable def toPoly (c : ChebC) : ℂ[X] :=
  ∑ k ∈ Finset.range c.length, C (c.getD k 0) * T ℂ k

/-- The shifted sum `∑ₖ cₖ T_{k₀+k}`, the structural-recursion form of `toPoly`. -/
noncomputable def toPolyFrom : ℕ → ChebC → ℂ[X]
  | _, [] => 0
  | k₀, a :: c => C a * T ℂ k₀ + toPolyFrom (k₀ + 1) c

@[simp] theorem toPolyFrom_nil (k₀ : ℕ) : toPolyFrom k₀ [] = 0 := rfl

@[simp] theorem toPolyFrom_cons (k₀ : ℕ) (a : ℂ) (c : ChebC) :
    toPolyFrom k₀ (a :: c) = C a * T ℂ k₀ + toPolyFrom (k₀ + 1) c := rfl

theorem toPolyFrom_eq_sum (k₀ : ℕ) (c : ChebC) :
    toPolyFrom k₀ c =
      ∑ k ∈ Finset.range c.length, C (c.getD k 0) * T ℂ ((k₀ + k : ℕ) : ℤ) := by
  induction c generalizing k₀ with
  | nil => simp
  | cons a c ih =>
    rw [toPolyFrom_cons, ih, List.length_cons, Finset.sum_range_succ', add_comm]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_right_comm k₀ 1 k, Nat.add_assoc]

theorem toPoly_eq_toPolyFrom (c : ChebC) : toPoly c = toPolyFrom 0 c := by
  rw [toPoly, toPolyFrom_eq_sum]
  simp only [Nat.zero_add]

@[simp] theorem toPoly_nil : toPoly [] = 0 := by simp [toPoly]

@[simp] theorem toPoly_singleton (a : ℂ) : toPoly [a] = C a := by
  simp [toPoly]

/-! ### Addition and scalar multiplication -/

/-- CERT-B. Pointwise addition of coefficient lists, padding the shorter one with zeros. -/
noncomputable def addC : ChebC → ChebC → ChebC
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addC l m

@[simp] theorem addC_nil (m : ChebC) : addC [] m = m := rfl

@[simp] theorem addC_nil_right (l : ChebC) : addC l [] = l := by
  cases l <;> rfl

@[simp] theorem addC_cons_cons (a b : ℂ) (l m : ChebC) :
    addC (a :: l) (b :: m) = (a + b) :: addC l m := rfl

/-- CERT-B. Scalar multiplication of a coefficient list by `a : ℂ`. -/
noncomputable def smulC (a : ℂ) (c : ChebC) : ChebC := c.map (a * ·)

@[simp] theorem smulC_nil (a : ℂ) : smulC a [] = [] := rfl

@[simp] theorem smulC_cons (a b : ℂ) (c : ChebC) : smulC a (b :: c) = a * b :: smulC a c := rfl

theorem toPolyFrom_addC (k₀ : ℕ) (c d : ChebC) :
    toPolyFrom k₀ (addC c d) = toPolyFrom k₀ c + toPolyFrom k₀ d := by
  induction c generalizing d k₀ with
  | nil => simp
  | cons a c ih =>
    cases d with
    | nil => simp
    | cons b d =>
      rw [addC_cons_cons, toPolyFrom_cons, toPolyFrom_cons, toPolyFrom_cons, ih, C_add]
      ring

theorem toPolyFrom_smulC (k₀ : ℕ) (a : ℂ) (c : ChebC) :
    toPolyFrom k₀ (smulC a c) = C a * toPolyFrom k₀ c := by
  induction c generalizing k₀ with
  | nil => simp
  | cons b c ih =>
    rw [smulC_cons, toPolyFrom_cons, toPolyFrom_cons, ih, C_mul]
    ring

/-- CERT-B. `∑ₖ (cₖ + dₖ) Tₖ = ∑ₖ cₖ Tₖ + ∑ₖ dₖ Tₖ`. -/
theorem toPoly_addC (c d : ChebC) : toPoly (addC c d) = toPoly c + toPoly d := by
  simp only [toPoly_eq_toPolyFrom, toPolyFrom_addC]

/-- CERT-B. `∑ₖ (a cₖ) Tₖ = a ∑ₖ cₖ Tₖ`. -/
theorem toPoly_smulC (a : ℂ) (c : ChebC) : toPoly (smulC a c) = C a * toPoly c := by
  simp only [toPoly_eq_toPolyFrom, toPolyFrom_smulC]

/-! ### Multiplication by `X` and by `1 - X²` -/

/-- CERT-B. `2 X ∑ₖ cₖ T_{k₀+1+k} = ∑ₖ cₖ T_{k₀+2+k} + ∑ₖ cₖ T_{k₀+k}`, from
`2 X T_{k+1} = T_{k+2} + T_k`. -/
theorem two_mul_X_mul_toPolyFrom_succ (k₀ : ℕ) (c : ChebC) :
    2 * X * toPolyFrom (k₀ + 1) c = toPolyFrom (k₀ + 2) c + toPolyFrom k₀ c := by
  induction c generalizing k₀ with
  | nil => simp
  | cons a c ih =>
    rw [toPolyFrom_cons, toPolyFrom_cons, toPolyFrom_cons]
    have h : 2 * X * toPolyFrom (k₀ + 1 + 1) c =
        toPolyFrom (k₀ + 2 + 1) c + toPolyFrom (k₀ + 1) c :=
      ih (k₀ + 1)
    linear_combination (C a) * two_mul_X_mul_T k₀ + h

/-- CERT-B. Multiplication by `X` in the Chebyshev basis: `(mulX c)ₖ = (c_{k-1} + c_{k+1}) / 2`
for `k ≥ 2`, `(mulX c)₁ = c₀ + c₂ / 2`, `(mulX c)₀ = c₁ / 2`.  Implemented as the sum of the
shifted-up list `[0, c₀, c₁/2, c₂/2, …]` and the shifted-down list `[c₁/2, c₂/2, …]`; the
factor `1/2` is written as the cast of the rational `1/2` so that the interval layer can mirror
it with a rational scaling. -/
noncomputable def mulX : ChebC → ChebC
  | [] => []
  | a :: c => addC (0 :: a :: smulC ((1 / 2 : ℚ) : ℂ) c) (smulC ((1 / 2 : ℚ) : ℂ) c)

@[simp] theorem mulX_nil : mulX [] = [] := rfl

theorem mulX_cons (a : ℂ) (c : ChebC) :
    mulX (a :: c) = addC (0 :: a :: smulC ((1 / 2 : ℚ) : ℂ) c) (smulC ((1 / 2 : ℚ) : ℂ) c) := rfl

/-- CERT-B. `mulX` is multiplication by `X`: `∑ₖ (mulX c)ₖ Tₖ = X ∑ₖ cₖ Tₖ`. -/
theorem toPoly_mulX (c : ChebC) : toPoly (mulX c) = X * toPoly c := by
  cases c with
  | nil => simp
  | cons a c =>
    rw [mulX_cons, toPoly_eq_toPolyFrom, toPoly_eq_toPolyFrom, toPolyFrom_addC, toPolyFrom_cons,
      toPolyFrom_cons, toPolyFrom_cons, toPolyFrom_smulC, toPolyFrom_smulC, C_0, zero_mul,
      zero_add]
    simp only [Nat.zero_add, Nat.reduceAdd, Nat.cast_zero, Nat.cast_one, T_zero, T_one, mul_one]
    have h := two_mul_X_mul_toPolyFrom_succ 0 c
    simp only [Nat.zero_add] at h
    have h2 : (C ((1 / 2 : ℚ) : ℂ) : ℂ[X]) * 2 = 1 := by
      rw [← C_ofNat, ← C_mul, ← C_1]
      congr 1
      norm_num
    linear_combination (-C ((1 / 2 : ℚ) : ℂ)) * h + (X * toPolyFrom 1 c) * h2

/-- CERT-B. Multiplication by `1 - X²`: `c - X (X c)`. -/
noncomputable def oneSubXSq (c : ChebC) : ChebC := addC c (smulC (-1) (mulX (mulX c)))

/-- CERT-B. `∑ₖ (oneSubXSq c)ₖ Tₖ = (1 - X²) ∑ₖ cₖ Tₖ`. -/
theorem toPoly_oneSubXSq (c : ChebC) : toPoly (oneSubXSq c) = (1 - X ^ 2) * toPoly c := by
  rw [oneSubXSq, toPoly_addC, toPoly_smulC, toPoly_mulX, toPoly_mulX, C_neg, C_1]
  ring

/-! ### The QSP recursion -/

/-- CERT-B. One QSP step in the Chebyshev basis (QSP-3, `qspPoly_cons`):
`P' = e^{iφ} (X P + (1 - X²) Q)`, `Q' = e^{-iφ} (P - X Q)`. -/
noncomputable def stepC (φ : ℝ) (P Q : ChebC) : ChebC × ChebC :=
  (smulC (Complex.exp (Complex.I * φ)) (addC (mulX P) (oneSubXSq Q)),
    smulC (Complex.exp (-(Complex.I * φ))) (addC P (smulC (-1) (mulX Q))))

/-- CERT-B. The Chebyshev coefficient lists of the QSP polynomials `(P, Q)` of a phase list:
base `([1], [])` (`P = 1 = T₀`, `Q = 0`), then `stepC`. -/
noncomputable def qspChebC : List ℝ → ChebC × ChebC
  | [] => ([1], [])
  | φ :: Φ => stepC φ (qspChebC Φ).1 (qspChebC Φ).2

@[simp] theorem qspChebC_nil : qspChebC [] = ([1], []) := rfl

theorem qspChebC_cons (φ : ℝ) (Φ : List ℝ) :
    qspChebC (φ :: Φ) = stepC φ (qspChebC Φ).1 (qspChebC Φ).2 := rfl

/-- CERT-B. The Chebyshev recursion computes `qspPoly` (QSP-3), both components. -/
theorem toPoly_qspChebC_fst_snd (Φ : List ℝ) :
    toPoly (qspChebC Φ).1 = (qspPoly Φ).1 ∧ toPoly (qspChebC Φ).2 = (qspPoly Φ).2 := by
  induction Φ with
  | nil => simp
  | cons φ Φ ih =>
    rw [qspChebC_cons, qspPoly_cons]
    simp only [stepC]
    rw [toPoly_smulC, toPoly_addC, toPoly_mulX, toPoly_oneSubXSq, ih.1, ih.2, toPoly_smulC,
      toPoly_addC, toPoly_smulC, toPoly_mulX, ih.1, ih.2, C_neg, C_1]
    exact ⟨rfl, by ring⟩

/-- CERT-B. The Chebyshev recursion computes `qspPoly` (QSP-3). -/
theorem toPoly_qspChebC (Φ : List ℝ) :
    (toPoly (qspChebC Φ).1, toPoly (qspChebC Φ).2) = qspPoly Φ :=
  Prod.ext (toPoly_qspChebC_fst_snd Φ).1 (toPoly_qspChebC_fst_snd Φ).2

/-! ### The `ℓ¹` bound -/

/-- A list sum of `f` over `l` as a `Finset` sum over the indices. -/
theorem sum_map_eq_sum_range {α M : Type*} [Zero α] [AddCommMonoid M] (f : α → M) :
    ∀ l : List α, (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i 0)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      sum_map_eq_sum_range f l, add_comm]
    simp only [List.getD_cons_zero, List.getD_cons_succ]

/-- CERT-B. The `ℓ¹` norm `∑ₖ ‖cₖ‖` of the coefficients. -/
noncomputable def l1 (c : ChebC) : ℝ := (c.map norm).sum

theorem l1_eq_sum (c : ChebC) : l1 c = ∑ k ∈ Finset.range c.length, ‖c.getD k 0‖ :=
  sum_map_eq_sum_range norm c

/-- CERT-B. `‖∑ₖ cₖ Tₖ(x)‖ ≤ ∑ₖ ‖cₖ‖` for `x ∈ [-1, 1]` (POLY-5). -/
theorem norm_eval_toPoly_le (c : ChebC) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(toPoly c).eval (x : ℂ)‖ ≤ ∑ k ∈ Finset.range c.length, ‖c.getD k 0‖ := by
  rw [toPoly, eval_finsetSum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [eval_mul, eval_C, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_eval_T_le_one k hx)

/-- CERT-B. `‖∑ₖ cₖ Tₖ(x)‖ ≤ l1 c` for `x ∈ [-1, 1]`. -/
theorem norm_eval_toPoly_le_l1 (c : ChebC) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(toPoly c).eval (x : ℂ)‖ ≤ l1 c := by
  rw [l1_eq_sum]
  exact norm_eval_toPoly_le c hx

/-- CERT-B. `‖∑ₖ cₖ Tₖ‖_∞ ≤ l1 c`. -/
theorem supNorm_toPoly_le_l1 (c : ChebC) : supNorm (toPoly c) ≤ l1 c :=
  supNorm_le_of_forall fun _ hx => norm_eval_toPoly_le_l1 c hx

/-! ### Real parts -/

/-- `getD` through a `map` whose function fixes the default. -/
theorem getD_map_of_map_zero {α β : Type*} [Zero α] [Zero β] {f : α → β} (hf : f 0 = 0)
    (l : List α) (k : ℕ) : (l.map f).getD k 0 = f (l.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? with
  | none => simp [hf]
  | some a => rfl

/-- CERT-B. The coefficientwise real part `(Re cₖ)ₖ`, embedded back into `ℂ`. -/
noncomputable def reC (c : ChebC) : ChebC := c.map fun z => ((z.re : ℝ) : ℂ)

@[simp] theorem reC_nil : reC [] = [] := rfl

@[simp] theorem reC_cons (a : ℂ) (c : ChebC) : reC (a :: c) = ((a.re : ℝ) : ℂ) :: reC c := rfl

@[simp] theorem length_reC (c : ChebC) : (reC c).length = c.length := List.length_map ..

theorem getD_reC (c : ChebC) (k : ℕ) : (reC c).getD k 0 = (((c.getD k 0).re : ℝ) : ℂ) :=
  getD_map_of_map_zero (by simp) c k

/-- CERT-B. At a real point, `(toPoly c)(x)` has real part `∑ₖ Re(cₖ) Tₖ(x)`. -/
theorem re_eval_toPoly (c : ChebC) (x : ℝ) :
    ((toPoly c).eval (x : ℂ)).re =
      ∑ k ∈ Finset.range c.length, (c.getD k 0).re * (T ℝ k).eval x := by
  rw [toPoly, eval_finsetSum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, ← Polynomial.Chebyshev.complex_ofReal_eval_T, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- CERT-B. At a real point, `(toPoly (reC c))(x)` is the real part of `(toPoly c)(x)`. -/
theorem eval_toPoly_reC (c : ChebC) (x : ℝ) :
    (toPoly (reC c)).eval (x : ℂ) = ((((toPoly c).eval (x : ℂ)).re : ℝ) : ℂ) := by
  rw [re_eval_toPoly, toPoly, eval_finsetSum, length_reC, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, getD_reC, ← Polynomial.Chebyshev.complex_ofReal_eval_T, Complex.ofReal_mul]

/-! ### The real target -/

/-- CERT-B. The target polynomial `∑ₖ tₖ Tₖ` of a rational Chebyshev coefficient list. -/
noncomputable def target (t : List ℚ) : ℂ[X] := toPoly (t.map fun q => ((q : ℚ) : ℂ))

theorem getD_map_ratCast (t : List ℚ) (k : ℕ) :
    (t.map fun q => ((q : ℚ) : ℂ)).getD k 0 = ((t.getD k 0 : ℚ) : ℂ) :=
  getD_map_of_map_zero (by simp) t k

/-- CERT-B. `target t = ∑ₖ tₖ Tₖ`, written out. -/
theorem target_eq (t : List ℚ) :
    target t = ∑ k ∈ Finset.range t.length, C ((t.getD k 0 : ℚ) : ℂ) * T ℂ k := by
  rw [target, toPoly, List.length_map]
  exact Finset.sum_congr rfl fun k _ => by rw [getD_map_ratCast]

/-- The real target is its own real part. -/
theorem reC_map_ratCast (t : List ℚ) :
    reC (t.map fun q => ((q : ℚ) : ℂ)) = t.map fun q => ((q : ℚ) : ℂ) := by
  rw [reC, List.map_map]
  exact List.map_congr_left fun q _ => by simp

/-- CERT-B. At a real point, `target t` takes the real value `∑ₖ tₖ Tₖ(x)`. -/
theorem eval_target_ofReal (t : List ℚ) (x : ℝ) :
    (target t).eval (x : ℂ) =
      ((∑ k ∈ Finset.range t.length, (t.getD k 0 : ℝ) * (T ℝ k).eval x : ℝ) : ℂ) := by
  rw [target, ← reC_map_ratCast, eval_toPoly_reC, re_eval_toPoly, List.length_map]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [getD_map_ratCast, Complex.ratCast_re]

/-- CERT-B. `target t` is real at real points: it equals its own real part. -/
theorem ofReal_re_eval_target (t : List ℚ) (x : ℝ) :
    ((((target t).eval (x : ℂ)).re : ℝ) : ℂ) = (target t).eval (x : ℂ) := by
  rw [eval_target_ofReal, Complex.ofReal_re]

end ChebC

end QSVT.Certificate
