/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import LeanCert.Tactic
import QSVT.Polynomial.ChebCoeff
import QSVT.Polynomial.SupNorm

/-!
# Certified sup-norm bounds for rational polynomials (formal-spec CERT-B, part 1)

Glue between the statements that LeanCert certifies and the `supNorm`/`PolyQC` layer of
`QSVT.Polynomial`.

* `PolyQ := List ℚ` : a real polynomial by its rational coefficient list (index = degree).
* `PolyQ.horner l x` : Horner evaluation over `ℝ`, by structural recursion, so that for a
  *concrete* list `simp only [l, PolyQ.horner]` (optionally followed by `push_cast`) unfolds
  `l.horner x` to the plain real expression `a₀ + x * (a₁ + x * (a₂ + x * 0))`, which is the
  input language of LeanCert's tactics.
* `PolyQ.toPoly l : ℂ[X]` : the complex polynomial, through `PolyQC.toPoly` (POLY-6), with
  `eval_toPoly_ofReal : (toPoly l).eval (x : ℂ) = ((l.horner x : ℝ) : ℂ)` and
  `norm_eval_toPoly : ‖(toPoly l).eval (x : ℂ)‖ = |l.horner x|`.
* Transfer lemmas from a two-sided real bound `c₁ ≤ l.horner x ∧ l.horner x ≤ c₂` (the goal shape
  LeanCert accepts; see below) to statements about `Polynomial ℂ`:
  `supNorm_toPoly_le_of_horner`, `supNorm_sub_le_of_horner`, `norm_eval_toPoly_sub_le`,
  `forall_norm_eval_sub_le_of_two_sided`, `forall_re_eval_mem_Icc_of_horner`.
* `PolyQ.sub` : pointwise difference of coefficient lists (`horner_sub`, `toPoly_sub`).
* A worked example, `cheb3_horner_bound : ∀ x ∈ Icc (-1) 1, -1 ≤ T₃(x) ∧ T₃(x) ≤ 1` for
  `T₃ = 4x³ − 3x`, certified by LeanCert in kernel mode, and its sup-norm corollary
  `supNorm_cheb3_le_one`.

## Using LeanCert (recipe)

For a concrete `p : PolyQ` and rational interval endpoints and bounds, the incantation is
```
theorem p_bound : ∀ x ∈ Set.Icc (a : ℝ) b, c₁ ≤ p.horner x ∧ p.horner x ≤ c₂ := by
  simp only [p, PolyQ.horner]
  push_cast
  leancert (trust := kernel)        -- or: bernstein_bound (trust := kernel)
```
Goal shapes accepted (LeanCert v4.34.1): `∀ x ∈ Set.Icc a b, e x ≤ c`, `c ≤ e x`, strict versions,
and conjunctions of these; constants may be decimal literals (`0.916`), rational literals
(`1/2`, `4461943376836953 / 5000000000000000`) or casts of rational literals (`((q : ℚ) : ℝ)`).
Not accepted: `|e x| ≤ c` (write the two-sided conjunction), `e x ∈ Set.Icc c₁ c₂`, exponent
literals such as `1e-9`, and goals pre-processed by `norm_num`/`simp` into
`∀ x, -1 ≤ x → x ≤ 1 → …` (the `Set.Icc` membership must be kept, hence `simp only`).

## Trust story

Every certificate in `QSVT.Certificate` is closed with `(trust := kernel)`: LeanCert reduces its
Boolean checker with `decide +kernel`, so the proof is checked by the Lean kernel alone and the
compiler (`Lean.ofReduceBool`, used by `native_decide`) is *not* trusted.  Consequently
`#print axioms` of every theorem here must list only `propext`, `Classical.choice` and
`Quot.sound`; this is audited in `test/QSVTTest/Certificate.lean`.  LeanCert itself is compiled
from source (no cached oleans), which costs about five minutes in CI; the numerical pre-search
(Taylor depth, subdivision) is untrusted and only produces the certificate.
-/

namespace QSVT.Certificate

open Polynomial QSVT.Poly

/-- CERT-B. A real polynomial with rational coefficients, as its coefficient list
(index = degree). -/
abbrev PolyQ := List ℚ

namespace PolyQ

/-! ### Horner evaluation over `ℝ` -/

/-- CERT-B. Horner evaluation `a₀ + x (a₁ + x (a₂ + ⋯))` over `ℝ`, by structural recursion so that
`simp only [horner]` unfolds a concrete coefficient list into a plain arithmetic expression. -/
def horner : PolyQ → ℝ → ℝ
  | [], _ => 0
  | a :: l, x => (a : ℝ) + x * horner l x

@[simp] theorem horner_nil (x : ℝ) : horner [] x = 0 := rfl

@[simp] theorem horner_cons (a : ℚ) (l : PolyQ) (x : ℝ) :
    horner (a :: l) x = (a : ℝ) + x * horner l x := rfl

/-- `horner` as a fold. -/
theorem horner_eq_foldr (l : PolyQ) (x : ℝ) :
    horner l x = l.foldr (fun (a : ℚ) acc => (a : ℝ) + x * acc) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ### The complex polynomial -/

/-- CERT-B. The Gaussian-rational coefficient list `(aᵢ, 0)` (POLY-6). -/
def toPolyQC (l : PolyQ) : PolyQC := l.map fun a => ((a, 0) : QC)

@[simp] theorem toPolyQC_nil : toPolyQC [] = [] := rfl

@[simp] theorem toPolyQC_cons (a : ℚ) (l : PolyQ) :
    toPolyQC (a :: l) = ((a, 0) : QC) :: toPolyQC l := rfl

/-- CERT-B. The complex polynomial `∑ᵢ aᵢ Xⁱ`. -/
noncomputable def toPoly (l : PolyQ) : ℂ[X] := PolyQC.toPoly (toPolyQC l)

@[simp] theorem toPoly_nil : toPoly [] = 0 := rfl

theorem toC_mk_zero (a : ℚ) : QC.toC ((a, 0) : QC) = (a : ℂ) := by
  simp [QC.toC]

@[simp] theorem toPoly_cons (a : ℚ) (l : PolyQ) :
    toPoly (a :: l) = C (a : ℂ) + X * toPoly l := by
  rw [toPoly, toPolyQC_cons, PolyQC.toPoly_cons, toC_mk_zero]
  rfl

/-- CERT-B. The `i`-th coefficient of `toPoly l` is `lᵢ` (zero beyond the list). -/
theorem coeff_toPoly (l : PolyQ) (i : ℕ) : (toPoly l).coeff i = ((l.getD i 0 : ℚ) : ℂ) := by
  rw [toPoly, PolyQC.coeff_toPoly]
  induction l generalizing i with
  | nil => simp [QC.toC]
  | cons a l ih =>
    cases i with
    | zero => simp [toC_mk_zero]
    | succ i => simpa using ih i

/-- CERT-B. `deg (toPoly l) ≤ length l - 1`. -/
theorem natDegree_toPoly_le (l : PolyQ) : (toPoly l).natDegree ≤ l.length - 1 := by
  rw [toPoly]
  exact (PolyQC.natDegree_toPoly_le _).trans (by simp [toPolyQC])

/-- CERT-B. At a real point, `toPoly l` evaluates to the (real) Horner value. -/
theorem eval_toPoly_ofReal (l : PolyQ) (x : ℝ) :
    (toPoly l).eval (x : ℂ) = ((horner l x : ℝ) : ℂ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [toPoly_cons, eval_add, eval_mul, eval_C, eval_X, ih, horner_cons]
    push_cast
    rfl

theorem re_eval_toPoly (l : PolyQ) (x : ℝ) : ((toPoly l).eval (x : ℂ)).re = horner l x := by
  rw [eval_toPoly_ofReal, Complex.ofReal_re]

theorem im_eval_toPoly (l : PolyQ) (x : ℝ) : ((toPoly l).eval (x : ℂ)).im = 0 := by
  rw [eval_toPoly_ofReal, Complex.ofReal_im]

/-- CERT-B. `‖(toPoly l)(x)‖ = |l.horner x|` for real `x`. -/
theorem norm_eval_toPoly (l : PolyQ) (x : ℝ) : ‖(toPoly l).eval (x : ℂ)‖ = |horner l x| := by
  rw [eval_toPoly_ofReal, Complex.norm_real, Real.norm_eq_abs]

/-! ### Differences of coefficient lists -/

/-- CERT-B. Pointwise difference of coefficient lists, padding the shorter one with zeros. -/
def sub : PolyQ → PolyQ → PolyQ
  | [], m => m.map Neg.neg
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a - b) :: sub l m

@[simp] theorem sub_nil_right (l : PolyQ) : sub l [] = l := by
  cases l <;> rfl

theorem horner_sub (l m : PolyQ) (x : ℝ) : horner (sub l m) x = horner l x - horner m x := by
  induction l generalizing m with
  | nil =>
    induction m with
    | nil => simp [sub]
    | cons b m ihm =>
      simp only [sub, List.map_cons, horner_cons, horner_nil] at ihm ⊢
      rw [ihm]
      push_cast
      ring
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      simp only [sub, horner_cons, ih]
      push_cast
      ring

theorem toPoly_sub (l m : PolyQ) : toPoly (sub l m) = toPoly l - toPoly m := by
  induction l generalizing m with
  | nil =>
    induction m with
    | nil => simp [sub]
    | cons b m ihm =>
      simp only [sub, List.map_cons, toPoly_cons, toPoly_nil] at ihm ⊢
      rw [ihm]
      push_cast
      simp only [map_neg]
      ring
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      simp only [sub, toPoly_cons, ih]
      push_cast
      simp only [map_sub]
      ring

/-! ### Transfer from two-sided real bounds -/

/-- CERT-B. A two-sided real bound around `c` gives a complex norm bound at a real point. -/
theorem norm_eval_toPoly_sub_le {l : PolyQ} {x c ε : ℝ}
    (h : c - ε ≤ horner l x ∧ horner l x ≤ c + ε) :
    ‖(toPoly l).eval (x : ℂ) - (c : ℂ)‖ ≤ ε := by
  rw [eval_toPoly_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- CERT-B. A two-sided Horner bound on `[a, b]` around a constant target `c` gives the pointwise
norm bound on `[a, b]` for the complex polynomial. -/
theorem forall_norm_eval_sub_le_of_two_sided {l : PolyQ} {a b c ε : ℝ}
    (h : ∀ x ∈ Set.Icc a b, c - ε ≤ horner l x ∧ horner l x ≤ c + ε) :
    ∀ x ∈ Set.Icc a b, ‖(toPoly l).eval (x : ℂ) - (c : ℂ)‖ ≤ ε :=
  fun x hx => norm_eval_toPoly_sub_le (h x hx)

/-- CERT-B. A two-sided Horner bound on `[a, b]` is a bound on the real part of the complex
polynomial (whose imaginary part vanishes, `im_eval_toPoly`). -/
theorem forall_re_eval_mem_Icc_of_horner {l : PolyQ} {a b c₁ c₂ : ℝ}
    (h : ∀ x ∈ Set.Icc a b, c₁ ≤ horner l x ∧ horner l x ≤ c₂) :
    ∀ x ∈ Set.Icc a b, ((toPoly l).eval (x : ℂ)).re ∈ Set.Icc c₁ c₂ := by
  intro x hx
  rw [re_eval_toPoly]
  exact h x hx

/-- CERT-B. A symmetric Horner bound on `[-1, 1]` bounds the sup norm. -/
theorem supNorm_toPoly_le_of_horner {l : PolyQ} {M : ℝ}
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, -M ≤ horner l x ∧ horner l x ≤ M) :
    supNorm (toPoly l) ≤ M :=
  supNorm_le_of_forall fun x hx => by
    rw [norm_eval_toPoly]
    exact abs_le.mpr (h x hx)

/-- CERT-B. A two-sided Horner bound on the difference of two coefficient lists bounds the sup
norm of the difference of the polynomials. -/
theorem supNorm_sub_le_of_horner (l m : PolyQ) (ε : ℝ)
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      -ε ≤ horner l x - horner m x ∧ horner l x - horner m x ≤ ε) :
    supNorm (toPoly l - toPoly m) ≤ ε := by
  rw [← toPoly_sub]
  exact supNorm_toPoly_le_of_horner fun x hx => by
    rw [horner_sub]
    exact h x hx

end PolyQ

/-! ### Worked example: `T₃ = 4x³ − 3x` -/

/-- CERT-B. The coefficient list of `T₃ = 4x³ − 3x`. -/
def cheb3 : PolyQ := [0, -3, 0, 4]

/-- CERT-B. `|T₃(x)| ≤ 1` on `[-1, 1]`, certified by LeanCert (kernel mode). -/
theorem cheb3_horner_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ cheb3.horner x ∧ cheb3.horner x ≤ 1 := by
  simp only [cheb3, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

/-- CERT-B. `‖T₃‖_∞ ≤ 1`, from the certificate. -/
theorem supNorm_cheb3_le_one : supNorm cheb3.toPoly ≤ 1 :=
  PolyQ.supNorm_toPoly_le_of_horner cheb3_horner_bound

end QSVT.Certificate
