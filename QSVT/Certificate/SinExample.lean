/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.Complex.Trigonometric
import QSVT.Certificate.Bound

/-!
# Worked certificate: a degree-11 approximation of `sin (2x)` (formal-spec CERT-B / APP-4)

The odd companion of `QSVT.Certificate.CosExample`: the imaginary part of the
Hamiltonian-simulation target `e^{-itx} = cos (tx) − i sin (tx)` for `t = 2` on `[-1, 1]`
(GSLW Thm 58), the second input of `QSVT.Examples.Evolution` (APP-4).  The polynomial is the
odd Jacobi–Anger expansion `sin (t x) = 2 ∑_{k ≥ 0} (-1)^k J_{2k+1}(t) T_{2k+1}(x)` truncated at
degree `11` (truncation tail `2 ∑_{k > 11} |J_k(2)| = 3.0 · 10⁻¹⁰`), *scaled by `1 − 10⁻⁸`*, with
the Bessel values rounded to `30` significant digits and converted exactly to the monomial basis
by `tools/phases/cos_cheb.py --sin --scale 1e-8` (untrusted; every statement here is about the
resulting list `sin2Poly : PolyQ`).

## Why the scale factor

Unlike `cos (2x)`, whose maximum `1` on `[-1, 1]` is attained at `x = 0` where the alternating
Jacobi–Anger tail *lowers* the truncation (`p(0) = 1 − 3.9 · 10⁻⁹`), `sin (2x)` attains `±1` at
`x = ±π/4`, where the unscaled truncation overshoots: `max |p| = 1 + 2.1 · 10⁻¹⁰`, so the
admissibility bound `|p| ≤ 1` required by the QSVT would be *false*.  Multiplying the
coefficients by `1 − 10⁻⁸` gives `max |p| = 1 − 9.8 · 10⁻⁹` (certified below) at the price of
`10⁻⁸` in the approximation error, which is irrelevant against the certified `ε = 10⁻⁶`.

Certified statements (numerically `max |p(x) − sin 2x| = 1.0 · 10⁻⁸`, `max |p| = 1 − 9.8 · 10⁻⁹`
on `[-1, 1]`):

* `sin2Poly_horner_bound` : `|p(x) − sin (2x)| ≤ ε` on `[-1, 1]` with `ε = 10⁻⁶`, stated as the
  two-sided bound `-ε ≤ p(x) − sin (2x) ≤ ε`; transferred to the complex polynomial as
  `norm_eval_sin2Poly_sub_sin_le`.
* `sin2Poly_abs_bound` : `-1 ≤ p(x) ≤ 1` on `[-1, 1]` (admissibility), hence
  `supNorm_sin2Poly_le_one`.  Only the upper bound `sin2Poly_le_one` is a LeanCert kernel
  certificate (Bernstein bisection with up to `20` levels, `bernstein_bound 20`, because the
  `9.8 · 10⁻⁹` margin sits at the interior non-dyadic point `π/4` and the default `leancert`
  budget is exhausted); the lower bound is the upper bound at `-x` by oddness.
* `sin2Poly_horner_neg` : `p` is odd (an exact `ring` identity).

## How `sin` is handled

As in `CosExample` (see its module docstring: LeanCert's interval strategies cannot certify
`p(x) − sin (2x)` against `Real.sin` directly at this accuracy), the certificate is split:

1. `sinTaylor17 : PolyQ` is the degree-17 Taylor polynomial
   `∑_{j ≤ 8} (-1)^j (2x)^{2j+1} / (2j+1)!` of `sin (2x)`, and
   `abs_sin_sub_sinTaylor17_le : |sin (2x) − T₁₇(x)| ≤ 10⁻⁷` on `|x| ≤ 1` is a Mathlib proof:
   `Real.sin (2x) = Im exp(2x i)` (`Complex.exp_ofReal_mul_I_im`), the remainder bound
   `Complex.exp_bound'` with `n = 18` (`2 · 2¹⁸ / 18! = 8.2 · 10⁻¹¹`), and the imaginary part of
   the 18-term complex sum computed by `simp`/`ring` (`im_sum_range_eq_sinTaylor17`).
2. `sin2Poly_sub_sinTaylor17_bound : |p(x) − T₁₇(x)| ≤ 9 · 10⁻⁷` is a LeanCert Bernstein
   certificate (kernel trust) for the degree-17 polynomial `p − T₁₇`.

Timings on an Apple-silicon laptop (`set_option profiler true`): the Bernstein certificates take
about `2.6 s` for `sin2Poly_sub_sinTaylor17_bound` (default depth; the degree-17 difference has
a comfortable margin) and `9 s` for `sin2Poly_le_one` (`5 s` untrusted search, `4 s` kernel check
of the deeper certificate); the Taylor lemmas are instantaneous, and the whole module elaborates
in about `16 s` after loading its imports.  No `native_decide`: every theorem depends only
on `propext`, `Classical.choice`, `Quot.sound` (audited in `test/QSVTTest/Evolution.lean`).

## Mathlib API used

`Complex.exp_bound'`, `Complex.exp_ofReal_mul_I_im`, `Complex.abs_im_le_norm`, `Complex.sub_im`,
`Complex.norm_I`, `Complex.norm_real`, `Finset.sum_range_succ`, `Nat.factorial`, `pow_le_one₀`,
`abs_le`.
-/

namespace QSVT.Certificate

open QSVT.Poly Finset Complex

/-- CERT-B/APP-4. Monomial coefficients (index = degree) of the degree-11 odd approximation
of `sin (2x)`: the Jacobi–Anger series `2 ∑_{k=0}^{5} (-1)^k J_{2k+1}(2) T_{2k+1}(x)` scaled by
`1 − 10⁻⁸` (so that `max |p| < 1`), with the coefficients rounded to 30 significant digits
(exact conversion by `tools/phases/cos_cheb.py --t 2 --sin --scale 1e-8`). -/
def sin2Poly : PolyQ :=
  [0,
   -- x^1 ≈ 2
   3999999952183022098469808049437413187 / 2000000000000000000000000000000000000,
   0,
   -- x^3 ≈ -1.33333
   -133333321035936704941898883148348927 / 100000000000000000000000000000000000,
   0,
   -- x^5 ≈ 0.26667
   33333223074516326644157951103159589 / 125000000000000000000000000000000000,
   0,
   -- x^7 ≈ -0.025394
   -99194524547131413054779378636901 / 3906250000000000000000000000000000,
   0,
   -- x^9 ≈ 0.0014059
   10983258924381257065305080861027 / 7812500000000000000000000000000000,
   0,
   -- x^11 ≈ -4.7192e-5
   -92171389412976153543390549637 / 1953125000000000000000000000000000]

/-- CERT-B/APP-4. The degree-17 Taylor polynomial of `sin (2x)`:
`∑_{j ≤ 8} (-1)^j 2^{2j+1} / (2j+1)! · x^{2j+1}`. -/
def sinTaylor17 : PolyQ :=
  [0, 2, 0, -4 / 3, 0, 4 / 15, 0, -8 / 315, 0, 4 / 2835, 0, -8 / 155925, 0, 8 / 6081075, 0,
   -16 / 638512875, 0, 4 / 10854718875]

/-! ### Certificates (LeanCert, kernel trust) -/

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (numerically `max |p − T₁₇| = 1.0 · 10⁻⁸`).
/-- CERT-B/APP-4. `|p(x) − T₁₇(x)| ≤ 9 · 10⁻⁷` on `[-1, 1]` for the Taylor polynomial `T₁₇` of
`sin (2x)`. -/
theorem sin2Poly_sub_sinTaylor17_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      -0.0000009 ≤ sin2Poly.horner x - sinTaylor17.horner x ∧
        sin2Poly.horner x - sinTaylor17.horner x ≤ 0.0000009 := by
  simp only [sin2Poly, sinTaylor17, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection (at most 20 levels) over exact rationals,
-- checked by `decide +kernel` (about 9 s: 5 s search, 4 s kernel).  The maximum
-- `p(π/4) = 1 − 9.8 · 10⁻⁹` is below `1`, but `π/4` is an interior non-dyadic point, so the
-- generic `leancert` front end (default depth) exhausts its cost budget here.
/-- CERT-B/APP-4. `p(x) ≤ 1` on `[-1, 1]`. -/
theorem sin2Poly_le_one : ∀ x ∈ Set.Icc (-1 : ℝ) 1, sin2Poly.horner x ≤ 1 := by
  simp only [sin2Poly, PolyQ.horner]
  push_cast
  bernstein_bound 20 (trust := kernel)

/-- CERT-B/APP-4. `p` is odd (all even coefficients vanish). -/
theorem sin2Poly_horner_neg (x : ℝ) : sin2Poly.horner (-x) = -sin2Poly.horner x := by
  simp only [sin2Poly, PolyQ.horner]
  ring

/-- CERT-B/APP-4. Admissibility: `-1 ≤ p(x) ≤ 1` on `[-1, 1]`: the upper bound is the
certificate `sin2Poly_le_one`, the lower bound is the upper bound at `-x` by oddness. -/
theorem sin2Poly_abs_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ sin2Poly.horner x ∧ sin2Poly.horner x ≤ 1 := by
  intro x hx
  refine ⟨?_, sin2Poly_le_one x hx⟩
  have h := sin2Poly_le_one (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [sin2Poly_horner_neg] at h
  linarith

/-! ### The Taylor remainder of `sin (2x)` (Mathlib) -/

/-- CERT-B/APP-4 (helper). The imaginary part of the 18-term Taylor sum of `exp (2x i)` is
`T₁₇(x)`. -/
theorem im_sum_range_eq_sinTaylor17 (x : ℝ) :
    (∑ m ∈ range 18, (((2 * x : ℝ) : ℂ) * I) ^ m / (m.factorial : ℂ)).im =
      sinTaylor17.horner x := by
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, sinTaylor17, PolyQ.horner]
  simp [pow_succ]
  ring

/-- CERT-B/APP-4 (helper). The Taylor remainder: `|sin (2x) − T₁₇(x)| ≤ 10⁻⁷` for `|x| ≤ 1`
(the true bound `2 · 2¹⁸ / 18! = 8.2 · 10⁻¹¹` is `Complex.exp_bound'`). -/
theorem abs_sin_sub_sinTaylor17_le (x : ℝ) (hx : |x| ≤ 1) :
    |Real.sin (2 * x) - sinTaylor17.horner x| ≤ 0.0000001 := by
  have hnorm : ‖((2 * x : ℝ) : ℂ) * I‖ = 2 * |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
  have hb := Complex.exp_bound' (x := ((2 * x : ℝ) : ℂ) * I) (n := 18) (by
    rw [hnorm]
    push_cast
    linarith)
  rw [← Complex.exp_ofReal_mul_I_im (2 * x), ← im_sum_range_eq_sinTaylor17, ← Complex.sub_im]
  refine (Complex.abs_im_le_norm _).trans (hb.trans ?_)
  rw [hnorm, mul_pow]
  have h18 : |x| ^ 18 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hf : ((18 : ℕ).factorial : ℝ) = 6402373705728000 := by norm_num [Nat.factorial]
  rw [hf]
  calc (2 : ℝ) ^ 18 * |x| ^ 18 / 6402373705728000 * 2
      ≤ 2 ^ 18 * 1 / 6402373705728000 * 2 := by gcongr
    _ ≤ 0.0000001 := by norm_num

/-! ### The headline certificate -/

/-- CERT-B/APP-4. `|p(x) − sin (2x)| ≤ 10⁻⁶` on `[-1, 1]`, as the two-sided bound
`-ε ≤ p(x) − sin (2x) ≤ ε`: the Bernstein certificate `sin2Poly_sub_sinTaylor17_bound`
(`9 · 10⁻⁷`) plus the Taylor remainder `abs_sin_sub_sinTaylor17_le` (`10⁻⁷`). -/
theorem sin2Poly_horner_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      -0.000001 ≤ sin2Poly.horner x - Real.sin (2 * x) ∧
        sin2Poly.horner x - Real.sin (2 * x) ≤ 0.000001 := by
  intro x hx
  have h₁ := sin2Poly_sub_sinTaylor17_bound x hx
  have h₂ := abs_le.mp (abs_sin_sub_sinTaylor17_le x (abs_le.mpr ⟨hx.1, hx.2⟩))
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-! ### Consequences -/

/-- CERT-B/APP-4. `‖p‖_∞ ≤ 1` for the complex polynomial `sin2Poly.toPoly`. -/
theorem supNorm_sin2Poly_le_one : supNorm sin2Poly.toPoly ≤ 1 :=
  PolyQ.supNorm_toPoly_le_of_horner sin2Poly_abs_bound

/-- CERT-B/APP-4. `‖p(x) − sin (2x)‖ ≤ 10⁻⁶` on `[-1, 1]` for the complex polynomial
`sin2Poly.toPoly` at real points. -/
theorem norm_eval_sin2Poly_sub_sin_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖sin2Poly.toPoly.eval (x : ℂ) - ((Real.sin (2 * x) : ℝ) : ℂ)‖ ≤ 0.000001 := by
  intro x hx
  have h := sin2Poly_horner_bound x hx
  exact PolyQ.norm_eval_toPoly_sub_le ⟨by linarith [h.1], by linarith [h.2]⟩

end QSVT.Certificate
