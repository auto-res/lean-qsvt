/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Bound

/-!
# Worked certificate: a degree-32 even approximation of the rectangle function (CERT-B / APP-2)

The polynomial input of the threshold-projector example `QSVT.Examples.Threshold` (APP-2, GSLW
Lemma 29 and Thm 31 "singular value threshold projector"): an even polynomial `r = rectPoly`
that approximates the rectangle (window) function

    rect(x) = 1  for |x| ≤ t − δ,     rect(x) = 0  for |x| ≥ t + δ,

with threshold `t = rectThreshold = 1/2` and transition half-width `δ = rectDelta = 1/10` (so the
plateaus are `|x| ≤ 0.4` and `|x| ≥ 0.6`), to accuracy `ε = rectEps = 10⁻²` on both plateaus,
and bounded by `1` on `[-1, 1]`.

## The polynomial

GSLW Lemma 29 builds the rectangle from two shifted sign approximations (degree
`O(log (1/ε) / δ)`); here `rectPoly` is instead the constrained Chebyshev fit of the rectangle
in the *even* Chebyshev basis `∑ⱼ aⱼ T₂ⱼ`, computed by linear programming
(`tools/phases/rect_cheb.py`, untrusted; every statement here is about the resulting list).  The
pure minimax error at degree `32` is `6.0 · 10⁻³`; the LP that produces `rectPoly` instead
*maximises the uniform certificate margin* `μ` at the stated accuracy `ε = 10⁻²`:

    1 − ε + μ ≤ r ≤ 1 − μ  on [0, 0.4],    |r| ≤ ε − μ  on [0.6, 1],    |r| ≤ 1 − μ  on [0, 1],

which gives `μ = 2.4 · 10⁻³`, so each of the three certified bounds below has a slack of
`2.4 · 10⁻³` (the upper bound `r ≤ 1` is stated without an `ε`, and an LP that merely
minimised `ε` would touch `1` at `x = 0`; the margin replaces the `(1 − 10⁻⁸)` rescaling of
`SinExample`).  The Chebyshev coefficients are rounded to `30` significant digits and
converted exactly to the monomial basis.  Numerically `r ∈ [0.99240, 0.99760]` on `[-0.4, 0.4]`,
`max |r| = 7.6 · 10⁻³` on `[0.6, 1]`, `max |r| = 0.99760` on `[-1, 1]` (attained at
`|x| = 0.254`), and `r(1/2) = 0.584`.

Certified statements (LeanCert, kernel trust):

* `rectPoly_abs_bound` : `-1 ≤ r(x) ≤ 1` on `[-1, 1]` (admissibility), hence
  `supNorm_rectPoly_le_one`.
* `rectPoly_inner_bound` : `1 − ε ≤ r(x) ≤ 1` on `[-0.4, 0.4]`, `ε = rectEps = 10⁻²`.
* `rectPoly_outer_bound` : `-ε ≤ r(x) ≤ ε` on `[0.6, 1]`, and the mirror
  `rectPoly_outer_bound_neg` on `[-1, -0.6]` by evenness (`rectPoly_horner_neg`, an exact
  `ring` identity).
* Transfers to the complex polynomial `rectPoly.toPoly`: `norm_eval_rectPoly_sub_one_le`
  (`‖r(x) − 1‖ ≤ ε` for `|x| ≤ 0.4`, also as `norm_eval_rectPoly_sub_one_le_of_abs`) and
  `norm_eval_rectPoly_le` / `norm_eval_rectPoly_le_neg` / `norm_eval_rectPoly_le_of_abs`
  (`‖r(x)‖ ≤ ε` for `0.6 ≤ |x| ≤ 1`).

All three certificates are Bernstein bisection certificates over exact rationals checked by
`decide +kernel` through the `leancert` router at its default depth (the `2.4 · 10⁻³` margins
make the deeper `(subdivisions := 14)` of `Sign21` / `InvExample` unnecessary).  Timings
(Apple-silicon laptop) are recorded next to each certificate; the whole module builds in about
two and a half minutes.  No `native_decide`: every theorem depends only on `propext`,
`Classical.choice`, `Quot.sound` (audited in `test/QSVTTest/Threshold.lean`).
-/

namespace QSVT.Certificate

open QSVT.Poly

/-- CERT-B/APP-2. The threshold `t = 1/2`: the window is `|x| ≤ t`.  The statements below write
the literals `0.4 = t − δ` and `0.6 = t + δ`. -/
def rectThreshold : ℚ := 1 / 2

/-- CERT-B/APP-2. The transition half-width `δ = 1/10`: the polynomial is unconstrained on
`t − δ < |x| < t + δ`. -/
def rectDelta : ℚ := 1 / 10

/-- CERT-B/APP-2. The certified plateau accuracy: `1 − ε ≤ r ≤ 1` on `|x| ≤ 0.4` and `|r| ≤ ε`
on `|x| ≥ 0.6`, `ε = rectEps = 10⁻²`. -/
def rectEps : ℚ := 0.01

/-- CERT-B/APP-2. Monomial coefficients (index = degree) of the even degree-32 approximation
of the rectangle function with plateaus `|x| ≤ 0.4` (value `1`) and `|x| ≥ 0.6` (value `0`):
the maximal-margin constrained Chebyshev fit of `tools/phases/rect_cheb.py --degree 32` with
the Chebyshev coefficients rounded to 30 significant digits (exact conversion to the monomial
basis). -/
def rectPoly : PolyQ :=
  [-- x^0 ≈ 9.924008e-01
   19848016667136977441571188407457 / 20000000000000000000000000000000,
   0,
   -- x^2 ≈ 1.652551e+00
   16525510598318188266314665568633 / 10000000000000000000000000000000,
   0,
   -- x^4 ≈ -1.734994e+02
   -216874203834269373824400473081819 / 1250000000000000000000000000000,
   0,
   -- x^6 ≈ 7.085399e+03
   1107093635424932424275029640977313 / 156250000000000000000000000000,
   0,
   -- x^8 ≈ -1.480239e+05
   -4625746825921071460653577478430223 / 31250000000000000000000000000,
   0,
   -- x^10 ≈ 1.807742e+06
   35307462950555590936538991053652231 / 19531250000000000000000000000,
   0,
   -- x^12 ≈ -1.396346e+07
   -13636188426512934308530711202666697 / 976562500000000000000000000,
   0,
   -- x^14 ≈ 7.198320e+07
   87870121368289148640704638859530083 / 1220703125000000000000000000,
   0,
   -- x^16 ≈ -2.575790e+08
   -78606860519013760353491254706480913 / 305175781250000000000000000,
   0,
   -- x^18 ≈ 6.568826e+08
   100232334761352705540683044604879497 / 152587890625000000000000000,
   0,
   -- x^20 ≈ -1.211405e+09
   -4621141810256114997031845481598579 / 3814697265625000000000000,
   0,
   -- x^22 ≈ 1.620732e+09
   7728251873189361109747069766835927 / 4768371582031250000000000,
   0,
   -- x^24 ≈ -1.558715e+09
   -3716267091173764421999092810720281 / 2384185791015625000000000,
   0,
   -- x^26 ≈ 1.050514e+09
   626155110051563170790039913881857 / 596046447753906250000000,
   0,
   -- x^28 ≈ -4.710568e+08
   -7019293719567495079547647662817 / 14901161193847656250000,
   0,
   -- x^30 ≈ 1.262419e+08
   4702878800614614957648074167193 / 37252902984619140625000,
   0,
   -- x^32 ≈ -1.530101e+07
   -142501767249274061133412772051 / 9313225746154785156250]

/-! ### Certificates (LeanCert, kernel trust) -/

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (numerically `max |r| = 0.99760`, so the margin is `2.4 · 10⁻³`; about
-- 55 s in isolation: 31 s untrusted search, 24 s kernel).
/-- CERT-B/APP-2. Admissibility: `-1 ≤ r(x) ≤ 1` on `[-1, 1]`. -/
theorem rectPoly_abs_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ rectPoly.horner x ∧ rectPoly.horner x ≤ 1 := by
  simp only [rectPoly, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (numerically `r ∈ [0.99240, 0.99760]` on `[-0.4, 0.4]`, margins
-- `2.4 · 10⁻³` on both sides; about 35 s in isolation: 20 s untrusted search, 15 s kernel).
-- The bound is stated with the literal `0.99 = 1 − ε`: LeanCert's front end reads the goal
-- syntactically, and rewriting `1 − ↑rectEps` into `0.99` with `rw` leaves an `mdata` wrapper it
-- does not recognise, so the `ε`-form `rectPoly_inner_bound` is derived below.
/-- CERT-B/APP-2 (GSLW Lemma 29, inner plateau; literal form). `0.99 ≤ r(x) ≤ 1` on
`[-0.4, 0.4]`. -/
theorem rectPoly_inner_cert :
    ∀ x ∈ Set.Icc (-0.4 : ℝ) 0.4, 0.99 ≤ rectPoly.horner x ∧ rectPoly.horner x ≤ 1 := by
  simp only [rectPoly, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

/-- CERT-B/APP-2 (GSLW Lemma 29, inner plateau). `1 − ε ≤ r(x) ≤ 1` on `[-0.4, 0.4]`,
`ε = rectEps = 10⁻²` (the certificate `rectPoly_inner_cert` with `0.99 = 1 − ε`). -/
theorem rectPoly_inner_bound :
    ∀ x ∈ Set.Icc (-0.4 : ℝ) 0.4,
      1 - (rectEps : ℝ) ≤ rectPoly.horner x ∧ rectPoly.horner x ≤ 1 := by
  have h : (1 : ℝ) - rectEps = 0.99 := by rw [rectEps]; norm_num
  rw [h]
  exact rectPoly_inner_cert

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (numerically `max |r| = 7.6 · 10⁻³` on `[0.6, 1]`, margin `2.4 · 10⁻³`;
-- about 45 s in isolation: 26 s untrusted search, 19 s kernel).
/-- CERT-B/APP-2 (GSLW Lemma 29, outer plateau). `-ε ≤ r(x) ≤ ε` on `[0.6, 1]`,
`ε = rectEps = 10⁻²`. -/
theorem rectPoly_outer_bound :
    ∀ x ∈ Set.Icc (0.6 : ℝ) 1,
      -(rectEps : ℝ) ≤ rectPoly.horner x ∧ rectPoly.horner x ≤ rectEps := by
  simp only [rectPoly, rectEps, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

/-! ### Consequences -/

/-- CERT-B/APP-2. `r` is even (all odd coefficients vanish). -/
theorem rectPoly_horner_neg (x : ℝ) : rectPoly.horner (-x) = rectPoly.horner x := by
  simp only [rectPoly, PolyQ.horner]
  ring

/-- CERT-B/APP-2. The mirror outer bound `-ε ≤ r(x) ≤ ε` on `[-1, -0.6]`, by evenness. -/
theorem rectPoly_outer_bound_neg :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.6),
      -(rectEps : ℝ) ≤ rectPoly.horner x ∧ rectPoly.horner x ≤ rectEps := by
  intro x hx
  have h := rectPoly_outer_bound (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rwa [rectPoly_horner_neg] at h

theorem rectEps_pos : (0 : ℝ) < rectEps := by
  rw [rectEps]; norm_num

theorem rectEps_nonneg : (0 : ℝ) ≤ rectEps := rectEps_pos.le

/-- CERT-B/APP-2. `‖r‖_∞ ≤ 1` for the complex polynomial `rectPoly.toPoly`. -/
theorem supNorm_rectPoly_le_one : supNorm rectPoly.toPoly ≤ 1 :=
  PolyQ.supNorm_toPoly_le_of_horner rectPoly_abs_bound

/-- CERT-B/APP-2. `‖r(x) − 1‖ ≤ ε` on `[-0.4, 0.4]` for the complex polynomial
`rectPoly.toPoly`, `ε = rectEps = 10⁻²`. -/
theorem norm_eval_rectPoly_sub_one_le :
    ∀ x ∈ Set.Icc (-0.4 : ℝ) 0.4, ‖rectPoly.toPoly.eval (x : ℂ) - 1‖ ≤ rectEps := by
  intro x hx
  have h := rectPoly_inner_bound x hx
  have h' := PolyQ.norm_eval_toPoly_sub_le (l := rectPoly) (x := x) (c := 1) (ε := rectEps)
    ⟨by linarith [h.1], by linarith [h.2, rectEps_nonneg]⟩
  rwa [Complex.ofReal_one] at h'

/-- CERT-B/APP-2. `‖r(x) − 1‖ ≤ ε` for `|x| ≤ 0.4` (the inner plateau as an absolute-value
hypothesis). -/
theorem norm_eval_rectPoly_sub_one_le_of_abs {x : ℝ} (hx : |x| ≤ 0.4) :
    ‖rectPoly.toPoly.eval (x : ℂ) - 1‖ ≤ rectEps :=
  norm_eval_rectPoly_sub_one_le x (Set.mem_Icc.mpr (abs_le.mp hx))

/-- CERT-B/APP-2. `‖r(x)‖ ≤ ε` on `[0.6, 1]` for the complex polynomial `rectPoly.toPoly`. -/
theorem norm_eval_rectPoly_le :
    ∀ x ∈ Set.Icc (0.6 : ℝ) 1, ‖rectPoly.toPoly.eval (x : ℂ)‖ ≤ rectEps := by
  intro x hx
  rw [PolyQ.norm_eval_toPoly]
  exact abs_le.mpr (rectPoly_outer_bound x hx)

/-- CERT-B/APP-2. `‖r(x)‖ ≤ ε` on `[-1, -0.6]` for the complex polynomial `rectPoly.toPoly`. -/
theorem norm_eval_rectPoly_le_neg :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.6), ‖rectPoly.toPoly.eval (x : ℂ)‖ ≤ rectEps := by
  intro x hx
  rw [PolyQ.norm_eval_toPoly]
  exact abs_le.mpr (rectPoly_outer_bound_neg x hx)

/-- CERT-B/APP-2. `‖r(x)‖ ≤ ε` for `0.6 ≤ |x| ≤ 1` (the outer plateau as an absolute-value
hypothesis). -/
theorem norm_eval_rectPoly_le_of_abs {x : ℝ} (hx : 0.6 ≤ |x|) (hx1 : |x| ≤ 1) :
    ‖rectPoly.toPoly.eval (x : ℂ)‖ ≤ rectEps := by
  have h1 := abs_le.mp hx1
  rcases le_abs.mp hx with h | h
  · exact norm_eval_rectPoly_le x ⟨h, h1.2⟩
  · exact norm_eval_rectPoly_le_neg x ⟨h1.1, by linarith⟩

end QSVT.Certificate
