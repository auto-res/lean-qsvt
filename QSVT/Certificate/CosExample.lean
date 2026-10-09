/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.Complex.Trigonometric
import QSVT.Certificate.Bound

/-!
# Worked certificate: a degree-10 approximation of `cos (2x)` (formal-spec CERT-B / APP-4 lite)

The second certified polynomial of the library, the input of `QSVT.Examples.CosEvolution`
(APP-4 lite, Hamiltonian simulation): `cos (t x)` for `t = 2` on `[-1, 1]`, the real part of the
Hamiltonian-simulation target `e^{-itx}` (GSLW Thm 58).  The polynomial is the Jacobi–Anger
expansion `cos (t x) = J₀(t) + 2 ∑_{k ≥ 1} (-1)^k J_{2k}(t) T_{2k}(x)` truncated at degree `10`
(truncation tail `2 ∑_{k > 10} |J_k(2)| = 3.9 · 10⁻⁹`), with the Bessel values rounded to `30`
significant digits and converted exactly to the monomial basis by `tools/phases/cos_cheb.py`
(untrusted; every statement here is about the resulting list `cos2Poly : PolyQ`).

Certified statements (numerically `max |p(x) − cos 2x| = 3.9 · 10⁻⁹`, `max |p| = p(0) =
1 − 3.9 · 10⁻⁹` on `[-1, 1]`):

* `cos2Poly_horner_bound` : `|p(x) − cos (2x)| ≤ ε` on `[-1, 1]` with `ε = 10⁻⁶`, stated as the
  two-sided bound `-ε ≤ p(x) − cos (2x) ≤ ε`; transferred to the complex polynomial as
  `norm_eval_cos2Poly_sub_cos_le`.
* `cos2Poly_abs_bound` : `-1 ≤ p(x) ≤ 1` on `[-1, 1]` (admissibility, LeanCert kernel certificate
  despite the `3.9 · 10⁻⁹` margin at `x = 0`), hence `supNorm_cos2Poly_le_one`.
* `cos2Poly_horner_neg` : `p` is even (an exact `ring` identity).

## How `cos` is handled

LeanCert's interval strategies (`leancert`, `(subdivisions := n)`) cannot certify
`p(x) − cos (2x)` against `Real.cos` directly: the Horner form and `cos (2x)` are evaluated by
independent interval arithmetic, so their difference is enclosed with a width of about `9 w` on a
box of width `w` while the true value is `≈ 10⁻⁹`; even the margin `10⁻³` fails at depth `14`
(Bernstein certificates, which are tight, apply to polynomials only).  The certificate is
therefore split, without weakening the statement:

1. `cosTaylor16 : PolyQ` is the degree-16 Taylor polynomial `∑_{j ≤ 8} (-1)^j (2x)^{2j} / (2j)!`
   of `cos (2x)`, and `abs_cos_sub_cosTaylor16_le : |cos (2x) − T₁₆(x)| ≤ 10⁻⁷` on `|x| ≤ 1` is a
   Mathlib proof: `Real.cos (2x) = Re exp(2x i)` (`Complex.exp_ofReal_mul_I_re`), the
   remainder bound `Complex.exp_bound'` with `n = 18` (`2 · 2¹⁸ / 18! = 8.2 · 10⁻¹¹`), and the
   real part of the 18-term complex sum computed by `simp`/`ring`
   (`re_sum_range_eq_cosTaylor16`).
2. `cos2Poly_sub_cosTaylor16_bound : |p(x) − T₁₆(x)| ≤ 9 · 10⁻⁷` is a LeanCert Bernstein
   certificate (kernel trust) for the degree-16 polynomial `p − T₁₆`.

Timings on an Apple-silicon laptop (`set_option profiler true`): the Bernstein certificates take
about `6.5 s` for `cos2Poly_sub_cosTaylor16_bound` (`2.4 s` untrusted search, `4.1 s` kernel
check of the degree-16 certificate) and `2 s` for `cos2Poly_abs_bound`, both at the default
bisection depth; the Taylor lemmas are instantaneous, and the whole module elaborates in about
`6 s` after loading its imports.  No `native_decide`: every
theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`test/QSVTTest/CosExample.lean`).

## Mathlib API used

`Complex.exp_bound'`, `Complex.exp_ofReal_mul_I_re`, `Complex.abs_re_le_norm`, `Complex.sub_re`,
`Complex.norm_I`, `Complex.norm_real`, `Finset.sum_range_succ`, `Nat.factorial`, `pow_le_one₀`,
`abs_le`.
-/

namespace QSVT.Certificate

open QSVT.Poly Finset Complex

/-- CERT-B/APP-4. Monomial coefficients (index = degree) of the degree-10 even approximation
of `cos (2x)`: the Jacobi–Anger series `J₀(2) + 2 ∑_{k=1}^{5} (-1)^k J_{2k}(2) T_{2k}(x)` with the
Bessel values rounded to 30 significant digits (exact conversion by
`tools/phases/cos_cheb.py --t 2`). -/
def cos2Poly : PolyQ :=
  [62499999757066272271938848645232619 / 62500000000000000000000000000000000,  -- x^0  ≈  1
   0,
   -499999929894335001519960863835789 / 250000000000000000000000000000000,     -- x^2  ≈ -2
   0,
   26041538509675309727382800284451 / 39062500000000000000000000000000,        -- x^4  ≈  0.66666
   0,
   -34716731052072727166101772944723 / 390625000000000000000000000000000,      -- x^6  ≈ -0.088875
   0,
   308686732133033009967311728309 / 48828125000000000000000000000000,          -- x^8  ≈  0.0063219
   0,
   -31442328533959208870439511719 / 122070312500000000000000000000000]         -- x^10 ≈ -0.00025758

/-- CERT-B/APP-4. The degree-16 Taylor polynomial of `cos (2x)`:
`∑_{j ≤ 8} (-1)^j 2^{2j} / (2j)! · x^{2j}`. -/
def cosTaylor16 : PolyQ :=
  [1, 0, -2, 0, 2 / 3, 0, -4 / 45, 0, 2 / 315, 0, -4 / 14175, 0, 4 / 467775, 0,
   -8 / 42567525, 0, 2 / 638512875]

/-! ### Certificates (LeanCert, kernel trust) -/

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (about 6.5 s: 2.4 s search, 4.1 s kernel; numerically
-- `max |p − T₁₆| = 4.0 · 10⁻⁹`).
/-- CERT-B/APP-4. `|p(x) − T₁₆(x)| ≤ 9 · 10⁻⁷` on `[-1, 1]` for the Taylor polynomial `T₁₆` of
`cos (2x)`. -/
theorem cos2Poly_sub_cosTaylor16_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      -0.0000009 ≤ cos2Poly.horner x - cosTaylor16.horner x ∧
        cos2Poly.horner x - cosTaylor16.horner x ≤ 0.0000009 := by
  simp only [cos2Poly, cosTaylor16, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (about 2 s; the maximum `p(0) = 1 − 3.9 · 10⁻⁹` is below `1`).
/-- CERT-B/APP-4. Admissibility: `-1 ≤ p(x) ≤ 1` on `[-1, 1]`. -/
theorem cos2Poly_abs_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ cos2Poly.horner x ∧ cos2Poly.horner x ≤ 1 := by
  simp only [cos2Poly, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

/-! ### The Taylor remainder of `cos (2x)` (Mathlib) -/

/-- CERT-B/APP-4 (helper). The real part of the 18-term Taylor sum of `exp (2x i)` is
`T₁₆(x)`. -/
theorem re_sum_range_eq_cosTaylor16 (x : ℝ) :
    (∑ m ∈ range 18, (((2 * x : ℝ) : ℂ) * I) ^ m / (m.factorial : ℂ)).re =
      cosTaylor16.horner x := by
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, cosTaylor16, PolyQ.horner]
  simp [pow_succ]
  ring

/-- CERT-B/APP-4 (helper). The Taylor remainder: `|cos (2x) − T₁₆(x)| ≤ 10⁻⁷` for `|x| ≤ 1`
(the true bound `2 · 2¹⁸ / 18! = 8.2 · 10⁻¹¹` is `Complex.exp_bound'`). -/
theorem abs_cos_sub_cosTaylor16_le (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos (2 * x) - cosTaylor16.horner x| ≤ 0.0000001 := by
  have hnorm : ‖((2 * x : ℝ) : ℂ) * I‖ = 2 * |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
  have hb := Complex.exp_bound' (x := ((2 * x : ℝ) : ℂ) * I) (n := 18) (by
    rw [hnorm]
    push_cast
    linarith)
  rw [← Complex.exp_ofReal_mul_I_re (2 * x), ← re_sum_range_eq_cosTaylor16, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans (hb.trans ?_)
  rw [hnorm, mul_pow]
  have h18 : |x| ^ 18 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hf : ((18 : ℕ).factorial : ℝ) = 6402373705728000 := by norm_num [Nat.factorial]
  rw [hf]
  calc (2 : ℝ) ^ 18 * |x| ^ 18 / 6402373705728000 * 2
      ≤ 2 ^ 18 * 1 / 6402373705728000 * 2 := by gcongr
    _ ≤ 0.0000001 := by norm_num

/-! ### The headline certificate -/

/-- CERT-B/APP-4. `|p(x) − cos (2x)| ≤ 10⁻⁶` on `[-1, 1]`, as the two-sided bound
`-ε ≤ p(x) − cos (2x) ≤ ε`: the Bernstein certificate `cos2Poly_sub_cosTaylor16_bound`
(`9 · 10⁻⁷`) plus the Taylor remainder `abs_cos_sub_cosTaylor16_le` (`10⁻⁷`). -/
theorem cos2Poly_horner_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      -0.000001 ≤ cos2Poly.horner x - Real.cos (2 * x) ∧
        cos2Poly.horner x - Real.cos (2 * x) ≤ 0.000001 := by
  intro x hx
  have h₁ := cos2Poly_sub_cosTaylor16_bound x hx
  have h₂ := abs_le.mp (abs_cos_sub_cosTaylor16_le x (abs_le.mpr ⟨hx.1, hx.2⟩))
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-! ### Consequences -/

/-- CERT-B/APP-4. `p` is even (all odd coefficients vanish). -/
theorem cos2Poly_horner_neg (x : ℝ) : cos2Poly.horner (-x) = cos2Poly.horner x := by
  simp only [cos2Poly, PolyQ.horner]
  ring

/-- CERT-B/APP-4. `‖p‖_∞ ≤ 1` for the complex polynomial `cos2Poly.toPoly`. -/
theorem supNorm_cos2Poly_le_one : supNorm cos2Poly.toPoly ≤ 1 :=
  PolyQ.supNorm_toPoly_le_of_horner cos2Poly_abs_bound

/-- CERT-B/APP-4. `‖p(x) − cos (2x)‖ ≤ 10⁻⁶` on `[-1, 1]` for the complex polynomial
`cos2Poly.toPoly` at real points. -/
theorem norm_eval_cos2Poly_sub_cos_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖cos2Poly.toPoly.eval (x : ℂ) - ((Real.cos (2 * x) : ℝ) : ℂ)‖ ≤ 0.000001 := by
  intro x hx
  have h := cos2Poly_horner_bound x hx
  exact PolyQ.norm_eval_toPoly_sub_le ⟨by linarith [h.1], by linarith [h.2]⟩

end QSVT.Certificate
