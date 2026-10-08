/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Bound

/-!
# Worked certificate: a degree-35 sign approximation with gap `δ = 0.1` (CERT-B, part 1)

A second certified sign-function approximation, with a smaller gap than the degree-21
`QSVT.Certificate.Sign21` (`δ = 0.15`, plateau value `0.8924`) and a plateau value close to `1`:
the input of the fixed-point amplitude amplification composed with the matrix-inversion example
(initial amplitudes `a ≥ 0.1`).

The polynomial `signD01 : PolyQ` is the *constrained minimax fit* of `sign x` on
`[-1, -0.1] ∪ [0.1, 1]` in the odd Chebyshev basis `∑ⱼ aⱼ T₂ⱼ₊₁`, computed by linear programming
(`tools/phases/sign_cheb.py`, untrusted): maximise the plateau lower bound `L` subject to
`p ≥ L` on `[0.1, 1]` and `|p| ≤ 1 − μ` on `[-1, 1]`, margin `μ = 10⁻³`.  At odd degree `35`
the optimum is `L = 0.97611`; it equioscillates between `L` and `1 − μ = 0.999` on the plateau
(`p(0.1) = 0.97611`, `p(1) = 0.97611`, `max |p| = 0.9990006` at `|x| = 0.8127`).  The LP
coefficients are rounded to doubles (exact dyadic rationals; their exact decimal expansions are
the `target_chebyshev_coeffs` of `tools/phases/examples/sign_d01_pyqsp_symqsp.json` and
`sign_d01_qsppack.json`) and converted exactly to the monomial basis by
`tools/phases/cheb_to_monomial.py`; every statement here is about the resulting list.

Certified statements (LeanCert, kernel trust; numerically `p ∈ [0.976107, 0.999001]` on
`[0.1, 1]`, `max |p| = 0.999001` on `[-1, 1]`; the stated plateau is widened by `4 · 10⁻⁴` on
each side, see below):

* `signD01_horner_bound_nonneg` : `-1 ≤ p(x) ≤ 1` on `[0, 1]` (admissibility, margin `10⁻³`),
  extended to `[-1, 1]` by oddness (`signD01_horner_bound`), hence
  `supNorm_signD01_le_one : ‖p‖_∞ ≤ 1`.
* `signD01_plateau` : `0.9755 ≤ p(x) ≤ 0.9995` on `[δ, 1]`, `δ = 0.1` (margins `6.1 · 10⁻⁴` and
  `5.0 · 10⁻⁴`), and by oddness (`signD01_horner_neg`, an exact `ring` identity) the mirror
  `signD01_plateau_neg` on `[-1, -δ]`.
* `norm_eval_signD01_sub_scale_le` : `‖p(x) − c‖ ≤ ε_p` on `[δ, 1]` for the complex polynomial
  `signD01.toPoly`, with the plateau centre `c = signD01Scale = 0.9875` and the ripple
  `ε_p = 0.012` (`c ± ε_p = 0.9755, 0.9995`), and the mirror `norm_eval_signD01_add_scale_le`.
  Against `sign21` (`c = 0.8924`, `ε_p = 0.0236`, `δ = 0.15`, degree `21`): the plateau lower
  bound `c − ε_p` rises from `0.869` to `0.9755` at a gap `δ` two thirds as wide, for `35`
  queries instead of `21`.

Both LeanCert calls are Bernstein bisection certificates over exact rationals checked by
`decide +kernel` through the `leancert` router with `(subdivisions := 8)` and
`maxHeartbeats 4000000`.  The Bernstein enclosure of this degree-35 polynomial on the whole of
`[0.1, 1]` is `[-49.8, 59.6]` (the monomial coefficients are of order `10¹⁰`) and tightens only
quadratically in the box width, so the router's default depth `4` fails for both bounds (even
for the `10⁻³` margin of admissibility, unlike the degree-21 `Sign21`); depth `8` suffices and
depth `10` changes nothing (the bisection is adaptive).  The tighter plateau `[0.976, 0.9992]`
(margins `10⁻⁴`) is also certifiable, at depth `14` (about 170 s of search plus 140 s of kernel
time) or by two one-sided `bernstein_bound 12` calls; the stated plateau trades `4 · 10⁻⁴` of
ripple for the cheaper depth-`8` certificate.  Timings on an Apple-silicon laptop are recorded
next to each certificate; the whole module builds in about 4.5 minutes (Lean elaborates the two
certificates in parallel).
-/

namespace QSVT.Certificate

open QSVT.Poly

/-- CERT-B. Monomial coefficients (index = degree) of the odd degree-35 minimax sign
approximation with gap `δ = 0.1`: `∑ₖ cₖ Tₖ` with the `target_chebyshev_coeffs` of
`sign_d01_pyqsp_symqsp.json` (exact conversion by `tools/phases/cheb_to_monomial.py`). -/
def signD01 : PolyQ :=
  [0,
   8761775013593043667 / 576460752303423488,         -- x^1  ≈  1.519926e+01
   0,
   -13440455447850639081 / 18014398509481984,        -- x^3  ≈ -7.460952e+02
   0,
   442911830132563109255 / 18014398509481984,        -- x^5  ≈  2.458655e+04
   0,
   -139314566157960701325 / 281474976710656,         -- x^7  ≈ -4.949448e+05
   0,
   1814697029336268397671 / 281474976710656,         -- x^9  ≈  6.447099e+06
   0,
   -4029690991183495185101 / 70368744177664,         -- x^11 ≈ -5.726535e+07
   0,
   25395304516956700889781 / 70368744177664,         -- x^13 ≈  3.608890e+08
   0,
   -29215911189047534908775 / 17592186044416,        -- x^15 ≈ -1.660732e+09
   0,
   50077580147469308218565 / 8796093022208,          -- x^17 ≈  5.693162e+09
   0,
   -16190233195005334638187 / 1099511627776,         -- x^19 ≈ -1.472493e+10
   0,
   3973623754124236287663 / 137438953472,            -- x^21 ≈  2.891192e+10
   0,
   -2960430732001758879705 / 68719476736,            -- x^23 ≈ -4.307994e+10
   0,
   1660958832184843501359 / 34359738368,             -- x^25 ≈  4.834026e+10
   0,
   -86227017428852311169 / 2147483648,               -- x^27 ≈ -4.015258e+10
   0,
   51378485522788269163 / 2147483648,                -- x^29 ≈  2.392497e+10
   0,
   -5189275328708437765 / 536870912,                 -- x^31 ≈ -9.665779e+09
   0,
   318141065124051903 / 134217728,                   -- x^33 ≈  2.370336e+09
   0,
   -8935138670902553 / 33554432]                     -- x^35 ≈ -2.662879e+08

/-- CERT-B. The plateau centre `c = 0.9875`: the midpoint of the certified plateau
`[0.9755, 0.9995]` of `signD01` on `[0.1, 1]` (numerically `p ∈ [0.976107, 0.999001]` there). -/
def signD01Scale : ℚ := 79 / 80

/-- CERT-B. The gap `δ = 0.1`: the plateaus are `[δ, 1]` and `[-1, -δ]`. -/
def signD01Delta : ℚ := 1 / 10

/-! ### Certificates (LeanCert, kernel trust) -/

/-- CERT-B. `p` is odd (all even coefficients vanish). -/
theorem signD01_horner_neg (x : ℝ) : signD01.horner (-x) = -signD01.horner x := by
  simp only [signD01, PolyQ.horner]
  ring

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection (depth 8) over exact rationals, checked by
-- `decide +kernel` (numerically `max |p| = 0.9990006` at `x = 0.8127`, margin `10⁻³`; about
-- 100 s wall-clock in isolation: 60 s untrusted search, 45 s kernel; the same certificate on
-- the whole of `[-1, 1]` costs twice as much: 120 s search, 50 s + 45 s kernel).
/-- CERT-B. Admissibility on `[0, 1]`: `-1 ≤ p(x) ≤ 1` (the lower bound is slack by `1`, the
upper bound by `10⁻³`). -/
theorem signD01_horner_bound_nonneg :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, -1 ≤ signD01.horner x ∧ signD01.horner x ≤ 1 := by
  simp only [signD01, PolyQ.horner]
  push_cast
  leancert (subdivisions := 8) (trust := kernel)

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection (depth 8) over exact rationals, checked by
-- `decide +kernel` (numerically `p ∈ [0.976107, 0.999001]` on `[0.1, 1]`, margins `6.1e-4` and
-- `5.0e-4`; about 215 s wall-clock in isolation: 120 s untrusted search, 45 s + 50 s kernel
-- for the two one-sided bounds).
/-- CERT-B. Plateau: `0.9755 ≤ p(x) ≤ 0.9995` on `[δ, 1]`, `δ = 0.1`. -/
theorem signD01_plateau :
    ∀ x ∈ Set.Icc (0.1 : ℝ) 1, 0.9755 ≤ signD01.horner x ∧ signD01.horner x ≤ 0.9995 := by
  simp only [signD01, PolyQ.horner]
  push_cast
  leancert (subdivisions := 8) (trust := kernel)

/-! ### Consequences -/

/-- CERT-B. Admissibility: `-1 ≤ p(x) ≤ 1` on `[-1, 1]` (the certificate on `[0, 1]` and its
mirror by oddness). -/
theorem signD01_horner_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ signD01.horner x ∧ signD01.horner x ≤ 1 := by
  intro x hx
  rcases le_total 0 x with h0 | h0
  · exact signD01_horner_bound_nonneg x ⟨h0, hx.2⟩
  · have h := signD01_horner_bound_nonneg (-x) ⟨by linarith, by linarith [hx.1]⟩
    rw [signD01_horner_neg] at h
    constructor <;> linarith [h.1, h.2]

/-- CERT-B. The mirror plateau `-0.9995 ≤ p(x) ≤ -0.9755` on `[-1, -0.1]`, by oddness. -/
theorem signD01_plateau_neg :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.1),
      -0.9995 ≤ signD01.horner x ∧ signD01.horner x ≤ -0.9755 := by
  intro x hx
  have h := signD01_plateau (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [signD01_horner_neg] at h
  constructor <;> linarith [h.1, h.2]

/-- CERT-B. `‖p‖_∞ ≤ 1` for the complex polynomial `signD01.toPoly`. -/
theorem supNorm_signD01_le_one : supNorm signD01.toPoly ≤ 1 :=
  PolyQ.supNorm_toPoly_le_of_horner signD01_horner_bound

/-- CERT-B. `‖p(x) − c‖ ≤ 0.012` on `[0.1, 1]`, `c = signD01Scale = 0.9875`. -/
theorem norm_eval_signD01_sub_scale_le :
    ∀ x ∈ Set.Icc (0.1 : ℝ) 1,
      ‖signD01.toPoly.eval (x : ℂ) - ((signD01Scale : ℝ) : ℂ)‖ ≤ 0.012 :=
  PolyQ.forall_norm_eval_sub_le_of_two_sided fun x hx => by
    have h := signD01_plateau x hx
    have hc : (signD01Scale : ℝ) = 79 / 80 := by
      rw [signD01Scale]; push_cast; ring
    rw [hc]
    constructor <;> linarith [h.1, h.2]

/-- CERT-B. `‖p(x) + c‖ ≤ 0.012` on `[-1, -0.1]`, `c = signD01Scale = 0.9875`. -/
theorem norm_eval_signD01_add_scale_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.1),
      ‖signD01.toPoly.eval (x : ℂ) + ((signD01Scale : ℝ) : ℂ)‖ ≤ 0.012 := by
  intro x hx
  have h := PolyQ.forall_norm_eval_sub_le_of_two_sided (l := signD01) (c := -(signD01Scale : ℝ))
    (ε := 0.012) (fun y hy => by
      have h := signD01_plateau_neg y hy
      have hc : (signD01Scale : ℝ) = 79 / 80 := by
        rw [signD01Scale]; push_cast; ring
      rw [hc]
      constructor <;> linarith [h.1, h.2]) x hx
  simpa [sub_neg_eq_add] using h

end QSVT.Certificate
