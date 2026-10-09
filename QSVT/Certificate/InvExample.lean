/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Bound

/-!
# Worked certificate: a degree-29 approximation of `(3/4) / (κ x)`, `κ = 4` (CERT-B / APP-3)

The polynomial input of the matrix-inversion example `QSVT.Examples.Inverse` (APP-3, the
polynomial step of GSLW's pseudoinverse / quantum linear-systems algorithm, Lemma 40 and
Thm 41): an odd polynomial `p = invPoly` that approximates a constant multiple of `1/x` on the
gapped region `[-1, -1/κ] ∪ [1/κ, 1]`, `κ = invKappa = 4`, and is bounded by `1` on `[-1, 1]`.

## Why a constant factor

GSLW Lemma 40 approximates `1/x` itself by `f(x) = (1 − (1 − x²)^b)/x`, `b = ⌈κ² log (κ/ε)⌉`,
truncated in the Chebyshev basis to degree `2J + 1 = O(κ log (κ/ε))`.  That construction is
unbounded on the interior: for `κ = 4`, `ε = 10⁻³` it has `b = 133`, degree `85`, and
`max f = 1.84 κ` on `(0, 1/κ)`, so `f/κ` violates the admissibility bound `|p| ≤ 1` that the
QSVT needs.  Worse, *no* odd polynomial can approximate `1/(κ x)` on `[1/κ, 1]` to relative
accuracy `ε` while staying below `1`, except at degree `Ω(1/ε)`: the target equals `1` at
`x = 1/κ` with slope `−κ`, so the polynomial would have to turn around within a window of width
`O(ε)` (numerically the best error is stuck near `10⁻²` for every degree `19 … 39`).  GSLW's
bounded-by-one version (Cor. 69, used in Thm 41) therefore approximates a constant multiple
`c/(κ x)`; here `c = invScale = 3/4`, the largest of the natural choices for which the
unconstrained degree-29 minimax fit still stays below `1` (`max |p| = 0.9738`).

## The polynomial

`invPoly` is the odd degree-29 Chebyshev minimax fit of `(3/4)/(4x)` on `[1/4, 1]` with respect
to the *relative* error, computed by linear programming (`tools/phases/inv_cheb.py`, untrusted;
every statement here is about the resulting list), with the Chebyshev coefficients rounded to
`30` significant digits and converted exactly to the monomial basis.  Numerically
`max |4x · p(x) − 3/4| = 7.05 · 10⁻⁴` on `[1/4, 1]` (relative error `9.4 · 10⁻⁴`) and
`max |p| = 0.9738` on `[-1, 1]`, attained at `|x| = 0.147`.

Certified statements (LeanCert, kernel trust):

* `invPoly_gap_bound` : `|4x · p(x) − 3/4| ≤ ε` on `[1/4, 1]` with `ε = invEps = 7.5 · 10⁻⁴`
  (relative accuracy exactly `10⁻³` with respect to the target `(3/4)/(4x)`), stated as the
  two-sided polynomial bound `-ε ≤ p(x)(4x) − 3/4 ≤ ε` that LeanCert certifies directly;
  dividing by `4x ≥ 1` gives `|p(x) − (3/4)/(4x)| ≤ ε/(4x) ≤ ε` (`abs_horner_sub_inv_le`), and
  the mirror statements on `[-1, -1/4]` follow from oddness (`invPoly_horner_neg`).
* `invPoly_abs_bound` : `-1 ≤ p(x) ≤ 1` on `[-1, 1]` (admissibility), hence
  `supNorm_invPoly_le_one`.
* Transfers to the complex polynomial `invPoly.toPoly`:
  `norm_eval_invPoly_sub_inv_le` (on `[1/4, 1]`) and `norm_eval_invPoly_sub_inv_le_neg`
  (on `[-1, -1/4]`): `‖p(x) − (3/4)/(4x)‖ ≤ ε`.

Both certificates are Bernstein bisection certificates over exact rationals checked by
`decide +kernel`; the gap bound (a degree-30 polynomial with a `4.5 · 10⁻⁵` margin) is certified
with `(subdivisions := 14)` as the plateau of `QSVT.Certificate.Sign21`.  Timings (Apple-silicon
laptop) are recorded next to each certificate; the whole module builds in about two minutes.
No `native_decide`: every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`
(audited in `test/QSVTTest/Inverse.lean`).
-/

namespace QSVT.Certificate

open QSVT.Poly

/-- CERT-B/APP-3. The condition-number bound: the gapped region is `|x| ≥ 1/κ`, `κ = 4`.  The
statements below write the literal `4`. -/
def invKappa : ℚ := 4

/-- CERT-B/APP-3. The constant factor in front of `1/(κ x)`: the target is
`invScale / (κ x) = (3/4) / (4x)`. -/
def invScale : ℚ := 3 / 4

/-- CERT-B/APP-3. The certified accuracy: `|4x · p(x) − 3/4| ≤ invEps = 7.5 · 10⁻⁴` on
`[1/4, 1]`, i.e. relative accuracy `10⁻³` with respect to the target `(3/4)/(4x)`. -/
def invEps : ℚ := 0.00075

/-- CERT-B/APP-3. Monomial coefficients (index = degree) of the odd degree-29 approximation of
`(3/4)/(4x)` on `[1/4, 1]`: the constrained Chebyshev minimax fit of
`tools/phases/inv_cheb.py` with the Chebyshev coefficients rounded to 30 significant digits
(exact conversion to the monomial basis). -/
def invPoly : PolyQ :=
  [0,
   -- x^1 ≈ 1.125000e+01
   11250000799484770104487603437085271 / 1000000000000000000000000000000000,
   0,
   -- x^3 ≈ -2.896878e+02
   -14484392097775918494396811542216287 / 50000000000000000000000000000000,
   0,
   -- x^5 ≈ 4.257660e+03
   133051889612161649000497687378435547 / 31250000000000000000000000000000,
   0,
   -- x^7 ≈ -4.012379e+04
   -313467088352000684623854115384776539 / 7812500000000000000000000000000,
   0,
   -- x^9 ≈ 2.582513e+05
   504397081530239849269932166098009751 / 1953125000000000000000000000000,
   0,
   -- x^11 ≈ -1.179764e+06
   -576056878317743339693794528410970829 / 488281250000000000000000000000,
   0,
   -- x^13 ≈ 3.918024e+06
   95654876042542434092159388259172259 / 24414062500000000000000000000,
   0,
   -- x^15 ≈ -9.589633e+06
   -73163094134122289512807586764346499 / 7629394531250000000000000000,
   0,
   -- x^17 ≈ 1.738525e+07
   265277936895048351534039977883729819 / 15258789062500000000000000000,
   0,
   -- x^19 ≈ -2.325991e+07
   -88729507661581307041850051609022891 / 3814697265625000000000000000,
   0,
   -- x^21 ≈ 2.264463e+07
   2699450763117901409842867496703097 / 119209289550781250000000000,
   0,
   -- x^23 ≈ -1.558422e+07
   -74311331959799382289658109534991 / 4768371582031250000000000,
   0,
   -- x^25 ≈ 7.180342e+06
   427981756670728861525511421692983 / 59604644775390625000000000,
   0,
   -- x^27 ≈ -1.986073e+06
   -29594797929626855581726474486721 / 14901161193847656250000000,
   0,
   -- x^29 ≈ 2.492329e+05
   928465053068109756780057484349 / 3725290298461914062500000]

/-! ### Certificates (LeanCert, kernel trust) -/

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (numerically `max |p| = 0.9738`, so the margin is `0.026`; about 30 s in
-- isolation: 18 s untrusted search, 12 s kernel).
/-- CERT-B/APP-3. Admissibility: `-1 ≤ p(x) ≤ 1` on `[-1, 1]`. -/
theorem invPoly_abs_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ invPoly.horner x ∧ invPoly.horner x ≤ 1 := by
  simp only [invPoly, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by
-- `decide +kernel` (numerically `max |4x · p(x) − 3/4| = 7.05 · 10⁻⁴`, margin `4.5 · 10⁻⁵`;
-- bisection depth `14`; about 115 s in isolation: 66 s untrusted search, 47 s kernel).
/-- CERT-B/APP-3 (GSLW Lemma 40 flavour). The inverse bound on the gapped region:
`-ε ≤ 4x · p(x) − 3/4 ≤ ε` on `[1/4, 1]`, `ε = invEps = 7.5 · 10⁻⁴`. -/
theorem invPoly_gap_bound :
    ∀ x ∈ Set.Icc (1 / 4 : ℝ) 1,
      -(invEps : ℝ) ≤ invPoly.horner x * (4 * x) - invScale ∧
        invPoly.horner x * (4 * x) - invScale ≤ invEps := by
  simp only [invPoly, invScale, invEps, PolyQ.horner]
  push_cast
  leancert (subdivisions := 14) (trust := kernel)

/-! ### Consequences -/

/-- CERT-B/APP-3. `p` is odd (all even coefficients vanish). -/
theorem invPoly_horner_neg (x : ℝ) : invPoly.horner (-x) = -invPoly.horner x := by
  simp only [invPoly, PolyQ.horner]
  ring

/-- CERT-B/APP-3. The mirror gap bound `-ε ≤ 4x · p(x) − 3/4 ≤ ε` on `[-1, -1/4]`, by oddness
(`4x · p(x)` is even). -/
theorem invPoly_gap_bound_neg :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-(1 / 4)),
      -(invEps : ℝ) ≤ invPoly.horner x * (4 * x) - invScale ∧
        invPoly.horner x * (4 * x) - invScale ≤ invEps := by
  intro x hx
  have h := invPoly_gap_bound (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [invPoly_horner_neg] at h
  have e : invPoly.horner x * (4 * x) = -invPoly.horner x * (4 * -x) := by ring
  rw [e]
  exact h

theorem invEps_nonneg : (0 : ℝ) ≤ invEps := by
  rw [invEps]; norm_num

/-- CERT-B/APP-3 (helper). From the two-sided bound on `4x · p(x) − 3/4` and `|4x| ≥ 1`:
`|p(x) − (3/4)/(4x)| = |4x · p(x) − 3/4| / |4x| ≤ ε`. -/
theorem abs_horner_sub_inv_le {x : ℝ} (hx : 1 ≤ |4 * x|)
    (h : -(invEps : ℝ) ≤ invPoly.horner x * (4 * x) - invScale ∧
      invPoly.horner x * (4 * x) - invScale ≤ invEps) :
    |invPoly.horner x - invScale / (4 * x)| ≤ invEps := by
  have hpos : (0 : ℝ) < |4 * x| := lt_of_lt_of_le one_pos hx
  have hne : (4 * x) ≠ 0 := fun h0 => by rw [h0, abs_zero] at hpos; exact lt_irrefl _ hpos
  have e : invPoly.horner x - invScale / (4 * x) =
      (invPoly.horner x * (4 * x) - invScale) / (4 * x) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
  rw [e, abs_div, div_le_iff₀ hpos]
  exact (abs_le.mpr h).trans (le_mul_of_one_le_right invEps_nonneg hx)

/-- CERT-B/APP-3. `‖p‖_∞ ≤ 1` for the complex polynomial `invPoly.toPoly`. -/
theorem supNorm_invPoly_le_one : supNorm invPoly.toPoly ≤ 1 :=
  PolyQ.supNorm_toPoly_le_of_horner invPoly_abs_bound

/-- CERT-B/APP-3. `‖p(x) − (3/4)/(4x)‖ ≤ ε` on `[1/4, 1]` for the complex polynomial
`invPoly.toPoly`, `ε = invEps = 7.5 · 10⁻⁴`. -/
theorem norm_eval_invPoly_sub_inv_le :
    ∀ x ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖invPoly.toPoly.eval (x : ℂ) - (((invScale : ℝ) / (4 * x) : ℝ) : ℂ)‖ ≤ invEps := by
  intro x hx
  have hx4 : 1 ≤ |4 * x| := by
    rw [abs_of_pos (by linarith [hx.1])]
    linarith [hx.1]
  have h := abs_le.mp (abs_horner_sub_inv_le hx4 (invPoly_gap_bound x hx))
  exact PolyQ.norm_eval_toPoly_sub_le ⟨by linarith [h.1], by linarith [h.2]⟩

/-- CERT-B/APP-3. `‖p(x) − (3/4)/(4x)‖ ≤ ε` on `[-1, -1/4]` (the target `(3/4)/(4x)` is
negative there, as the odd extension of `1/x`). -/
theorem norm_eval_invPoly_sub_inv_le_neg :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-(1 / 4)),
      ‖invPoly.toPoly.eval (x : ℂ) - (((invScale : ℝ) / (4 * x) : ℝ) : ℂ)‖ ≤ invEps := by
  intro x hx
  have hx4 : 1 ≤ |4 * x| := by
    rw [abs_of_neg (by linarith [hx.2])]
    linarith [hx.2]
  have h := abs_le.mp (abs_horner_sub_inv_le hx4 (invPoly_gap_bound_neg x hx))
  exact PolyQ.norm_eval_toPoly_sub_le ⟨by linarith [h.1], by linarith [h.2]⟩

end QSVT.Certificate
