/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Bound

/-!
# Worked certificate: the degree-21 sign-function approximation (formal-spec CERT-B, part 1)

The target polynomial of `tools/phases/examples/sign21_qsppack.json` (also
`sign21_pyqsp_symqsp.json`): the odd degree-21 Chebyshev approximation of `sign x` produced by
pyqsp's `PolySign` (Chebyshev interpolant of `erf(10 x)`, rescaled by `0.8923886753673906` so that
the QSP polynomial fits in the unit disc).  The Chebyshev coefficients are stored in the JSON as
exact decimal expansions of doubles; `tools/phases/cheb_to_monomial.py` converts them to the exact
monomial coefficient list `sign21 : PolyQ` below (dyadic rationals, computed outside Lean; the
conversion is untrusted but every statement here is about `sign21` itself).

Certified statements (LeanCert, kernel trust; numerically `max |p| = 0.91580…` on `[-1, 1]`,
`p ∈ [0.86923…, 0.91580…]` on `[0.15, 1]`):

* `sign21_horner_bound` : `-1 ≤ p(x) ≤ 1` on `[-1, 1]` (admissibility), hence
  `supNorm_sign21_le_one : ‖p‖_∞ ≤ 1`.
* `sign21_plateau` : `0.8692 ≤ p(x) ≤ 0.9159` on `[δ, 1]` with `δ = 0.15`, and by oddness
  (`sign21_horner_neg`, an exact `ring` identity) the mirror `sign21_plateau_neg` on `[-1, -δ]`.
* `norm_eval_sign21_sub_scale_le` : `‖p(x) − c‖ ≤ ε` on `[δ, 1]` for the complex polynomial
  `sign21.toPoly`, with the plateau value `c = sign21Scale = 0.8923886753673906` and
  `ε = 0.0236` (and the mirror `norm_eval_sign21_add_scale_le`).  The ripple `±0.023` is the
  Chebyshev truncation error of the degree-21 interpolant of `erf(10 x)`, not a certification
  slack: the two-sided decimal bounds above are within `1e-4` of the numerical extrema.

Both LeanCert calls are closed by the Bernstein strategy (exact rational Bernstein coefficients on
a bisection tree, one Boolean certificate reduced by `decide +kernel`); `leancert` needs
`(subdivisions := 14)` for the plateau (the router's default bisection depth 4 is too coarse for
a `1e-4` margin) and `maxHeartbeats 4000000`.  Timings on an Apple-silicon laptop: about 25 s
for the global bound and 40 s for the plateau in isolation; the whole module builds in about a
minute.
`bernstein_bound 12 (trust := kernel)` also certifies each one-sided bound but prints a stray
`ring` info message, so the router is used.
-/

namespace QSVT.Certificate

open QSVT.Poly

/-- CERT-B. Monomial coefficients (index = degree) of the degree-21 odd sign approximation,
`∑ₖ cₖ Tₖ` with the `target_chebyshev_coeffs` of `sign21_qsppack.json` (exact conversion by
`tools/phases/cheb_to_monomial.py`). -/
def sign21 : PolyQ :=
  [0,
   1276695597083805399 / 144115188075855872,      -- x^1  ≈  8.858855e+00
   0,
   -3053919444637669801 / 18014398509481984,      -- x^3  ≈ -1.695266e+02
   0,
   36706388884741918581 / 18014398509481984,      -- x^5  ≈  2.037614e+03
   0,
   -16008048384044981249 / 1125899906842624,      -- x^7  ≈ -1.421800e+04
   0,
   34340154590280406615 / 562949953421312,        -- x^9  ≈  6.100037e+04
   0,
   -11797815007087978035 / 70368744177664,        -- x^11 ≈ -1.676570e+05
   0,
   21157083095307074947 / 70368744177664,         -- x^13 ≈  3.006602e+05
   0,
   -769330569085344469 / 2199023255552,           -- x^15 ≈ -3.498510e+05
   0,
   559624485234198553 / 2199023255552,            -- x^17 ≈  2.544878e+05
   0,
   -14446279103326001 / 137438953472,             -- x^19 ≈ -1.051105e+05
   0,
   5171055401310877 / 274877906944]               -- x^21 ≈  1.881219e+04

/-- CERT-B. The plateau value: pyqsp's rescaling constant `0.8923886753673906` of the target
`c · sign x`. -/
def sign21Scale : ℚ := 4461943376836953 / 5000000000000000

/-! ### Certificates (LeanCert, kernel trust) -/

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by `decide +kernel`
-- (about 25 s wall-clock in isolation).
/-- CERT-B. Admissibility: `-1 ≤ p(x) ≤ 1` on `[-1, 1]`. -/
theorem sign21_horner_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ sign21.horner x ∧ sign21.horner x ≤ 1 := by
  simp only [sign21, PolyQ.horner]
  push_cast
  leancert (trust := kernel)

set_option maxHeartbeats 4000000 in
-- LeanCert kernel certificate: Bernstein bisection over exact rationals, checked by `decide +kernel`
-- (about 40 s wall-clock in isolation; the default bisection depth 4 fails, 14 succeeds).
/-- CERT-B. Plateau: `0.8692 ≤ p(x) ≤ 0.9159` on `[δ, 1]`, `δ = 0.15` (numerically
`p ∈ [0.869234, 0.915803]` there). -/
theorem sign21_plateau :
    ∀ x ∈ Set.Icc (0.15 : ℝ) 1, 0.8692 ≤ sign21.horner x ∧ sign21.horner x ≤ 0.9159 := by
  simp only [sign21, PolyQ.horner]
  push_cast
  leancert (subdivisions := 14) (trust := kernel)

/-! ### Consequences -/

/-- CERT-B. `p` is odd (all even coefficients vanish). -/
theorem sign21_horner_neg (x : ℝ) : sign21.horner (-x) = -sign21.horner x := by
  simp only [sign21, PolyQ.horner]
  ring

/-- CERT-B. The mirror plateau `-0.9159 ≤ p(x) ≤ -0.8692` on `[-1, -0.15]`, by oddness. -/
theorem sign21_plateau_neg :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.15), -0.9159 ≤ sign21.horner x ∧ sign21.horner x ≤ -0.8692 := by
  intro x hx
  have h := sign21_plateau (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [sign21_horner_neg] at h
  constructor <;> linarith [h.1, h.2]

/-- CERT-B. `‖p‖_∞ ≤ 1` for the complex polynomial `sign21.toPoly`. -/
theorem supNorm_sign21_le_one : supNorm sign21.toPoly ≤ 1 :=
  PolyQ.supNorm_toPoly_le_of_horner sign21_horner_bound

/-- CERT-B. `‖p(x) − c‖ ≤ 0.0236` on `[0.15, 1]`, `c = sign21Scale`. -/
theorem norm_eval_sign21_sub_scale_le :
    ∀ x ∈ Set.Icc (0.15 : ℝ) 1,
      ‖sign21.toPoly.eval (x : ℂ) - ((sign21Scale : ℝ) : ℂ)‖ ≤ 0.0236 :=
  PolyQ.forall_norm_eval_sub_le_of_two_sided fun x hx => by
    have h := sign21_plateau x hx
    have hc : (sign21Scale : ℝ) = 4461943376836953 / 5000000000000000 := by
      rw [sign21Scale]; push_cast; ring
    rw [hc]
    constructor <;> linarith [h.1, h.2]

/-- CERT-B. `‖p(x) + c‖ ≤ 0.0236` on `[-1, -0.15]`, `c = sign21Scale`. -/
theorem norm_eval_sign21_add_scale_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.15),
      ‖sign21.toPoly.eval (x : ℂ) + ((sign21Scale : ℝ) : ℂ)‖ ≤ 0.0236 := by
  intro x hx
  have h := PolyQ.forall_norm_eval_sub_le_of_two_sided (l := sign21) (c := -(sign21Scale : ℝ))
    (ε := 0.0236) (fun y hy => by
      have h := sign21_plateau_neg y hy
      have hc : (sign21Scale : ℝ) = 4461943376836953 / 5000000000000000 := by
        rw [sign21Scale]; push_cast; ring
      rw [hc]
      constructor <;> linarith [h.1, h.2]) x hx
  simpa [sub_neg_eq_add] using h

end QSVT.Certificate
