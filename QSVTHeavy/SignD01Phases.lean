/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Sign21Phases
import QSVTHeavy.SignD01

/-!
# Kernel-checked phases for the degree-35 sign approximation with gap `0.1` (CERT-B, part 2)

The certified phase list of the Route B implementation (phase-based QSVT, GSLW Cor 18) of the
degree-35 sign approximation `signD01` of CERT-B part 1 (`QSVT.Certificate.SignD01`), the
analogue of `QSVT.Certificate.Sign21Phases` for the gap `δ = 0.1` and plateau value `0.9875`.

* `signD01Phases : List ℚ` : the `35` reflection-convention phases `phases_R_dyadic` of
  `tools/phases/examples/sign_d01_pyqsp_symqsp.json` (pyqsp `sym_qsp` output, Newton iteration of
  Dong–Meng–Whaley–Lin, converted to the R convention by `tools/phases/qsp_conventions.W_to_R`
  and reduced mod `2π`; exact dyadic rationals, `|φ| ≤ 2.1`).  The QSPPACK phases for the same
  target (`sign_d01_qsppack.json`, FPI) are a different completion with `|φ| ≤ 2.62` and would
  need `ε = 10⁻¹¹` at Taylor depth `30` (`errBoundRe ≈ 1.7e-12`).
* `signD01Target : List ℚ` : the `36` Chebyshev coefficients `target_chebyshev_coeffs` of the
  same file, as exact rationals.
* `signD01_checkRe : checkRe signD01Phases signD01Target signD01Eps 30 = true`,
  `signD01Eps = 10⁻¹²`: the kernel certificate (`decide +kernel`, Taylor depth `30`; the interval
  bound `errBoundRe` is `≈ 2.3e-13`; depth `28` gives `8.5e-11`, depth `24` only `7.8e-6`), about
  **265 s** on an Apple-silicon laptop, against 45 s for the degree-21 `sign21_checkRe` (the cost
  grows like the cube of the degree).  This is the *only* numerics-dependent input of Route
  B, and it is checked by the Lean kernel alone (no `Lean.ofReduceBool`).
* `signD01_phase_bound` : by `checkRe_sound` and `eval_rePoly_ofReal` (SVT-8),
  `‖Re[P_Φ̃](x) − (∑ₖ tₖ Tₖ)(x)‖ ≤ 10⁻¹²` on `[-1, 1]`.
* `target_signD01_eq : ChebC.target signD01Target = signD01.toPoly` : the JSON target *is* the
  certified polynomial `signD01` of CERT-B part 1, by the same argument as `target_sign21_eq`:
  `signD01Target` equals the real parts of `ChebQC.ofMonomials (PolyQ.toPolyQC signD01)`
  (`signD01Target_eq_map_fst`, a kernel evaluation on rational lists), those coefficients are
  real (`signD01ChebQC_im_eq_zero`), and `ChebC.target_map_fst` (the helper of
  `Sign21Phases`, imported for this purpose) with `ChebQC.toPoly_ofMonomials`.  The two rational
  lists agree *exactly*: both are the same doubles of the JSON, read once as
  `target_chebyshev_coeffs` and once through `tools/phases/cheb_to_monomial.py` → `signD01` →
  `ofMonomials`.
* Consequences for the polynomial `Re[P_Φ̃]` realised by the circuit (`rePoly`, SVT-8):
  `signD01_rePoly_bound` (`‖Re[P_Φ̃](x) − signD01(x)‖ ≤ 10⁻¹²` on `[-1, 1]`),
  `signD01_rePoly_sub_scale_le` (`‖Re[P_Φ̃](x) − c‖ ≤ 10⁻¹² + 0.012` on `[0.1, 1]`,
  `c = signD01Scale = 0.9875`), its mirror `signD01_rePoly_add_scale_le` on `[-1, -0.1]`, and the
  global bound `signD01_rePoly_norm_le` (`‖Re[P_Φ̃](x)‖ ≤ 1 + 10⁻¹²`), all by the triangle
  inequality with the LeanCert certificates of CERT-B part 1.
-/

namespace QSVT.Certificate

open Polynomial
open QSVT.Poly QSVT.QSP QSVT.SVT

/-! ### The data -/

/-- CERT-B. The `35` reflection-convention phases `phases_R_dyadic` of
`sign_d01_pyqsp_symqsp.json` (pyqsp `sym_qsp` output for the degree-35 sign approximation with
gap `0.1`, exact dyadic rationals reduced mod `2π`; `|φ| ≤ 2.1`).  The last `34` phases are
palindromic (symmetric QSP), the first carries the convention shift. -/
def signD01Phases : List ℚ :=
  [51506174637215 / 35184372088832, -6975934299978917 / 4503599627370496,
   -7192563172336785 / 4503599627370496, -3466566039370221 / 2251799813685248,
   -1810328465423487 / 1125899906842624, -859681622395475 / 562949953421312,
   -7305253767986519 / 4503599627370496, -6803402450960853 / 4503599627370496,
   -3696018577900723 / 2251799813685248, -6700048462308295 / 4503599627370496,
   -1879442817908281 / 1125899906842624, -6542774351150517 / 4503599627370496,
   -3860953021607577 / 2251799813685248, -6264131358216875 / 4503599627370496,
   -2032532307682999 / 1125899906842624, -2799657790680751 / 2251799813685248,
   -2353720553013779 / 1125899906842624, -73917979008299 / 140737488355328,
   -73917979008299 / 140737488355328, -2353720553013779 / 1125899906842624,
   -2799657790680751 / 2251799813685248, -2032532307682999 / 1125899906842624,
   -6264131358216875 / 4503599627370496, -3860953021607577 / 2251799813685248,
   -6542774351150517 / 4503599627370496, -1879442817908281 / 1125899906842624,
   -6700048462308295 / 4503599627370496, -3696018577900723 / 2251799813685248,
   -6803402450960853 / 4503599627370496, -7305253767986519 / 4503599627370496,
   -859681622395475 / 562949953421312, -1810328465423487 / 1125899906842624,
   -3466566039370221 / 2251799813685248, -7192563172336785 / 4503599627370496,
   -6975934299978917 / 4503599627370496]

/-- CERT-B. The `target_chebyshev_coeffs` of `sign_d01_pyqsp_symqsp.json`: the Chebyshev
coefficients of the odd degree-35 approximation of `c · sign x` (the polynomial `signD01` of
CERT-B part 1, `target_signD01_eq`), as exact rationals. -/
def signD01Target : List ℚ :=
  [0, 2828367495517317 / 2251799813685248, 0, -7477875473428205 / 18014398509481984, 0,
   551266194019491 / 2251799813685248, 0, -3069375610572867 / 18014398509481984, 0,
   4610979109178287 / 36028797018963968, 0, -7220382793865181 / 72057594037927936, 0,
   5791610458009897 / 72057594037927936, 0, -4711677068098569 / 72057594037927936, 0,
   7724840317899753 / 144115188075855872, 0, -198493276622051 / 4503599627370496, 0,
   652497504394327 / 18014398509481984, 0, -8549906969668953 / 288230376151711744, 0,
   6958720084853437 / 288230376151711744, 0, -5613447801745993 / 288230376151711744, 0,
   8950117268893847 / 576460752303423488, 0, -7027688801744001 / 576460752303423488, 0,
   1352802910615637 / 144115188075855872, 0, -8935138670902553 / 576460752303423488]


/-- CERT-B. The certified tolerance `ε = 10⁻¹²` of the phase certificate. -/
def signD01Eps : ℚ := 1 / 10 ^ 12

/-- CERT-B. `35` phases: the degree of `signD01`, hence the query count of Route B. -/
theorem signD01Phases_length : signD01Phases.length = 35 := rfl

/-- CERT-B. `36` target coefficients (degrees `0, …, 35`). -/
theorem signD01Target_length : signD01Target.length = 36 := rfl

/-! ### The kernel certificate -/

-- Kernel certificate: the interval QSP recursion in exact rational arithmetic (Taylor depth 30),
-- reduced by `decide +kernel`; about 265 s wall-clock on an Apple-silicon laptop (the module builds
-- in 276 s; `errBoundRe ≈ 2.3e-13`; depth 28 gives `8.5e-11`, depth 24 only `7.8e-6`).  The cost
-- grows like the cube of the degree (45 s for the degree-21 `sign21_checkRe`): exact rational
-- arithmetic on coefficients whose size grows linearly along the recursion.
/-- CERT-B. The phase certificate: `‖Re P_Φ̃ − ∑ₖ tₖ Tₖ‖ ≤ 10⁻¹²` for the degree-35 sign
approximation with gap `0.1`, checked by the Lean kernel (`decide +kernel`, Taylor depth `30`).
As for every solver output only `Re P_Φ̃` is fitted (`Im P_Φ̃` is of order `0.49`); GSLW Cor 18
realises exactly `Re P_Φ̃` (`rePoly`). -/
theorem signD01_checkRe : checkRe signD01Phases signD01Target signD01Eps 30 = true := by
  decide +kernel

/-- CERT-B. The certified statement about the QSP polynomial of the phases (SVT-8 form):
`‖Re[P_Φ̃](x) − (∑ₖ tₖ Tₖ)(x)‖ ≤ 10⁻¹²` on `[-1, 1]`, with `Re[P_Φ̃] = rePoly (qspPoly Φ̃).1` the
polynomial realised by GSLW Cor 18. -/
theorem signD01_phase_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) -
        (ChebC.target signD01Target).eval (x : ℂ)‖ ≤ signD01Eps := by
  intro x hx
  rw [eval_rePoly_ofReal]
  exact checkRe_sound signD01_checkRe x hx

/-! ### The target is the certified polynomial `signD01` -/

/-- CERT-B. The Chebyshev coefficients of `signD01` computed inside Lean (POLY-6) are all real
(kernel evaluation). -/
theorem signD01ChebQC_im_eq_zero :
    ∀ z ∈ ChebQC.ofMonomials (PolyQ.toPolyQC signD01), z.2 = 0 := by
  decide +kernel

/-- CERT-B. The JSON target coefficients are exactly the real parts of the Chebyshev coefficients
of `signD01` computed by POLY-6 `ChebQC.ofMonomials` (kernel evaluation on rational lists). -/
theorem signD01Target_eq_map_fst :
    signD01Target = (ChebQC.ofMonomials (PolyQ.toPolyQC signD01)).map Prod.fst := by
  decide +kernel

/-- CERT-B. The certified target of the phases is the certified polynomial of CERT-B part 1:
`∑ₖ tₖ Tₖ = signD01`. -/
theorem target_signD01_eq : ChebC.target signD01Target = signD01.toPoly := by
  rw [signD01Target_eq_map_fst, ChebC.target_map_fst _ signD01ChebQC_im_eq_zero,
    ChebQC.toPoly_ofMonomials]
  rfl

/-! ### Bounds on the realised polynomial `Re[P_Φ̃]` -/

/-- CERT-B. `‖Re[P_Φ̃](x) − signD01(x)‖ ≤ 10⁻¹²` on `[-1, 1]`. -/
theorem signD01_rePoly_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) -
        signD01.toPoly.eval (x : ℂ)‖ ≤ signD01Eps := by
  rw [← target_signD01_eq]
  exact signD01_phase_bound

/-- CERT-B. On the positive plateau `[0.1, 1]`: `‖Re[P_Φ̃](x) − c‖ ≤ 10⁻¹² + 0.012`,
`c = signD01Scale = 0.9875` (phase certificate plus `norm_eval_signD01_sub_scale_le`). -/
theorem signD01_rePoly_sub_scale_le :
    ∀ x ∈ Set.Icc (0.1 : ℝ) 1,
      ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) - (signD01Scale : ℂ)‖ ≤
        signD01Eps + 0.012 := by
  intro x hx
  have h1 := signD01_rePoly_bound x ⟨by linarith [hx.1], hx.2⟩
  have h2 := norm_eval_signD01_sub_scale_le x hx
  rw [Complex.ofReal_ratCast] at h2
  calc ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) - (signD01Scale : ℂ)‖
      = ‖((rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) -
            signD01.toPoly.eval (x : ℂ)) +
          (signD01.toPoly.eval (x : ℂ) - (signD01Scale : ℂ))‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ signD01Eps + 0.012 := add_le_add h1 h2

/-- CERT-B. On the negative plateau `[-1, -0.1]`: `‖Re[P_Φ̃](x) + c‖ ≤ 10⁻¹² + 0.012`,
`c = signD01Scale = 0.9875` (phase certificate plus `norm_eval_signD01_add_scale_le`). -/
theorem signD01_rePoly_add_scale_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.1),
      ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) + (signD01Scale : ℂ)‖ ≤
        signD01Eps + 0.012 := by
  intro x hx
  have h1 := signD01_rePoly_bound x ⟨hx.1, by linarith [hx.2]⟩
  have h2 := norm_eval_signD01_add_scale_le x hx
  rw [Complex.ofReal_ratCast] at h2
  calc ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) + (signD01Scale : ℂ)‖
      = ‖((rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) -
            signD01.toPoly.eval (x : ℂ)) +
          (signD01.toPoly.eval (x : ℂ) + (signD01Scale : ℂ))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ signD01Eps + 0.012 := add_le_add h1 h2

/-- CERT-B. Global bound `‖Re[P_Φ̃](x)‖ ≤ 1 + 10⁻¹²` on `[-1, 1]` (phase certificate plus the
admissibility certificate `supNorm_signD01_le_one`). -/
theorem signD01_rePoly_norm_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ)‖ ≤ 1 + signD01Eps := by
  intro x hx
  have h1 := signD01_rePoly_bound x hx
  have h2 : ‖signD01.toPoly.eval (x : ℂ)‖ ≤ 1 :=
    (norm_eval_le_supNorm _ hx).trans supNorm_signD01_le_one
  calc ‖(rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ)‖
      = ‖((rePoly (qspPoly (signD01Phases.map (↑))).1).eval (x : ℂ) -
            signD01.toPoly.eval (x : ℂ)) +
          signD01.toPoly.eval (x : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ signD01Eps + 1 := add_le_add h1 h2
    _ = 1 + signD01Eps := add_comm _ _

end QSVT.Certificate
