/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.PhaseCheck
import QSVT.Certificate.Sign21
import QSVT.SVT.RealPoly

/-!
# Kernel-checked phases for the degree-21 sign approximation (formal-spec CERT-B, part 2)

The certified phase list of the Route B implementation (phase-based QSVT, GSLW Cor 18) of the
degree-21 sign approximation `sign21` of CERT-B part 1.

* `sign21Phases : List ℚ` : the `21` reflection-convention phases `phases_R_dyadic` of
  `tools/phases/examples/sign21_qsppack.json` (QSPPACK output, converted to the R-convention by
  `tools/phases/qsp_conventions.py` and reduced mod `2π`; exact dyadic rationals).
* `sign21Target : List ℚ` : the `22` Chebyshev coefficients `target_chebyshev_coeffs` of the same
  file, as exact rationals.
* `sign21_checkRe : checkRe sign21Phases sign21Target sign21Eps 30 = true`, `sign21Eps = 10⁻¹²`:
  the kernel certificate (`decide +kernel`, Taylor depth `30`, about **45 s** on an Apple-silicon
  laptop; the interval bound `errBoundRe` is `≈ 7.9e-14`).  This is the *only* numerics-dependent
  input of Route B, and it is checked by the Lean kernel alone (no `Lean.ofReduceBool`).
* `sign21_phase_bound` : by `checkRe_sound` and `eval_rePoly_ofReal` (SVT-8),
  `‖Re[P_Φ̃](x) − (∑ₖ tₖ Tₖ)(x)‖ ≤ 10⁻¹²` on `[-1, 1]`.
* `target_sign21_eq : ChebC.target sign21Target = sign21.toPoly` : the JSON target *is* the
  certified polynomial `sign21` of CERT-B part 1.  Proof: `sign21Target` equals the real parts of
  `ChebQC.ofMonomials (PolyQ.toPolyQC sign21)`, the Chebyshev coefficients of `sign21` computed
  inside Lean by POLY-6 (`sign21Target_eq_map_fst`, a kernel evaluation on rational lists, well
  under a second), those coefficients are real (`sign21ChebQC_im_eq_zero`), and
  `ChebQC.toPoly_ofMonomials`.  The two rational lists agree *exactly*: both are the same doubles
  of the JSON, read once as `target_chebyshev_coeffs` and once through the monomial conversion
  `tools/phases/cheb_to_monomial.py` → `sign21` → `ofMonomials`.
* Consequences for the polynomial `Re[P_Φ̃]` realised by the circuit (`rePoly`, SVT-8):
  `sign21_rePoly_bound` (`‖Re[P_Φ̃](x) − sign21(x)‖ ≤ 10⁻¹²` on `[-1, 1]`),
  `sign21_rePoly_sub_scale_le` (`‖Re[P_Φ̃](x) − c‖ ≤ 10⁻¹² + 0.0236` on `[0.15, 1]`,
  `c = sign21Scale`), its mirror `sign21_rePoly_add_scale_le` on `[-1, -0.15]`, and the global
  bound `sign21_rePoly_norm_le` (`‖Re[P_Φ̃](x)‖ ≤ 1 + 10⁻¹²`), all by the triangle inequality with
  the LeanCert certificates of CERT-B part 1.

The circuit-level statements (`HermitianEncoding.qsvtReal`, `compileQsvtReal`, eigenvector-level
behaviour, query count `21`) are assembled in `QSVT.Examples.Sign21RouteB` (APP-1).
-/

namespace QSVT.Certificate

open Polynomial
open QSVT.Poly QSVT.QSP QSVT.SVT

/-! ### The data -/

/-- CERT-B. The `21` reflection-convention phases `phases_R_dyadic` of `sign21_qsppack.json`
(QSPPACK output for the degree-21 sign approximation, exact dyadic rationals reduced mod `2π`;
`|φ| ≤ 2.31`).  The last `20` phases are palindromic (symmetric QSP), the first carries the
convention shift. -/
def sign21Phases : List ℚ :=
  [215730704601777 / 140737488355328, -3483537972770937 / 2251799813685248,
   -7209831662386485 / 4503599627370496, -6901305567289623 / 4503599627370496,
   -7296699691818309 / 4503599627370496, -6784661288090225 / 4503599627370496,
   -3729219811284745 / 2251799813685248, -1636729195328927 / 1125899906842624,
   -3923397093034391 / 2251799813685248, -2883881419528359 / 2251799813685248,
   -5199479559502869 / 2251799813685248, -5199479559502869 / 2251799813685248,
   -2883881419528359 / 2251799813685248, -3923397093034391 / 2251799813685248,
   -1636729195328927 / 1125899906842624, -3729219811284745 / 2251799813685248,
   -6784661288090225 / 4503599627370496, -7296699691818309 / 4503599627370496,
   -6901305567289623 / 4503599627370496, -7209831662386485 / 4503599627370496,
   -3483537972770937 / 2251799813685248]

/-- CERT-B. The `target_chebyshev_coeffs` of `sign21_qsppack.json`: the Chebyshev coefficients
of the odd degree-21 approximation of `c · sign x` (the polynomial `sign21` of CERT-B part 1,
`target_sign21_eq`), as exact rationals. -/
def sign21Target : List ℚ :=
  [0, 5104259128596299 / 4503599627370496, 0, -1667563197230541 / 4503599627370496,
   0, 7688981794739765 / 36028797018963968, 0, -5170919160542979 / 36028797018963968,
   0, 7422883927095795 / 72057594037927936, 0, -5493494299215661 / 72057594037927936,
   0, 1030359789386511 / 18014398509481984, 0, -3104546081626977 / 72057594037927936,
   0, 2334045259532281 / 72057594037927936, 0, -6978069399079591 / 288230376151711744,
   0, 5171055401310877 / 288230376151711744]

/-- CERT-B. The certified tolerance `ε = 10⁻¹²` of the phase certificate. -/
def sign21Eps : ℚ := 1 / 10 ^ 12

/-- CERT-B. `21` phases: the degree of `sign21`, hence the query count of Route B. -/
theorem sign21Phases_length : sign21Phases.length = 21 := rfl

/-- CERT-B. `22` target coefficients (degrees `0, …, 21`). -/
theorem sign21Target_length : sign21Target.length = 22 := rfl

/-! ### The kernel certificate -/

-- Kernel certificate: the interval QSP recursion in exact rational arithmetic (Taylor depth 30),
-- reduced by `decide +kernel`; about 45 s wall-clock on an Apple-silicon laptop
-- (`errBoundRe ≈ 7.9e-14`; depth 24 gives `5.4e-11` in 40 s, depth 20 only `8.2e-7`).
/-- CERT-B. The phase certificate: `‖Re P_Φ̃ − ∑ₖ tₖ Tₖ‖ ≤ 10⁻¹²` for the degree-21 sign
approximation, checked by the Lean kernel (`decide +kernel`, Taylor depth `30`, about 45 s).  The
complex check `check` fails for these phases, as for every solver output: `Im P_Φ̃` is of order
`0.7` and only `Re P_Φ̃` is fitted (GSLW Cor 18 realises exactly `Re P_Φ̃`, `rePoly`). -/
theorem sign21_checkRe : checkRe sign21Phases sign21Target sign21Eps 30 = true := by
  decide +kernel

/-- CERT-B. The certified statement about the QSP polynomial of the phases (SVT-8 form):
`‖Re[P_Φ̃](x) − (∑ₖ tₖ Tₖ)(x)‖ ≤ 10⁻¹²` on `[-1, 1]`, with `Re[P_Φ̃] = rePoly (qspPoly Φ̃).1` the
polynomial realised by GSLW Cor 18. -/
theorem sign21_phase_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) -
        (ChebC.target sign21Target).eval (x : ℂ)‖ ≤ sign21Eps := by
  intro x hx
  rw [eval_rePoly_ofReal]
  exact checkRe_sound sign21_checkRe x hx

/-! ### The target is the certified polynomial `sign21` -/

/-- CERT-B (helper). A real Chebyshev coefficient list (`ChebQC`, all imaginary parts zero) read
through its real parts gives the same polynomial:
`ChebC.target (c.map Prod.fst) = ChebQC.toPoly c`. -/
theorem ChebC.target_map_fst (c : ChebQC) (h : ∀ z ∈ c, z.2 = 0) :
    ChebC.target (c.map Prod.fst) = ChebQC.toPoly c := by
  rw [ChebC.target_eq, ChebQC.toPoly, List.length_map]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < c.length := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem (c.map Prod.fst) 0 (by simpa using hk'),
    List.getElem_map]
  congr 2
  simp [QC.toC, h _ (List.getElem_mem hk')]

/-- CERT-B. The Chebyshev coefficients of `sign21` computed inside Lean (POLY-6) are all real
(kernel evaluation). -/
theorem sign21ChebQC_im_eq_zero : ∀ z ∈ ChebQC.ofMonomials (PolyQ.toPolyQC sign21), z.2 = 0 := by
  decide +kernel

/-- CERT-B. The JSON target coefficients are exactly the real parts of the Chebyshev coefficients
of `sign21` computed by POLY-6 `ChebQC.ofMonomials` (kernel evaluation on rational lists). -/
theorem sign21Target_eq_map_fst :
    sign21Target = (ChebQC.ofMonomials (PolyQ.toPolyQC sign21)).map Prod.fst := by
  decide +kernel

/-- CERT-B. The certified target of the phases is the certified polynomial of CERT-B part 1:
`∑ₖ tₖ Tₖ = sign21`. -/
theorem target_sign21_eq : ChebC.target sign21Target = sign21.toPoly := by
  rw [sign21Target_eq_map_fst, ChebC.target_map_fst _ sign21ChebQC_im_eq_zero,
    ChebQC.toPoly_ofMonomials]
  rfl

/-! ### Bounds on the realised polynomial `Re[P_Φ̃]` -/

/-- CERT-B. `‖Re[P_Φ̃](x) − sign21(x)‖ ≤ 10⁻¹²` on `[-1, 1]`. -/
theorem sign21_rePoly_bound :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) - sign21.toPoly.eval (x : ℂ)‖ ≤
        sign21Eps := by
  rw [← target_sign21_eq]
  exact sign21_phase_bound

/-- CERT-B. On the positive plateau `[0.15, 1]`: `‖Re[P_Φ̃](x) − c‖ ≤ 10⁻¹² + 0.0236`,
`c = sign21Scale` (phase certificate plus `norm_eval_sign21_sub_scale_le`). -/
theorem sign21_rePoly_sub_scale_le :
    ∀ x ∈ Set.Icc (0.15 : ℝ) 1,
      ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) - (sign21Scale : ℂ)‖ ≤
        sign21Eps + 0.0236 := by
  intro x hx
  have h1 := sign21_rePoly_bound x ⟨by linarith [hx.1], hx.2⟩
  have h2 := norm_eval_sign21_sub_scale_le x hx
  rw [Complex.ofReal_ratCast] at h2
  calc ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) - (sign21Scale : ℂ)‖
      = ‖((rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) - sign21.toPoly.eval (x : ℂ)) +
          (sign21.toPoly.eval (x : ℂ) - (sign21Scale : ℂ))‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ sign21Eps + 0.0236 := add_le_add h1 h2

/-- CERT-B. On the negative plateau `[-1, -0.15]`: `‖Re[P_Φ̃](x) + c‖ ≤ 10⁻¹² + 0.0236`,
`c = sign21Scale` (phase certificate plus `norm_eval_sign21_add_scale_le`). -/
theorem sign21_rePoly_add_scale_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) (-0.15),
      ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) + (sign21Scale : ℂ)‖ ≤
        sign21Eps + 0.0236 := by
  intro x hx
  have h1 := sign21_rePoly_bound x ⟨hx.1, by linarith [hx.2]⟩
  have h2 := norm_eval_sign21_add_scale_le x hx
  rw [Complex.ofReal_ratCast] at h2
  calc ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) + (sign21Scale : ℂ)‖
      = ‖((rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) - sign21.toPoly.eval (x : ℂ)) +
          (sign21.toPoly.eval (x : ℂ) + (sign21Scale : ℂ))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ sign21Eps + 0.0236 := add_le_add h1 h2

/-- CERT-B. Global bound `‖Re[P_Φ̃](x)‖ ≤ 1 + 10⁻¹²` on `[-1, 1]` (phase certificate plus the
admissibility certificate `supNorm_sign21_le_one`). -/
theorem sign21_rePoly_norm_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ)‖ ≤ 1 + sign21Eps := by
  intro x hx
  have h1 := sign21_rePoly_bound x hx
  have h2 : ‖sign21.toPoly.eval (x : ℂ)‖ ≤ 1 :=
    (norm_eval_le_supNorm _ hx).trans supNorm_sign21_le_one
  calc ‖(rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ)‖
      = ‖((rePoly (qspPoly (sign21Phases.map (↑))).1).eval (x : ℂ) - sign21.toPoly.eval (x : ℂ)) +
          sign21.toPoly.eval (x : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ sign21Eps + 1 := add_le_add h1 h2
    _ = 1 + sign21Eps := add_comm _ _

end QSVT.Certificate
