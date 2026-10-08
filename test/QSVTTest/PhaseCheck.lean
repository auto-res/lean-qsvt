/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.PhaseCheck

/-!
# QSVTTest.PhaseCheck

Regression tests for the QSP phase certificate checker (formal-spec CERT-B, part 2):
`#eval`/`#guard` checks of the interval layer, kernel-checked instances of `check`/`checkRe`
(`decide +kernel`) from degree 1 to degree 21, their transfer through `check_sound`/
`checkRe_sound` to statements about `qspPoly`, and the axiom audit (kernel trust: no
`Lean.ofReduceBool`).

Kernel timings (Apple-silicon laptop, `decide +kernel`, exact rational arithmetic):
degree 1–3 with phases `0`: 0.2 s; degree 2 with phases `[1/3, -1/3]` (Taylor depth 20): 0.35 s;
degree 5 (QSPPACK phases for `T₅`, depth 20): 0.9 s each; degree 21 (QSPPACK phases for the sign
approximation): 40 s at depth 24 (`ε = 1e-10`), 45 s at depth 30 (`ε = 1e-12`,
`sign21_checkRe`).  The Taylor depth must grow with the phase magnitude: for the degree-21 phases
(`|φ| ≤ 2.31`) the real-part bound `errBoundRe` is `8.2e-7` at depth 20, `5.4e-11` at depth 24
and `7.9e-14` at depth 30.
-/

-- `#guard` / `#print axioms` are the whole point of a test file.
set_option linter.hashCommand false

open QSVT.Certificate QSVT.QSP QSVT.Poly
open LeanCert.Core (IntervalRat)

/-! ### The interval layer -/

-- `i · i = -1` on point intervals
#guard CI.mul (CI.mk (IntervalRat.singleton 0) (IntervalRat.singleton 1))
    (CI.mk (IntervalRat.singleton 0) (IntervalRat.singleton 1)) =
  CI.mk (IntervalRat.singleton (-1)) (IntervalRat.singleton 0)

-- `X T₁ = (T₀ + T₂) / 2`
#guard ChebI.mulXI [CI.ofRat 0, CI.ofRat 1] = [CI.ofRat (1 / 2), CI.ofRat 0, CI.ofRat (1 / 2)]

-- `(1 - X²) T₀ = T₀ / 2 - T₂ / 2`
#guard ChebI.oneSubXSqI [CI.ofRat 1] = [CI.ofRat (1 / 2), CI.ofRat 0, CI.ofRat (-1 / 2)]

-- `e^{i·0} = 1` is enclosed exactly
#guard CI.expI 0 20 = CI.ofRat 1

-- phases `0`: `P = T₁ = X` with zero error against the target `[0, 1]`
#guard ChebI.errBound (ChebI.qspChebI 20 [0]).1 [0, 1] = 0

-- the interval recursion on the empty list
/-- info: ([{ re := { lo := 1, hi := 1, le := _ }, im := { lo := 0, hi := 0, le := _ } }], []) -/
#guard_msgs in
#eval ChebI.qspChebI 20 []

/-! ### Kernel-checked certificates, degree ≤ 3 -/

-- degree 1, phases `[0]`: `P = X`
example : check [0] [0, 1] (1 / 1000) 20 = true := by decide +kernel

-- negative test: `P = X` is not the constant `1`
example : check [0] [1] (1 / 1000) 20 = false := by decide +kernel

-- degree 2, phases `[0, 0]`: `P = 1`
example : check [0, 0] [1] (1 / 1000) 20 = true := by decide +kernel

-- degree 3, phases `[0, 0, 0]`: `P = X`
example : check [0, 0, 0] [0, 1] (1 / 1000) 20 = true := by decide +kernel

/-- Degree 2 with transcendental phase factors, `Φ̃ = [1/3, -1/3]`:
`P = x² + e^{2i/3}(1 - x²)`, so `Re P = (1 + cos (2/3)) / 2 · T₀ + (1 - cos (2/3)) / 2 · T₂`;
these are its coefficients as 15-digit decimals. -/
def thirdCheb : List ℚ :=
  [892943630388474 / 1000000000000000, 0, 107056369611526 / 1000000000000000]

/-- `‖Re P_Φ̃ − ∑ₖ tₖ Tₖ‖ ≤ 10⁻¹²` for `Φ̃ = [1/3, -1/3]` (`errBoundRe ≈ 7e-19`). -/
theorem third_checkRe :
    checkRe [1 / 3, -1 / 3] thirdCheb (1 / 1000000000000) 20 = true := by
  decide +kernel

-- the complex check fails for the same data: `Im P ≠ 0`
example : check [1 / 3, -1 / 3] thirdCheb (1 / 10) 20 = false := by
  decide +kernel

/-! ### Degree 5: QSPPACK phases for `T₅` (`tools/phases/examples/T5_qsppack.json`) -/

/-- The reflection-convention phases `phases_R_dyadic` of `T5_qsppack.json` (exact dyadic
rationals). -/
def t5PhasesR : List ℚ :=
  [73659023 / 281474976710656, -3537118875101627 / 2251799813685248,
   -7074237752741821 / 4503599627370496, -7074237752741821 / 4503599627370496,
   -3537118875101627 / 2251799813685248]

/-- `‖P_Φ̃ − T₅‖ ≤ 10⁻⁶` (the solver only fits `Re P`; `Im P` is about `2.6e-7`). -/
theorem t5_check : check t5PhasesR [0, 0, 0, 0, 0, 1] (1 / 1000000) 20 = true := by
  decide +kernel

/-- `‖Re P_Φ̃ − T₅‖ ≤ 10⁻¹²`. -/
theorem t5_checkRe : checkRe t5PhasesR [0, 0, 0, 0, 0, 1] (1 / 1000000000000) 20 = true := by
  decide +kernel

-- transfer to `qspPoly` and `supNorm`
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    ‖(qspPoly (t5PhasesR.map (↑))).1.eval (x : ℂ) -
      (Polynomial.Chebyshev.T ℂ 5).eval (x : ℂ)‖ ≤ 1 / 1000000 := by
  have h := check_sound_target t5_check
  have ht : ChebC.target [0, 0, 0, 0, 0, 1] = Polynomial.Chebyshev.T ℂ 5 := by
    rw [ChebC.target_eq]
    simp [Finset.sum_range_succ]
  rw [ht] at h
  exact fun x hx => (h x hx).trans_eq (by norm_num)

example : supNorm ((qspPoly (t5PhasesR.map (↑))).1 - ChebC.target [0, 0, 0, 0, 0, 1]) ≤
    ((1 / 1000000 : ℚ) : ℝ) :=
  supNorm_sound t5_check

/-! ### Degree 21: QSPPACK phases for the sign approximation
(`tools/phases/examples/sign21_qsppack.json`) -/

/-- The reflection-convention phases `phases_R_dyadic` of `sign21_qsppack.json` (exact dyadic
rationals, reduced mod `2π`). -/
def sign21PhasesR : List ℚ :=
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

/-- The `target_chebyshev_coeffs` of `sign21_qsppack.json`: the odd degree-21 Chebyshev
approximation of `sign x` (the same polynomial as `QSVT.Certificate.sign21`, in the Chebyshev
basis), as exact rationals. -/
def sign21Cheb : List ℚ :=
  [0, 5104259128596299 / 4503599627370496, 0, -1667563197230541 / 4503599627370496,
   0, 7688981794739765 / 36028797018963968, 0, -5170919160542979 / 36028797018963968,
   0, 7422883927095795 / 72057594037927936, 0, -5493494299215661 / 72057594037927936,
   0, 1030359789386511 / 18014398509481984, 0, -3104546081626977 / 72057594037927936,
   0, 2334045259532281 / 72057594037927936, 0, -6978069399079591 / 288230376151711744,
   0, 5171055401310877 / 288230376151711744]

/-- `‖Re P_Φ̃ − ∑ₖ tₖ Tₖ‖ ≤ 10⁻¹²` for the degree-21 sign approximation, kernel-checked with
Taylor depth 30 (about 45 s; `errBoundRe ≈ 7.9e-14`).  The complex check `check` fails here, as
for every solver output: `Im P_Φ̃` is of order `0.7` and only `Re P_Φ̃` is fitted. -/
theorem sign21_checkRe : checkRe sign21PhasesR sign21Cheb (1 / 1000000000000) 30 = true := by
  decide +kernel

-- the certified statement about `qspPoly`: `|Re P_Φ̃(x) − ∑ₖ tₖ Tₖ(x)| ≤ 10⁻¹²` on `[-1, 1]`
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |((qspPoly (sign21PhasesR.map (↑))).1.eval (x : ℂ)).re -
      ∑ k ∈ Finset.range sign21Cheb.length,
        (sign21Cheb.getD k 0 : ℝ) * (Polynomial.Chebyshev.T ℝ k).eval x| ≤
      ((1 / 1000000000000 : ℚ) : ℝ) :=
  checkRe_sound_real sign21_checkRe

/-! ### Axiom audit: kernel-checked certificates use only the standard three axioms -/

/-- info: 'QSVT.Certificate.ChebC.toPoly_qspChebC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ChebC.toPoly_qspChebC

/-- info: 'QSVT.Certificate.listMem_qspChebI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listMem_qspChebI

/-- info: 'QSVT.Certificate.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_sound

/-- info: 'QSVT.Certificate.supNorm_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supNorm_sound

/-- info: 'QSVT.Certificate.checkRe_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkRe_sound

/-- info: 'QSVT.Certificate.checkRe_sound_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkRe_sound_real

/-- info: 'third_checkRe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms third_checkRe

/-- info: 't5_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t5_check

/-- info: 't5_checkRe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t5_checkRe

/-- info: 'sign21_checkRe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign21_checkRe
