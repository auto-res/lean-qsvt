/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import QSVT.QSP.Conventions

/-!
# Chebyshev phases (formal-spec QSP-4, GSLW Lemma 9)

The phase sequence `Φ = ((1-d)π/2, π/2, …, π/2)` of length `d` realizes the Chebyshev
polynomial `T_d` in the reflection convention: the top-left entry of `seqR Φ x` is `T_d(x)`.
In fact the whole matrix is

  `seqR Φ x = [[T_d(x), U_{d-1}(x) s], [(-1)^(d+1) U_{d-1}(x) s, (-1)^d T_d(x)]]`,

with `s = √(1-x²)`, where `U` is the Chebyshev polynomial of the second kind (Mathlib's
`ℤ`-indexed `Polynomial.Chebyshev.U`, with `U_{-1} = 0`).

The proof is algebraic: `e^{iπσ_z/2} R(x) = i • rot x` with `rot x = [[x, s], [-s, x]]`, and the
powers of `rot x` are computed by induction from the recurrences
`T_{n+1} = X T_n - (1 - X²) U_{n-1}` and `U_n = X U_{n-1} + T_n`
(`Polynomial.Chebyshev.T_eq_X_mul_T_sub_pol_U`, `Polynomial.Chebyshev.U_eq_X_mul_U_add_T`).
The leading phase `e^{i(1-d)πσ_z/2}` cancels the factor `i^d` up to the sign pattern above.
-/

namespace QSVT.QSP

open Matrix Complex Polynomial
open scoped Real

/-- QSP-4. The GSLW Lemma 9 phases `((1-d)π/2, π/2, …, π/2)` (length `d`) realizing `T_d`.
For `d = 0` the list is empty (`seqR [] x = 1 = T_0(x)`), so the closed form below holds for every
`d`; for `d ≥ 1` the list is `((1-d)π/2) :: replicate (d-1) (π/2)`, see `chebPhases_eq`. -/
noncomputable def chebPhases : ℕ → List ℝ
  | 0 => []
  | d + 1 => ((1 - ((d + 1 : ℕ) : ℝ)) * π / 2) :: List.replicate d (π / 2)

@[simp]
theorem chebPhases_zero : chebPhases 0 = [] := rfl

theorem chebPhases_succ (d : ℕ) :
    chebPhases (d + 1) = ((1 - ((d + 1 : ℕ) : ℝ)) * π / 2) :: List.replicate d (π / 2) :=
  rfl

/-- For `d ≥ 1`, `chebPhases d = ((1-d)π/2) :: replicate (d-1) (π/2)`. -/
theorem chebPhases_eq {d : ℕ} (hd : 1 ≤ d) :
    chebPhases d = ((1 - (d : ℝ)) * π / 2) :: List.replicate (d - 1) (π / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rfl

@[simp]
theorem chebPhases_length (d : ℕ) : (chebPhases d).length = d := by
  cases d with
  | zero => rfl
  | succ n => simp [chebPhases_succ]

/-! ### The rotation `rot x` and its powers -/

/-- The rotation `[[x, s], [-s, x]]` with `s = √(1-x²)`; for `x = cos θ` this is the rotation by
the angle `θ`. One has `e^{iπσ_z/2} R(x) = i • rot x` (`phaseZ_pi_div_two_mul_Rref`). -/
noncomputable def rot (x : ℝ) : M₂ :=
  !![(x : ℂ), (Real.sqrt (1 - x ^ 2) : ℂ); -(Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)]

theorem phaseZ_pi_div_two : phaseZ (π / 2) = !![I, 0; 0, -I] := by
  have h1 : I * ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 * I := by push_cast; ring
  have h2 : -(I * ((π / 2 : ℝ) : ℂ)) = -(π : ℂ) / 2 * I := by push_cast; ring
  rw [phaseZ, h2, h1, exp_pi_div_two_mul_I, exp_neg_pi_div_two_mul_I]

/-- `e^{iπσ_z/2} R(x) = i • rot x`. -/
theorem phaseZ_pi_div_two_mul_Rref (x : ℝ) : phaseZ (π / 2) * Rref x = I • rot x := by
  rw [phaseZ_pi_div_two, Rref, rot]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `e^{-i d π σ_z / 2} = diag((-i)^d, i^d)`. -/
theorem phaseZ_neg_nat_mul_pi_div_two (d : ℕ) :
    phaseZ (-((d : ℝ) * (π / 2))) = !![(-I) ^ d, 0; 0, I ^ d] := by
  have h1 : I * ((-((d : ℝ) * (π / 2)) : ℝ) : ℂ) = (d : ℂ) * (-(π : ℂ) / 2 * I) := by
    push_cast; ring
  have h2 : -(I * ((-((d : ℝ) * (π / 2)) : ℝ) : ℂ)) = (d : ℂ) * ((π : ℂ) / 2 * I) := by
    push_cast; ring
  rw [phaseZ, h2, h1, exp_nat_mul, exp_nat_mul, exp_pi_div_two_mul_I, exp_neg_pi_div_two_mul_I]

/-- A constant phase list gives a power: `seqR (replicate n φ) x = (e^{iφσ_z} R(x))^n`. -/
theorem seqR_replicate (n : ℕ) (φ x : ℝ) :
    seqR (List.replicate n φ) x = (phaseZ φ * Rref x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, seqR_cons, ih, pow_succ']

/-- `(rot x)^n = [[T_n(x), U_{n-1}(x) s], [-U_{n-1}(x) s, T_n(x)]]` for `x ∈ [-1, 1]`,
`s = √(1-x²)`. -/
theorem rot_pow {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (n : ℕ) :
    rot x ^ n =
      !![(Chebyshev.T ℂ n).eval (x : ℂ),
          (Chebyshev.U ℂ ((n : ℤ) - 1)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
        -((Chebyshev.U ℂ ((n : ℤ) - 1)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ)),
          (Chebyshev.T ℂ n).eval (x : ℂ)] := by
  have hs : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by
    have h : (0 : ℝ) ≤ 1 - x ^ 2 := by
      obtain ⟨h₁, h₂⟩ := hx
      nlinarith
    rw [← Complex.ofReal_pow, Real.sq_sqrt h]
    push_cast
    ring
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    have hT := congrArg (Polynomial.eval (x : ℂ))
      (Chebyshev.T_eq_X_mul_T_sub_pol_U ℂ ((n : ℤ) - 1))
    have hU := congrArg (Polynomial.eval (x : ℂ))
      (Chebyshev.U_eq_X_mul_U_add_T ℂ ((n : ℤ) - 1))
    rw [show (n : ℤ) - 1 + 2 = (n : ℤ) + 1 by ring, sub_add_cancel] at hT
    rw [sub_add_cancel] at hU
    simp only [eval_sub, eval_mul, eval_X, eval_one, eval_pow, eval_add] at hT hU
    rw [pow_succ', ih, rot]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -hT - (Chebyshev.U ℂ ((n : ℤ) - 1)).eval (x : ℂ) * hs
    · linear_combination -(Real.sqrt (1 - x ^ 2) : ℂ) * hU
    · linear_combination (Real.sqrt (1 - x ^ 2) : ℂ) * hU
    · linear_combination -hT - (Chebyshev.U ℂ ((n : ℤ) - 1)).eval (x : ℂ) * hs

/-! ### The closed form -/

/-- QSP-4 (GSLW Lemma 9, full matrix). For `x ∈ [-1, 1]` and `s = √(1-x²)`,
`seqR (chebPhases d) x = [[T_d(x), U_{d-1}(x) s], [(-1)^(d+1) U_{d-1}(x) s, (-1)^d T_d(x)]]`. -/
theorem seqR_chebPhases_eq {d : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    seqR (chebPhases d) x =
      !![(Chebyshev.T ℂ d).eval (x : ℂ),
          (Chebyshev.U ℂ ((d : ℤ) - 1)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
        (-1) ^ (d + 1) *
          ((Chebyshev.U ℂ ((d : ℤ) - 1)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ)),
          (-1) ^ d * (Chebyshev.T ℂ d).eval (x : ℂ)] := by
  cases d with
  | zero => simp [Matrix.one_fin_two]
  | succ n =>
    have hφ : (1 - ((n + 1 : ℕ) : ℝ)) * π / 2
        = -(((n + 1 : ℕ) : ℝ) * (π / 2)) + π / 2 := by ring
    have key : seqR (chebPhases (n + 1)) x
        = phaseZ (-(((n + 1 : ℕ) : ℝ) * (π / 2))) * (phaseZ (π / 2) * Rref x) ^ (n + 1) := by
      rw [chebPhases_succ, seqR_cons, seqR_replicate, hφ, ← phaseZ_mul_phaseZ]
      simp only [pow_succ', mul_assoc]
    rw [key, phaseZ_pi_div_two_mul_Rref, smul_pow, rot_pow hx, phaseZ_neg_nat_mul_pi_div_two]
    have h1 : (-I) ^ (n + 1) * I ^ (n + 1) = 1 := by
      rw [← mul_pow]
      simp
    have h2 : I ^ (n + 1) * I ^ (n + 1) = (-1) ^ (n + 1) := by
      rw [← mul_pow, I_mul_I]
    set T := (Chebyshev.T ℂ ((n : ℤ) + 1)).eval (x : ℂ) with hTdef
    set Us := (Chebyshev.U ℂ (n : ℤ)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ) with hUsdef
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination T * h1
    · linear_combination Us * h1
    · linear_combination -Us * h2
    · linear_combination T * h2

/-- QSP-4 (GSLW Lemma 9). The top-left entry of the QSP sequence with phases
`((1-d)π/2, π/2, …, π/2)` is the Chebyshev polynomial `T_d(x)`, for `x ∈ [-1, 1]`. -/
theorem seqR_chebPhases {d : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (seqR (chebPhases d) x) 0 0 = (Chebyshev.T ℂ d).eval (x : ℂ) := by
  rw [seqR_chebPhases_eq hx]
  simp

end QSVT.QSP
