/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Topology.Algebra.Polynomial
import QSVT.Polynomial.SqrtPart
import QSVT.QSP.Existence
import QSVT.SVT.RealPoly

/-!
# Complementary polynomials (formal-spec QSP-7a/7b/7d; GSLW Lemma 6, Theorem 5, Cor 10)

Everything in this file is fully proved (no `sorry`, standard axioms only).

**Main results.**

* `exists_sumsq_decomposition` (QSP-7a, GSLW Lemma 6): an even real polynomial `A` of degree
  `≤ 2k` with `A ≥ 0` on `[-1, 1]` is `A = B² + (1 - X²) C²` with real `B, C`, `deg B ≤ k`,
  `deg C ≤ k - 1` (`C = 0` if `k = 0`), `B` of parity `k`, `C` of parity `k - 1`.
* `exists_complement` (QSP-7b, GSLW Theorem 5, real version): a real `P̃` with `deg P̃ ≤ k`,
  parity `k` and `P̃(x)² ≤ 1` on `[-1, 1]` is the real part `Re[P] = P̃` of a pair `(P, Q)` over
  `ℂ` satisfying the hypotheses (i)–(iii) of `exists_phases` (`P := P̃ + i B`, `Q := C` with
  `(B, C)` from Lemma 6 applied to `A := 1 - P̃²`; `exists_complement_of_sumsq` is the assembly
  with the Lemma 6 data as hypotheses).
* `exists_phases_real`, `exists_phases_R_real` (QSP-7d, GSLW Cor 10): such a `P̃` is realised as
  `Re` of the QSP polynomial of a phase list of length `k`, in the rotation convention
  (`Re[(qspPolyW φ₀ Φ).1] = P̃`) and, for `k ≥ 1`, in the reflection convention
  (`Re (seqR Φ x)₀₀ = P̃(x)` on `[-1, 1]`).

**Proof of Lemma 6.** Instead of GSLW's global root factorisation (9), we peel off one
elementary factor at a time.  `SOSRep k A` records a representation `A = B² + (1 - X²) C²`
together with the degree and parity data in a product-friendly form (`deg (X C) ≤ k`, `X C` of
parity `k`).  It is closed under products by the Brahmagupta–Fibonacci identity
`(B₁² + w C₁²)(B₂² + w C₂²) = (B₁B₂ - w C₁C₂)² + w (B₁C₂ + B₂C₁)²` (`SOSRep.mul`) and under
`k ↦ k + 1` by multiplying with `1 = X² + (1 - X²)` (`SOSRep.succ`).  Given a complex root `s`
of `A` (`Complex.exists_root`), `A` is even and real, so `-s, s̄, -s̄` are roots too, and one of
three elementary factors `F` divides `A` over `ℝ` (`exists_factor_of_isRoot`):

* `s² ∉ ℝ`: the quartic `(X² - s²)(X² - s̄²) = X⁴ - 2 Re(s²) X² + |s²|²` (GSLW (12)),
  `SOSRep 2` with `B = α X² - |s²|`, `C = √(α² - 1) X`, `α = |s²| + |s² - 1| ≥ 1`
  (`sosRep_quartic`); it is positive on `ℝ`.
* `s² = v ∈ ℝ`, `v ∉ (0, 1)`: the quadratic `±(X² - v) = |1 - v| X² + |v| (1 - X²)`
  (GSLW (10), (11), and `X²` for `v = 0`), `SOSRep 1` with `B = √|1 - v| X`, `C = √|v|`
  (`sosRep_quad`); it is nonnegative on `[-1, 1]` and vanishes there only at `x ∈ {-1, 0, 1}`.
* `s² = r² ∈ (0, 1)`: `s = ±r` is a real root in `(-1, 1)`, hence a *double* root by
  nonnegativity (`X_sub_C_sq_dvd_of_nonneg`: a simple root would change the sign); the factor
  is `(X² - r²)² = B²` (`sosRep_sq`).

The cofactor `G = A / F` is even (`IsEven.of_mul_left`) and nonnegative on `[-1, 1]`: it is
nonnegative where `F > 0`, i.e. off a finite set, and extends by continuity
(`eval_nonneg_of_nonneg_off_finite`, via one-sided limits `𝓝[>] s`, `𝓝[<] s`).  Strong
induction on `k` (`sosRep_of_nonneg`) finishes: `deg G ≤ 2(k - j)` for a factor of degree `2j`.

Parity of real polynomials is expressed through the complexification
`HasParity (P.map (algebraMap ℝ ℂ)) k`, reusing `QSVT.Polynomial.Parity`; the new parity
lemmas `IsEven.mul`, `HasParity.mul`, `HasParity.of_X_mul`, `HasParity.of_X_mul_X_mul`,
`IsEven.of_mul_left`, `IsEven.eval_neg` are in `QSVT.Poly`.

## Mathlib facts used

`Complex.exists_root`, `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`,
`Polynomial.rootMultiplicity_pos`, `Polynomial.dvd_iff_isRoot`, `Polynomial.map_dvd_map`,
`Polynomial.isCoprime_X_sub_C_of_isUnit_sub`, `IsCoprime.mul_dvd`, `IsCoprime.pow`,
`Polynomial.monic_X_pow_sub_C`, `monicity!`, `compute_degree!`, `Polynomial.continuous`,
`ge_of_tendsto`, `tendsto_nhdsWithin_of_tendsto_nhds`, `Ioo_mem_nhdsGT`, `Ioo_mem_nhdsLT`,
`eventually_all_finite`, `eventually_ne_nhdsWithin`, `Complex.normSq_sub`, `Complex.sq_norm`,
`abs_norm_sub_norm_le`, `sq_lt_one_iff_abs_lt_one`, `eq_or_eq_neg_of_sq_eq_sq`.
-/

open Polynomial

namespace QSVT.Poly

/-! ### Parity under multiplication -/

/-- Even times even is even. -/
theorem IsEven.mul {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P * Q) := by
  obtain ⟨R, rfl⟩ := isEven_iff_exists_comp_X_sq.mp hP
  obtain ⟨S, rfl⟩ := isEven_iff_exists_comp_X_sq.mp hQ
  rw [← mul_comp]
  exact isEven_comp_X_sq _

/-- Even times odd is odd. -/
theorem IsEven.mul_isOdd {P Q : ℂ[X]} (hP : IsEven P) (hQ : IsOdd Q) : IsOdd (P * Q) := by
  obtain ⟨R, rfl⟩ := isEven_iff_exists_comp_X_sq.mp hP
  obtain ⟨S, rfl⟩ := isOdd_iff_exists_X_mul_comp_X_sq.mp hQ
  rw [show R.comp (X ^ 2) * (X * S.comp (X ^ 2)) = X * (R * S).comp (X ^ 2) by
    rw [mul_comp]; ring]
  exact isOdd_X_mul_comp_X_sq _

/-- Odd times even is odd. -/
theorem IsOdd.mul_isEven {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsEven Q) : IsOdd (P * Q) := by
  rw [mul_comm]
  exact hQ.mul_isOdd hP

/-- Odd times odd is even. -/
theorem IsOdd.mul {P Q : ℂ[X]} (hP : IsOdd P) (hQ : IsOdd Q) : IsEven (P * Q) := by
  obtain ⟨R, rfl⟩ := isOdd_iff_exists_X_mul_comp_X_sq.mp hP
  obtain ⟨S, rfl⟩ := isOdd_iff_exists_X_mul_comp_X_sq.mp hQ
  rw [show X * R.comp (X ^ 2) * (X * S.comp (X ^ 2)) = (X * (R * S)).comp (X ^ 2) by
    rw [mul_comp, mul_comp, X_comp]; ring]
  exact isEven_comp_X_sq _

/-- Parities add under multiplication. -/
theorem HasParity.mul {P Q : ℂ[X]} {m n : ℕ} (hP : HasParity P m) (hQ : HasParity Q n) :
    HasParity (P * Q) (m + n) := by
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn
  · exact ((hP.1 hm).mul (hQ.1 hn)).hasParity (hm.add hn)
  · exact ((hP.1 hm).mul_isOdd (hQ.2 hn)).hasParity (hm.add_odd hn)
  · exact ((hP.2 hm).mul_isEven (hQ.1 hn)).hasParity (hm.add_even hn)
  · exact ((hP.2 hm).mul (hQ.2 hn)).hasParity (hm.add_odd hn)

/-- Dividing by `X²` preserves the parity. -/
theorem HasParity.of_X_mul_X_mul {P : ℂ[X]} {n : ℕ} (h : HasParity (X * (X * P)) n) :
    HasParity P n := by
  refine ⟨fun hn k hk => ?_, fun hn k hk => ?_⟩
  · have := h.1 hn (k + 1 + 1) (by rw [add_assoc]; exact hk.add_even even_two)
    rwa [coeff_X_mul, coeff_X_mul] at this
  · have := h.2 hn (k + 1 + 1) (by rw [add_assoc]; exact hk.add even_two)
    rwa [coeff_X_mul, coeff_X_mul] at this

/-- Dividing by `X` shifts the parity down by one. -/
theorem HasParity.of_X_mul {P : ℂ[X]} {n : ℕ} (h : HasParity (X * P) (n + 1)) :
    HasParity P n := by
  refine ⟨fun hn k hk => ?_, fun hn k hk => ?_⟩
  · have := h.2 hn.add_one (k + 1) hk.add_one
    rwa [coeff_X_mul] at this
  · have := h.1 hn.add_one (k + 1) hk.add_one
    rwa [coeff_X_mul] at this

/-- A quotient of an even polynomial by a nonzero even polynomial is even. -/
theorem IsEven.of_mul_left {F G : ℂ[X]} (hF : IsEven F) (hF0 : F ≠ 0) (hFG : IsEven (F * G)) :
    IsEven G := by
  have hdecomp : F * evenPart G + F * oddPart G = F * G := by
    rw [← mul_add, evenPart_add_oddPart]
  have hodd : oddPart (F * G) = F * oddPart G :=
    oddPart_eq_of_add (hF.mul (isEven_evenPart G)) (hF.mul_isOdd (isOdd_oddPart G)) hdecomp
  have hzero : oddPart (F * G) = 0 := oddPart_eq_of_add hFG isOdd_zero (add_zero _)
  rw [hzero] at hodd
  have hG : oddPart G = 0 := (mul_eq_zero.mp hodd.symm).resolve_left hF0
  have h := evenPart_add_oddPart G
  rw [hG, add_zero] at h
  rw [← h]
  exact isEven_evenPart G

/-- An even polynomial takes the same value at `z` and `-z`. -/
theorem IsEven.eval_neg {P : ℂ[X]} (hP : IsEven P) (z : ℂ) : P.eval (-z) = P.eval z := by
  rw [hP.eval_eq, hP.eval_eq, neg_sq]

end QSVT.Poly

namespace QSVT.QSP

open QSVT.Poly Complex

/-! ### Real polynomials viewed over `ℂ` -/

/-- A real polynomial viewed in `ℂ[X]` has real coefficients: `(map P)^* = map P`. -/
theorem conjP_map_algebraMap (P : ℝ[X]) :
    conjP (P.map (algebraMap ℝ ℂ)) = P.map (algebraMap ℝ ℂ) := by
  ext k
  rw [coeff_conjP, coeff_map, Complex.coe_algebraMap, Complex.conj_ofReal]

/-- Evaluating the complexification at a real point. -/
theorem eval_map_algebraMap_ofReal (P : ℝ[X]) (x : ℝ) :
    (P.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  change (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = algebraMap ℝ ℂ (P.eval x)
  rw [eval_map, eval₂_at_apply]

theorem natDegree_le_natDegree_X_mul (P : ℝ[X]) : P.natDegree ≤ (X * P).natDegree := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · rw [natDegree_X_mul hP]
    omega

/-! ### Weighted sum-of-squares representations -/

/-- QSP-7a. `SOSRep k A`: the real polynomial `A` is `B² + (1 - X²) C²` with real `B, C`,
`deg B ≤ k`, `deg (X C) ≤ k` (i.e. `deg C ≤ k - 1`, and `C = 0` if `k = 0`), `B` of parity `k` and
`X C` of parity `k` (i.e. `C` of parity `k - 1`).  This is the conclusion of GSLW Lemma 6 in a form
that is stable under products (`SOSRep.mul`) and under `k ↦ k + 1` (`SOSRep.succ`). -/
def SOSRep (k : ℕ) (A : ℝ[X]) : Prop :=
  ∃ B C : ℝ[X], A = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧ B.natDegree ≤ k ∧ (X * C).natDegree ≤ k ∧
    HasParity (B.map (algebraMap ℝ ℂ)) k ∧ HasParity (X * C.map (algebraMap ℝ ℂ)) k

/-- QSP-7a. The Brahmagupta–Fibonacci identity with weight `w`:
`(B₁² + w C₁²)(B₂² + w C₂²) = (B₁B₂ - w C₁C₂)² + w (B₁C₂ + B₂C₁)²`. -/
theorem sumsq_mul_sumsq {R : Type*} [CommRing R] (w B₁ C₁ B₂ C₂ : R) :
    (B₁ ^ 2 + w * C₁ ^ 2) * (B₂ ^ 2 + w * C₂ ^ 2) =
      (B₁ * B₂ - w * (C₁ * C₂)) ^ 2 + w * (B₁ * C₂ + B₂ * C₁) ^ 2 := by
  ring

/-- QSP-7a. Products of representable polynomials are representable, with the degree bounds and
parities adding up. -/
theorem SOSRep.mul {k₁ k₂ : ℕ} {A₁ A₂ : ℝ[X]} (h₁ : SOSRep k₁ A₁) (h₂ : SOSRep k₂ A₂) :
    SOSRep (k₁ + k₂) (A₁ * A₂) := by
  obtain ⟨B₁, C₁, rfl, hB₁, hC₁, pB₁, pC₁⟩ := h₁
  obtain ⟨B₂, C₂, rfl, hB₂, hC₂, pB₂, pC₂⟩ := h₂
  refine ⟨B₁ * B₂ - (1 - X ^ 2) * (C₁ * C₂), B₁ * C₂ + B₂ * C₁, sumsq_mul_sumsq _ _ _ _ _,
    ?_, ?_, ?_, ?_⟩
  · have h1 : ((1 - X ^ 2) * (C₁ * C₂)).natDegree ≤ k₁ + k₂ := by
      rw [show (1 - X ^ 2) * (C₁ * C₂) = C₁ * C₂ - (X * C₁) * (X * C₂) by ring]
      refine (natDegree_sub_le _ _).trans (max_le ?_ (natDegree_mul_le_of_le hC₁ hC₂))
      exact natDegree_mul_le_of_le ((natDegree_le_natDegree_X_mul C₁).trans hC₁)
        ((natDegree_le_natDegree_X_mul C₂).trans hC₂)
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le_of_le hB₁ hB₂) h1)
  · rw [show X * (B₁ * C₂ + B₂ * C₁) = B₁ * (X * C₂) + B₂ * (X * C₁) by ring]
    exact natDegree_add_le_of_degree_le (natDegree_mul_le_of_le hB₁ hC₂)
      ((natDegree_mul_le_of_le hB₂ hC₁).trans (by omega))
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X]
    refine (pB₁.mul pB₂).sub (HasParity.one_sub_X_sq_mul (HasParity.of_X_mul_X_mul ?_))
    rw [show X * (X * (C₁.map (algebraMap ℝ ℂ) * C₂.map (algebraMap ℝ ℂ))) =
      (X * C₁.map (algebraMap ℝ ℂ)) * (X * C₂.map (algebraMap ℝ ℂ)) by ring]
    exact pC₁.mul pC₂
  · simp only [Polynomial.map_add, Polynomial.map_mul]
    rw [show X * (B₁.map (algebraMap ℝ ℂ) * C₂.map (algebraMap ℝ ℂ) +
        B₂.map (algebraMap ℝ ℂ) * C₁.map (algebraMap ℝ ℂ)) =
      B₁.map (algebraMap ℝ ℂ) * (X * C₂.map (algebraMap ℝ ℂ)) +
        B₂.map (algebraMap ℝ ℂ) * (X * C₁.map (algebraMap ℝ ℂ)) by ring]
    refine (pB₁.mul pC₂).add ?_
    rw [Nat.add_comm k₁ k₂]
    exact pB₂.mul pC₁

/-- QSP-7a. A `k`-representation is also a `(k + 1)`-representation (multiply by
`1 = X² + (1 - X²)`): `(B, C) ↦ (X B - (1 - X²) C, B + X C)`. -/
theorem SOSRep.succ {k : ℕ} {A : ℝ[X]} (h : SOSRep k A) : SOSRep (k + 1) A := by
  obtain ⟨B, C, rfl, hB, hC, pB, pC⟩ := h
  refine ⟨X * B - (1 - X ^ 2) * C, B + X * C, by ring, ?_, ?_, ?_, ?_⟩
  · rw [show X * B - (1 - X ^ 2) * C = X * B - C + X * (X * C) by ring]
    refine natDegree_add_le_of_degree_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_
    · exact (natDegree_mul_le_of_le natDegree_X_le hB).trans (by omega)
    · exact ((natDegree_le_natDegree_X_mul C).trans hC).trans (by omega)
    · exact (natDegree_mul_le_of_le natDegree_X_le hC).trans (by omega)
  · rw [show X * (B + X * C) = X * B + X * (X * C) by ring]
    exact natDegree_add_le_of_degree_le ((natDegree_mul_le_of_le natDegree_X_le hB).trans
      (by omega)) ((natDegree_mul_le_of_le natDegree_X_le hC).trans (by omega))
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X]
    exact pB.X_mul.sub (HasParity.one_sub_X_sq_mul (HasParity.of_X_mul_X_mul pC.X_mul))
  · simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X]
    rw [mul_add]
    exact pB.X_mul.add pC.X_mul

/-! ### Elementary factors (GSLW eqs. (10)–(12)) -/

/-- QSP-7a. A nonnegative constant is a `0`-representation (`B = √a`, `C = 0`). -/
theorem sosRep_C_of_nonneg {a : ℝ} (ha : 0 ≤ a) : SOSRep 0 (C a) := by
  refine ⟨C (Real.sqrt a), 0, ?_, (natDegree_C _).le, by simp, ?_, ?_⟩
  · rw [← C_pow, Real.sq_sqrt ha]
    ring
  · rw [Polynomial.map_C]
    exact hasParity_C _
  · rw [Polynomial.map_zero, mul_zero]
    exact hasParity_zero _

/-- QSP-7a. The quadratic factor `|1 - v| X² + |v| (1 - X²)`, which equals `X² - v` for `v ≤ 0`
and `v - X²` for `v ≥ 1` (GSLW eqs. (10), (11)): `B = √|1 - v| X`, `C = √|v|`. -/
theorem sosRep_quad (v : ℝ) : SOSRep 1 (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)) := by
  refine ⟨C (Real.sqrt |1 - v|) * X, C (Real.sqrt |v|), ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_pow, ← C_pow, Real.sq_sqrt (abs_nonneg _), ← C_pow, Real.sq_sqrt (abs_nonneg _)]
    ring
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · compute_degree
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    exact hasParity_X.C_mul _
  · rw [Polynomial.map_C]
    exact (hasParity_C _).X_mul

/-- QSP-7a. The square `(X² - r)²` is a `2`-representation (`B = X² - r`, `C = 0`); used for the
double roots `±√r` in `(-1, 1)`. -/
theorem sosRep_sq (r : ℝ) : SOSRep 2 ((X ^ 2 - C r) ^ 2) := by
  refine ⟨X ^ 2 - C r, 0, by ring, by compute_degree, by simp, ?_, ?_⟩
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, sq]
    exact hasParity_X.X_mul.sub (hasParity_C _).add_two
  · rw [Polynomial.map_zero, mul_zero]
    exact hasParity_zero _

/-- QSP-7a. The real quartic `(X² - a)(X² - ā) = X⁴ - 2 Re(a) X² + |a|²` attached to a complex
number `a` (GSLW eq. (12), with `a = s²`). -/
noncomputable def quartic (a : ℂ) : ℝ[X] :=
  X ^ 4 - C (2 * a.re) * X ^ 2 + C (Complex.normSq a)

/-- Over `ℂ`, `quartic a = (X² - a)(X² - ā)`. -/
theorem quartic_map (a : ℂ) :
    (quartic a).map (algebraMap ℝ ℂ) = (X ^ 2 - C a) * (X ^ 2 - C ((starRingEnd ℂ) a)) := by
  simp only [quartic, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Complex.coe_algebraMap]
  rw [← Complex.add_conj, ← Complex.mul_conj, C_add, C_mul]
  ring

/-- `quartic a` evaluates to `(x² - Re a)² + (Im a)²` at a real `x`. -/
theorem eval_quartic (a : ℂ) (x : ℝ) :
    (quartic a).eval x = (x ^ 2 - a.re) ^ 2 + a.im ^ 2 := by
  simp only [quartic, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Complex.normSq_apply]
  ring

/-- QSP-7a. The quartic factor is a `2`-representation (GSLW eq. (12)): with `m = |a|`,
`n = |a - 1|`, `α = m + n ≥ 1`, `B = α X² - m` and `C = √(α² - 1) X`. -/
theorem sosRep_quartic (a : ℂ) : SOSRep 2 (quartic a) := by
  set m := ‖a‖ with hm
  set n := ‖a - 1‖ with hn
  have hn2 : n ^ 2 = m ^ 2 + 1 - 2 * a.re := by
    rw [hn, hm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, map_one,
      mul_one]
  have h1 : 1 ≤ m + n := by
    have h := abs_norm_sub_norm_le a 1
    rw [norm_one, ← hm, ← hn] at h
    linarith [neg_abs_le (m - 1)]
  have hγ : Real.sqrt ((m + n) ^ 2 - 1) ^ 2 = (m + n) ^ 2 - 1 :=
    Real.sq_sqrt (by nlinarith)
  refine ⟨C (m + n) * X ^ 2 - C m, C (Real.sqrt ((m + n) ^ 2 - 1)) * X, ?_, by compute_degree,
    by compute_degree, ?_, ?_⟩
  · have hγ' : (C (Real.sqrt ((m + n) ^ 2 - 1)) : ℝ[X]) ^ 2 = (C m + C n) ^ 2 - 1 := by
      rw [← C_pow, hγ, C_sub, C_pow, C_add, C_1]
    have hn' : (C n : ℝ[X]) ^ 2 = C m ^ 2 + 1 - C 2 * C a.re := by
      rw [← C_pow, hn2, C_sub, C_add, C_pow, C_1, C_mul]
    rw [quartic, Complex.normSq_eq_norm_sq, ← hm, C_pow, C_add, C_mul]
    linear_combination (X ^ 4 - X ^ 2) * hγ' - X ^ 2 * hn'
  · rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, sq]
    exact (hasParity_X.X_mul.C_mul _).sub (hasParity_C _).add_two
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      show X * (C ((algebraMap ℝ ℂ) (Real.sqrt ((m + n) ^ 2 - 1))) * X) =
        C ((algebraMap ℝ ℂ) (Real.sqrt ((m + n) ^ 2 - 1))) * (X * X) by ring]
    exact hasParity_X.X_mul.C_mul _

/-! ### One-sided limits and nonnegativity off a finite set -/

open Topology Filter

/-- If `0 ≤ D` eventually to the right of `s`, then `0 ≤ D(s)`. -/
theorem eval_nonneg_of_eventually_nhdsGT (D : ℝ[X]) (s : ℝ)
    (h : ∀ᶠ x in 𝓝[>] s, 0 ≤ D.eval x) : 0 ≤ D.eval s :=
  ge_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds (D.continuous.tendsto s)) h

/-- If `0 ≤ D` eventually to the left of `s`, then `0 ≤ D(s)`. -/
theorem eval_nonneg_of_eventually_nhdsLT (D : ℝ[X]) (s : ℝ)
    (h : ∀ᶠ x in 𝓝[<] s, 0 ≤ D.eval x) : 0 ≤ D.eval s :=
  ge_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds (D.continuous.tendsto s)) h

/-- QSP-7a. A polynomial nonnegative on `[-1, 1]` off a finite set is nonnegative on all of
`[-1, 1]` (by continuity). -/
theorem eval_nonneg_of_nonneg_off_finite (D : ℝ[X]) {S : Set ℝ} (hS : S.Finite)
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ S → 0 ≤ D.eval x) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ D.eval x := by
  intro s hs
  by_cases hsS : s ∈ S
  · have hS' : ∀ᶠ x in 𝓝[≠] s, x ∉ S := by
      have : ∀ᶠ x in 𝓝[≠] s, ∀ t ∈ S, x ≠ t := by
        rw [eventually_all_finite hS]
        intro t ht
        rcases eq_or_ne s t with rfl | hst
        · exact eventually_mem_nhdsWithin.mono fun x hx => hx
        · exact eventually_ne_nhdsWithin hst
      exact this.mono fun x hx hxS => hx x hxS rfl
    rcases lt_or_eq_of_le hs.2 with hs1 | hs1
    · apply eval_nonneg_of_eventually_nhdsGT
      have h2 : ∀ᶠ x in 𝓝[>] s, x ∉ S :=
        hS'.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
      filter_upwards [Ioo_mem_nhdsGT hs1, h2] with x hx1 hx2
      exact h x ⟨by linarith [hs.1, hx1.1], hx1.2.le⟩ hx2
    · apply eval_nonneg_of_eventually_nhdsLT
      have h2 : ∀ᶠ x in 𝓝[<] s, x ∉ S :=
        hS'.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
      filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < s by linarith), h2] with x hx1 hx2
      exact h x ⟨hx1.1.le, by linarith [hx1.2]⟩ hx2
  · exact h s hs hsS

/-- QSP-7a. If `F G ≥ 0` on `[-1, 1]` and `F > 0` there off a finite set, then `G ≥ 0` on
`[-1, 1]`. -/
theorem eval_nonneg_of_mul_nonneg {F G : ℝ[X]} {S : Set ℝ} (hS : S.Finite)
    (hF : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ S → 0 < F.eval x)
    (hFG : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (F * G).eval x) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ G.eval x :=
  eval_nonneg_of_nonneg_off_finite G hS fun x hx hxS => by
    have h := hFG x hx
    rw [eval_mul] at h
    exact nonneg_of_mul_nonneg_right h (hF x hx hxS)

/-- QSP-7a. A root `r ∈ (-1, 1)` of a polynomial nonnegative on `[-1, 1]` is at least a double
root: `(X - r)² ∣ A`.  (If the multiplicity were `1`, `A = (X - r) D` with `D(r) ≠ 0` would change
sign at `r`.) -/
theorem X_sub_C_sq_dvd_of_nonneg {A : ℝ[X]} (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x)
    {r : ℝ} (hr : r ∈ Set.Ioo (-1 : ℝ) 1) (hroot : A.IsRoot r) : (X - C r) ^ 2 ∣ A := by
  rcases eq_or_ne A 0 with rfl | hA0
  · exact dvd_zero _
  obtain ⟨D, hD, hDr⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd A hA0 r
  rw [dvd_iff_isRoot] at hDr
  have hm : 0 < rootMultiplicity r A := (rootMultiplicity_pos hA0).mpr hroot
  rcases Nat.lt_or_ge (rootMultiplicity r A) 2 with h2 | h2
  · exfalso
    have hm1 : rootMultiplicity r A = 1 := by omega
    rw [hm1, pow_one] at hD
    have key : ∀ x, A.eval x = (x - r) * D.eval x := fun x => by
      rw [hD, eval_mul, eval_sub, eval_X, eval_C]
    have hpos : 0 ≤ D.eval r := by
      apply eval_nonneg_of_eventually_nhdsGT
      filter_upwards [Ioo_mem_nhdsGT hr.2] with x hx
      have h := hA x ⟨by linarith [hr.1, hx.1], hx.2.le⟩
      rw [key] at h
      exact nonneg_of_mul_nonneg_right h (by linarith [hx.1])
    have hneg : 0 ≤ (-D).eval r := by
      apply eval_nonneg_of_eventually_nhdsLT
      filter_upwards [Ioo_mem_nhdsLT hr.1] with x hx
      have h := hA x ⟨hx.1.le, by linarith [hx.2, hr.2]⟩
      rw [key, show (x - r) * D.eval x = (r - x) * (-D).eval x by rw [eval_neg]; ring] at h
      exact nonneg_of_mul_nonneg_right h (by linarith [hx.2])
    rw [eval_neg] at hneg
    exact hDr (IsRoot.def.mpr (le_antisymm (by linarith) hpos))
  · exact (pow_dvd_pow _ h2).trans (Dvd.intro D hD.symm)

/-! ### Root pairing (GSLW Lemma 6, eqs. (9)–(12)) -/

/-- Two distinct roots `s ≠ -s` of `P` give `X² - s² ∣ P`. -/
theorem X_sq_sub_C_dvd_of_isRoot {P : ℂ[X]} {s : ℂ} (hs0 : s ≠ 0) (h1 : P.IsRoot s)
    (h2 : P.IsRoot (-s)) : X ^ 2 - C (s ^ 2) ∣ P := by
  have hcop : IsCoprime (X - C s) (X - C (-s)) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [sub_neg_eq_add]
    exact isUnit_iff_ne_zero.mpr fun h => hs0 (by linear_combination h / 2)
  have h := hcop.mul_dvd (dvd_iff_isRoot.mpr h1) (dvd_iff_isRoot.mpr h2)
  rwa [show (X - C s) * (X - C (-s)) = X ^ 2 - C (s ^ 2) by rw [C_neg, C_pow]; ring] at h

/-- The complexification of an even real polynomial has the root `-s` with every root `s`. -/
theorem isRoot_neg_of_isEven {A : ℝ[X]} (hAe : IsEven (A.map (algebraMap ℝ ℂ))) {s : ℂ}
    (hs : (A.map (algebraMap ℝ ℂ)).IsRoot s) : (A.map (algebraMap ℝ ℂ)).IsRoot (-s) := by
  rw [IsRoot.def, hAe.eval_neg]
  exact hs.eq_zero

/-- The complexification of a real polynomial has the root `conj s` with every root `s`. -/
theorem isRoot_conj_of_map {A : ℝ[X]} {s : ℂ} (hs : (A.map (algebraMap ℝ ℂ)).IsRoot s) :
    (A.map (algebraMap ℝ ℂ)).IsRoot ((starRingEnd ℂ) s) := by
  have h := eval_conjP (A.map (algebraMap ℝ ℂ)) ((starRingEnd ℂ) s)
  rw [conjP_map_algebraMap, Complex.conj_conj] at h
  rw [IsRoot.def, h, hs.eq_zero, map_zero]

/-- Properties of the cofactor `G` in `A = F G`: degree, evenness, nonnegativity on `[-1, 1]`
(the last one needs `F > 0` on `[-1, 1]` off a finite set). -/
theorem cofactor_props {A F G : ℝ[X]} (hAe : IsEven (A.map (algebraMap ℝ ℂ))) (hA0 : A ≠ 0)
    (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) (hFe : IsEven (F.map (algebraMap ℝ ℂ)))
    (hAFG : A = F * G) {S : Set ℝ} (hS : S.Finite)
    (hF : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ S → 0 < F.eval x) :
    G.natDegree + F.natDegree = A.natDegree ∧ IsEven (G.map (algebraMap ℝ ℂ)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ G.eval x := by
  have hF0 : F ≠ 0 := fun h => hA0 (by rw [hAFG, h, zero_mul])
  have hG0 : G ≠ 0 := fun h => hA0 (by rw [hAFG, h, mul_zero])
  refine ⟨by rw [hAFG, natDegree_mul hF0 hG0, add_comm], ?_, ?_⟩
  · refine hFe.of_mul_left ((Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hF0) ?_
    rw [← Polynomial.map_mul, ← hAFG]
    exact hAe
  · exact eval_nonneg_of_mul_nonneg hS hF fun x hx => by rw [← hAFG]; exact hA x hx

/-- QSP-7a. The root-pairing step of GSLW Lemma 6.  A nonzero even real polynomial `A ≥ 0` on
`[-1, 1]` with a complex root `s` factors as `A = F G`, where `F` is one of the elementary factors
(GSLW eqs. (10)–(12), or the square `(X² - s²)²` for a real root `s ∈ (-1, 1)`), a
`j`-representation of degree `2j` (`j ∈ {1, 2}`), and `G` is again even and nonnegative on
`[-1, 1]`. -/
theorem exists_factor_of_isRoot {A : ℝ[X]} (hAe : IsEven (A.map (algebraMap ℝ ℂ))) (hA0 : A ≠ 0)
    (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) {s : ℂ}
    (hs : (A.map (algebraMap ℝ ℂ)).IsRoot s) :
    ∃ j : ℕ, ∃ F G : ℝ[X], 0 < j ∧ SOSRep j F ∧ A = F * G ∧
      G.natDegree + 2 * j ≤ A.natDegree ∧ IsEven (G.map (algebraMap ℝ ℂ)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ G.eval x := by
  have hinj := (algebraMap ℝ ℂ).injective
  have hs' : (A.map (algebraMap ℝ ℂ)).IsRoot (-s) := isRoot_neg_of_isEven hAe hs
  by_cases him : (s ^ 2).im = 0
  · -- `s²` is real
    set v := (s ^ 2).re with hv
    have hsv : s ^ 2 = (v : ℂ) := Complex.ext (by simp [hv]) (by simp [him])
    by_cases hv01 : 0 < v ∧ v < 1
    · -- Case I: `s = ±r` real with `0 < r² < 1`: double roots `±r`, factor `(X² - r²)²`
      have hsim : s.im = 0 := by
        have h2 : s.re * s.im = 0 := by
          have h := him
          rw [sq, Complex.mul_im] at h
          linarith
        rcases mul_eq_zero.mp h2 with h | h
        · exfalso
          have hv' : v = -(s.im ^ 2) := by
            rw [hv, sq, Complex.mul_re, h]
            ring
          nlinarith [hv01.1, sq_nonneg s.im]
        · exact h
      set r := s.re with hr
      have hsr : s = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hsim])
      have hr2 : r ^ 2 = v := by
        have h := congrArg Complex.re hsv
        rw [hsr, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re] at h
        exact h
      have hrI : r ∈ Set.Ioo (-1 : ℝ) 1 := by
        rw [Set.mem_Ioo, ← abs_lt, ← sq_lt_one_iff_abs_lt_one, hr2]
        exact hv01.2
      have hr0 : r ≠ 0 := by
        intro h
        rw [h, zero_pow two_ne_zero] at hr2
        linarith [hv01.1]
      have hrootr : A.IsRoot r := by
        have h := hs.eq_zero
        rw [hsr, eval_map_algebraMap_ofReal, Complex.ofReal_eq_zero] at h
        exact h
      have hrootr' : A.IsRoot (-r) := by
        have h := hs'.eq_zero
        rw [hsr, ← Complex.ofReal_neg, eval_map_algebraMap_ofReal, Complex.ofReal_eq_zero] at h
        exact h
      have hd1 := X_sub_C_sq_dvd_of_nonneg hA hrI hrootr
      have hd2 := X_sub_C_sq_dvd_of_nonneg hA
        (by rw [Set.mem_Ioo] at hrI ⊢; constructor <;> linarith [hrI.1, hrI.2]) hrootr'
      have hcop : IsCoprime ((X - C r) ^ 2) ((X - C (-r)) ^ 2) := by
        refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub ?_)
        rw [sub_neg_eq_add]
        exact isUnit_iff_ne_zero.mpr fun h => hr0 (by linarith)
      obtain ⟨G, hG⟩ := hcop.mul_dvd hd1 hd2
      rw [show (X - C r) ^ 2 * (X - C (-r)) ^ 2 = (X ^ 2 - C (r ^ 2)) ^ 2 by
        rw [C_neg, C_pow]; ring] at hG
      have hFe : IsEven (((X ^ 2 - C (r ^ 2)) ^ 2).map (algebraMap ℝ ℂ)) := by
        rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C]
        exact isEven_iff_exists_comp_X_sq.mpr
          ⟨(X - C ((algebraMap ℝ ℂ) (r ^ 2))) ^ 2, by rw [pow_comp, sub_comp, X_comp, C_comp]⟩
      have hFpos : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ ({r, -r} : Set ℝ) →
          0 < ((X ^ 2 - C (r ^ 2)) ^ 2).eval x := by
        intro x _ hxS
        simp only [eval_pow, eval_sub, eval_X, eval_C]
        have hne : x ^ 2 - r ^ 2 ≠ 0 := by
          intro h
          rcases eq_or_eq_neg_of_sq_eq_sq x r (by linarith) with h | h <;> simp [h] at hxS
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      obtain ⟨hdeg, hGe, hGnn⟩ := cofactor_props hAe hA0 hA hFe hG (Set.toFinite _) hFpos
      refine ⟨2, _, G, two_pos, sosRep_sq _, hG, ?_, hGe, hGnn⟩
      have h4 : ((X ^ 2 - C (r ^ 2)) ^ 2 : ℝ[X]).natDegree = 4 := by compute_degree!
      omega
    · -- Case II: `v = s² ≤ 0` or `v ≥ 1`: the quadratic factor `±(X² - v)` (GSLW (10), (11))
      have hv' : v ≤ 0 ∨ 1 ≤ v := by
        rcases le_or_gt v 0 with h | h
        · exact Or.inl h
        · exact Or.inr (le_of_not_gt fun h1 => hv01 ⟨h, h1⟩)
      have hdvd : X ^ 2 - C v ∣ A := by
        rcases eq_or_ne s 0 with hs0 | hs0
        · have hv0 : v = 0 := by rw [hv, hs0, zero_pow two_ne_zero, Complex.zero_re]
          have h0 : A.IsRoot 0 := by
            have h := hs.eq_zero
            rw [hs0, ← Complex.ofReal_zero, eval_map_algebraMap_ofReal] at h
            exact IsRoot.def.mpr (by exact_mod_cast h)
          have h := X_sub_C_sq_dvd_of_nonneg hA (by norm_num) h0
          rw [C_0, sub_zero] at h
          rw [hv0, C_0, sub_zero]
          exact h
        · have h := X_sq_sub_C_dvd_of_isRoot hs0 hs hs'
          have hmap : (X ^ 2 - C v).map (algebraMap ℝ ℂ) = X ^ 2 - C (v : ℂ) := by
            rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
              Complex.coe_algebraMap]
          rw [hsv, ← hmap] at h
          exact (map_dvd_map _ hinj (monic_X_pow_sub_C v two_ne_zero)).mp h
      obtain ⟨G₀, hG₀⟩ := hdvd
      obtain ⟨ε, hε1, hFε⟩ : ∃ ε : ℝ, ε * ε = 1 ∧
          C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2) = C ε * (X ^ 2 - C v) := by
        rcases hv' with hv0 | hv1
        · refine ⟨1, one_mul 1, ?_⟩
          rw [abs_of_nonneg (by linarith), abs_of_nonpos hv0, C_sub, C_1, C_neg]
          ring
        · refine ⟨-1, by norm_num, ?_⟩
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          simp only [C_neg, C_sub, C_1]
          ring
      have hAFG : A = (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)) * (C ε * G₀) := by
        rw [hFε, hG₀]
        have hεε : (C ε : ℝ[X]) * C ε = 1 := by rw [← C_mul, hε1, C_1]
        linear_combination (-(X ^ 2 - C v) * G₀) * hεε
      have hFe : IsEven ((C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)).map (algebraMap ℝ ℂ)) := by
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
          Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
        exact isEven_iff_exists_comp_X_sq.mpr
          ⟨C ((algebraMap ℝ ℂ) |1 - v|) * X + C ((algebraMap ℝ ℂ) |v|) * (1 - X), by
            simp only [add_comp, mul_comp, C_comp, X_comp, sub_comp, one_comp]⟩
      have hFpos : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ ({-1, 0, 1} : Set ℝ) →
          0 < (C |1 - v| * X ^ 2 + C |v| * (1 - X ^ 2)).eval x := by
        intro x hx hxS
        simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
        have h1 : 0 ≤ |1 - v| * x ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
        have h2 : 0 ≤ |v| * (1 - x ^ 2) :=
          mul_nonneg (abs_nonneg _) (by nlinarith [hx.1, hx.2])
        rcases h1.lt_or_eq with h1 | h1
        · linarith
        rcases h2.lt_or_eq with h2 | h2
        · linarith
        exfalso
        rcases mul_eq_zero.mp h1.symm with ha | hx0
        · have hv1 : v = 1 := by
            have := abs_eq_zero.mp ha
            linarith
          rcases mul_eq_zero.mp h2.symm with hb | hx1
          · rw [abs_eq_zero] at hb
            linarith
          · rcases eq_or_eq_neg_of_sq_eq_sq x 1 (by linarith) with h | h <;> simp [h] at hxS
        · have hx0' : x = 0 := pow_eq_zero_iff two_ne_zero |>.mp hx0
          simp [hx0'] at hxS
      obtain ⟨-, hGe, hGnn⟩ := cofactor_props hAe hA0 hA hFe hAFG (Set.toFinite _) hFpos
      refine ⟨1, _, C ε * G₀, one_pos, sosRep_quad v, hAFG, ?_, hGe, hGnn⟩
      have hG₀0 : G₀ ≠ 0 := fun h => hA0 (by rw [hG₀, h, mul_zero])
      have h1 : A.natDegree = 2 + G₀.natDegree := by
        rw [hG₀, natDegree_mul (monic_X_pow_sub_C v two_ne_zero).ne_zero hG₀0,
          natDegree_X_pow_sub_C]
      have h2 := natDegree_C_mul_le ε G₀
      omega
  · -- Case III: `s²` is not real: the quartic factor `(X² - s²)(X² - s̄²)` (GSLW (12))
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact him (by rw [zero_pow two_ne_zero, Complex.zero_im])
    have hsc : (A.map (algebraMap ℝ ℂ)).IsRoot ((starRingEnd ℂ) s) := isRoot_conj_of_map hs
    have hsc' : (A.map (algebraMap ℝ ℂ)).IsRoot (-(starRingEnd ℂ) s) :=
      isRoot_neg_of_isEven hAe hsc
    have hd1 : X ^ 2 - C (s ^ 2) ∣ A.map (algebraMap ℝ ℂ) := X_sq_sub_C_dvd_of_isRoot hs0 hs hs'
    have hd2 : X ^ 2 - C ((starRingEnd ℂ) (s ^ 2)) ∣ A.map (algebraMap ℝ ℂ) := by
      have h := X_sq_sub_C_dvd_of_isRoot
        ((map_ne_zero_iff _ (RingHom.injective _)).mpr hs0) hsc hsc'
      rwa [← map_pow] at h
    have hne : (starRingEnd ℂ) (s ^ 2) - s ^ 2 ≠ 0 := by
      intro h
      exact him (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h))
    have hcop : IsCoprime (X ^ 2 - C (s ^ 2)) (X ^ 2 - C ((starRingEnd ℂ) (s ^ 2))) := by
      refine ⟨C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹, -C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹, ?_⟩
      rw [show C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹ * (X ^ 2 - C (s ^ 2)) +
          -C ((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹ * (X ^ 2 - C ((starRingEnd ℂ) (s ^ 2))) =
          C (((starRingEnd ℂ) (s ^ 2) - s ^ 2)⁻¹ * ((starRingEnd ℂ) (s ^ 2) - s ^ 2)) by
        rw [C_mul, C_sub]; ring]
      rw [inv_mul_cancel₀ hne, C_1]
    have hmonic : (quartic (s ^ 2)).Monic := by
      unfold quartic
      monicity!
    obtain ⟨G, hG⟩ : quartic (s ^ 2) ∣ A := by
      have h := hcop.mul_dvd hd1 hd2
      rw [← quartic_map] at h
      exact (map_dvd_map _ hinj hmonic).mp h
    have hFe : IsEven ((quartic (s ^ 2)).map (algebraMap ℝ ℂ)) := by
      rw [quartic_map]
      exact isEven_iff_exists_comp_X_sq.mpr
        ⟨(X - C (s ^ 2)) * (X - C ((starRingEnd ℂ) (s ^ 2))), by
          simp only [mul_comp, sub_comp, X_comp, C_comp]⟩
    have hFpos : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ∉ (∅ : Set ℝ) → 0 < (quartic (s ^ 2)).eval x := by
      intro x _ _
      rw [eval_quartic]
      have h := lt_of_le_of_ne (sq_nonneg (s ^ 2).im) (Ne.symm (pow_ne_zero 2 him))
      nlinarith [sq_nonneg (x ^ 2 - (s ^ 2).re)]
    obtain ⟨hdeg, hGe, hGnn⟩ := cofactor_props hAe hA0 hA hFe hG Set.finite_empty hFpos
    refine ⟨2, _, G, two_pos, sosRep_quartic _, hG, ?_, hGe, hGnn⟩
    have h4 : (quartic (s ^ 2)).natDegree = 4 := by
      unfold quartic
      compute_degree!
    omega

/-! ### GSLW Lemma 6 -/

/-- QSP-7a (GSLW Lemma 6, representation form).  An even real polynomial `A` of degree `≤ 2k`
with `A ≥ 0` on `[-1, 1]` has a weighted sum-of-squares representation `SOSRep k A`, i.e.
`A = B² + (1 - X²) C²` with `deg B ≤ k`, `deg C ≤ k - 1`, `B` of parity `k` and `C` of parity
`k - 1`.  Proof: strong induction on `k`, peeling off one elementary factor at a time
(`exists_factor_of_isRoot`) and multiplying the representations (`SOSRep.mul`); if the degree
drops below `2k`, lift with `SOSRep.succ`. -/
theorem sosRep_of_nonneg (k : ℕ) :
    ∀ A : ℝ[X], IsEven (A.map (algebraMap ℝ ℂ)) → A.natDegree ≤ 2 * k →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) → SOSRep k A := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A hAe hAd hA
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hAd0 : A.natDegree ≤ 0 := by simpa using hAd
    rw [eq_C_of_natDegree_le_zero hAd0]
    apply sosRep_C_of_nonneg
    rw [coeff_zero_eq_eval_zero]
    exact hA 0 ⟨by norm_num, by norm_num⟩
  · by_cases hlow : A.natDegree ≤ 2 * (k - 1)
    · have h := (ih (k - 1) (by omega) A hAe hlow hA).succ
      rwa [Nat.sub_add_cancel hk] at h
    · have hA0 : A ≠ 0 := fun h => hlow (by rw [h, natDegree_zero]; exact Nat.zero_le _)
      have hpos : 0 < (A.map (algebraMap ℝ ℂ)).degree := by
        rw [← natDegree_pos_iff_degree_pos,
          natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
        omega
      obtain ⟨s, hs⟩ := Complex.exists_root hpos
      obtain ⟨j, F, G, hj, hF, hAFG, hdeg, hGe, hGnn⟩ := exists_factor_of_isRoot hAe hA0 hA hs
      have hjk : j ≤ k := by omega
      have h := hF.mul (ih (k - j) (by omega) G hGe (by omega) hGnn)
      rwa [← hAFG, Nat.add_sub_cancel' hjk] at h

/-- From `deg (X C) ≤ k`: `deg C ≤ k - 1`, and `C = 0` if `k = 0`. -/
theorem natDegree_le_pred_of_X_mul {C : ℝ[X]} {k : ℕ} (h : (X * C).natDegree ≤ k) :
    C.natDegree ≤ k - 1 ∧ (k = 0 → C = 0) := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp
  · rw [natDegree_X_mul hC] at h
    exact ⟨by omega, fun hk => absurd h (by omega)⟩

/-- From `X C` of parity `k` (and `C = 0` if `k = 0`): `C` has parity `k - 1`. -/
theorem hasParity_pred_of_X_mul {C : ℂ[X]} {k : ℕ} (h : HasParity (X * C) k) (hC : k = 0 → C = 0) :
    HasParity C (k - 1) := by
  rcases k with _ | n
  · rw [hC rfl]
    exact hasParity_zero _
  · rw [Nat.add_sub_cancel]
    exact h.of_X_mul

/-- QSP-7a (GSLW Lemma 6).  Let `A ∈ ℝ[X]` be even of degree `≤ 2k` with `A(x) ≥ 0` on
`[-1, 1]`.  Then there are real `B, C` with `A = B² + (1 - X²) C²`, `deg B ≤ k`, `deg C ≤ k - 1`
(and `C = 0` if `k = 0`), `B` of parity `k` and `C` of parity `k - 1`. -/
theorem exists_sumsq_decomposition (k : ℕ) (A : ℝ[X]) (hAe : IsEven (A.map (algebraMap ℝ ℂ)))
    (hAd : A.natDegree ≤ 2 * k) (hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) :
    ∃ B C : ℝ[X], A = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧ B.natDegree ≤ k ∧ C.natDegree ≤ k - 1 ∧
      (k = 0 → C = 0) ∧ HasParity (B.map (algebraMap ℝ ℂ)) k ∧
      HasParity (C.map (algebraMap ℝ ℂ)) (k - 1) := by
  obtain ⟨B, C, hABC, hB, hC, pB, pC⟩ := sosRep_of_nonneg k A hAe hAd hA
  obtain ⟨hC', hC0⟩ := natDegree_le_pred_of_X_mul hC
  exact ⟨B, C, hABC, hB, hC', hC0, pB,
    hasParity_pred_of_X_mul pC fun hk => by rw [hC0 hk, Polynomial.map_zero]⟩

/-! ### Complementary polynomials (GSLW Theorems 4/5, Cor 10) -/

/-- QSP-7b. The algebraic core of GSLW Theorem 5: if `1 - P̃² = B² + (1 - X²) C²` over `ℝ`, then
`P := P̃ + i B` and `Q := C` satisfy `P P^* + (1 - X²) Q Q^* = 1` over `ℂ`
(since `P P^* = P̃² + B²`). -/
theorem complement_unit (Pr B C : ℝ[X]) (h : 1 - Pr ^ 2 = B ^ 2 + (1 - X ^ 2) * C ^ 2) :
    (Pr.map (algebraMap ℝ ℂ) + Polynomial.C Complex.I * B.map (algebraMap ℝ ℂ)) *
        conjP (Pr.map (algebraMap ℝ ℂ) + Polynomial.C Complex.I * B.map (algebraMap ℝ ℂ)) +
      (1 - X ^ 2) * C.map (algebraMap ℝ ℂ) * conjP (C.map (algebraMap ℝ ℂ)) = 1 := by
  have hmap := congrArg (Polynomial.map (algebraMap ℝ ℂ)) h
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_X] at hmap
  have hI : (Polynomial.C Complex.I : ℂ[X]) ^ 2 = -1 := by
    rw [← C_pow, Complex.I_sq, C_neg, C_1]
  rw [conjP_add, conjP_mul, conjP_C, Complex.conj_I, conjP_map_algebraMap, conjP_map_algebraMap,
    conjP_map_algebraMap, C_neg]
  linear_combination (-(B.map (algebraMap ℝ ℂ) ^ 2)) * hI - hmap

/-- QSP-7b. `Re[P̃ + i B] = P̃` for real `P̃, B`. -/
theorem rePoly_map_add_I_mul_map (Pr B : ℝ[X]) :
    QSVT.SVT.rePoly (Pr.map (algebraMap ℝ ℂ) + Polynomial.C Complex.I * B.map (algebraMap ℝ ℂ)) =
      Pr.map (algebraMap ℝ ℂ) := by
  ext k
  rw [QSVT.SVT.coeff_rePoly, coeff_add, coeff_C_mul, coeff_map, coeff_map, Complex.coe_algebraMap]
  simp [Complex.add_re, Complex.mul_re]

/-- QSP-7b (GSLW Theorem 5, assembly from Lemma 6).  Given a real `P̃` of degree `≤ k` and parity
`k`, and a Lemma 6 decomposition `1 - P̃² = B² + (1 - X²) C²` with the degree/parity data, the
complex pair `P := P̃ + i B`, `Q := C` satisfies the hypotheses (i)–(iii) of `exists_phases` and
`Re[P] = P̃`. -/
theorem exists_complement_of_sumsq {k : ℕ} {Pr B C : ℝ[X]} (hP : Pr.natDegree ≤ k)
    (hPpar : HasParity (Pr.map (algebraMap ℝ ℂ)) k) (h : 1 - Pr ^ 2 = B ^ 2 + (1 - X ^ 2) * C ^ 2)
    (hB : B.natDegree ≤ k) (hC : C.natDegree ≤ k - 1) (hC0 : k = 0 → C = 0)
    (hBpar : HasParity (B.map (algebraMap ℝ ℂ)) k)
    (hCpar : HasParity (C.map (algebraMap ℝ ℂ)) (k - 1)) :
    ∃ P Q : ℂ[X], P.natDegree ≤ k ∧ Q.natDegree ≤ k - 1 ∧ (k = 0 → Q = 0) ∧ HasParity P k ∧
      HasParity Q (k - 1) ∧ P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1 ∧
      QSVT.SVT.rePoly P = Pr.map (algebraMap ℝ ℂ) :=
  ⟨Pr.map (algebraMap ℝ ℂ) + Polynomial.C Complex.I * B.map (algebraMap ℝ ℂ),
    C.map (algebraMap ℝ ℂ),
    natDegree_add_le_of_degree_le (natDegree_map_le.trans hP)
      ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hB)),
    natDegree_map_le.trans hC, fun hk => by rw [hC0 hk, Polynomial.map_zero],
    hPpar.add (hBpar.C_mul _), hCpar, complement_unit Pr B C h, rePoly_map_add_I_mul_map Pr B⟩

/-- QSP-7b (GSLW Theorem 5, real version; Cor 10).  For a real polynomial `P̃` of degree `≤ k`
and parity `k` with `P̃(x)² ≤ 1` on `[-1, 1]`, there are `P, Q ∈ ℂ[X]` satisfying the hypotheses
(i)–(iii) of `exists_phases` with `Re[P] = P̃`.  (Apply Lemma 6 to `A := 1 - P̃²`.) -/
theorem exists_complement (k : ℕ) (Pr : ℝ[X]) (hP : Pr.natDegree ≤ k)
    (hPpar : HasParity (Pr.map (algebraMap ℝ ℂ)) k)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pr.eval x ^ 2 ≤ 1) :
    ∃ P Q : ℂ[X], P.natDegree ≤ k ∧ Q.natDegree ≤ k - 1 ∧ (k = 0 → Q = 0) ∧ HasParity P k ∧
      HasParity Q (k - 1) ∧ P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1 ∧
      QSVT.SVT.rePoly P = Pr.map (algebraMap ℝ ℂ) := by
  have hAe : IsEven ((1 - Pr ^ 2).map (algebraMap ℝ ℂ)) := by
    rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, sq]
    exact isEven_one.sub ((hPpar.mul hPpar).isEven ⟨k, rfl⟩)
  have hAd : (1 - Pr ^ 2).natDegree ≤ 2 * k := by
    refine (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; omega) ?_)
    exact natDegree_pow_le.trans (by omega)
  have hA : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (1 - Pr ^ 2).eval x := by
    intro x hx
    rw [eval_sub, eval_one, eval_pow]
    linarith [hbound x hx]
  obtain ⟨B, C, h, hB, hC, hC0, hBpar, hCpar⟩ :=
    exists_sumsq_decomposition k (1 - Pr ^ 2) hAe hAd hA
  exact exists_complement_of_sumsq hP hPpar h hB hC hC0 hBpar hCpar

/-- QSP-7d (GSLW Cor 10, rotation convention).  A real polynomial `P̃` of degree `≤ k`, parity
`k`, and `|P̃| ≤ 1` on `[-1, 1]` is the real part of the QSP polynomial of some phase list
`(φ₀, Φ)` of length `k`: `Re[(qspPolyW φ₀ Φ).1] = P̃`. -/
theorem exists_phases_real (k : ℕ) (Pr : ℝ[X]) (hP : Pr.natDegree ≤ k)
    (hPpar : HasParity (Pr.map (algebraMap ℝ ℂ)) k)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pr.eval x ^ 2 ≤ 1) :
    ∃ φ₀ : ℝ, ∃ Φ : List ℝ, Φ.length = k ∧
      QSVT.SVT.rePoly (qspPolyW φ₀ Φ).1 = Pr.map (algebraMap ℝ ℂ) := by
  obtain ⟨P, Q, hPd, hQd, hQ0, hPp, hQp, hunit, hre⟩ := exists_complement k Pr hP hPpar hbound
  obtain ⟨φ₀, Φ, hlen, hΦ⟩ := exists_phases k P Q hPd hQd hQ0 hPp hQp hunit
  exact ⟨φ₀, Φ, hlen, by rw [hΦ]; exact hre⟩

/-- QSP-7d (GSLW Cor 10, reflection convention).  For `k ≥ 1` and a real `P̃` of degree `≤ k`,
parity `k`, `|P̃| ≤ 1` on `[-1, 1]`, there is a reflection-convention phase list `Φ` of length `k`
with `Re (seqR Φ x)₀₀ = P̃(x)` for all `x ∈ [-1, 1]`. -/
theorem exists_phases_R_real (k : ℕ) (hk : 1 ≤ k) (Pr : ℝ[X]) (hP : Pr.natDegree ≤ k)
    (hPpar : HasParity (Pr.map (algebraMap ℝ ℂ)) k)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pr.eval x ^ 2 ≤ 1) :
    ∃ Φ : List ℝ, Φ.length = k ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, ((seqR Φ x) 0 0).re = Pr.eval x := by
  obtain ⟨P, Q, hPd, hQd, _, hPp, hQp, hunit, hre⟩ := exists_complement k Pr hP hPpar hbound
  obtain ⟨Φ, hlen, hΦ⟩ := exists_phases_R k hk P Q hPd hQd hPp hQp hunit
  refine ⟨Φ, hlen, fun x hx => ?_⟩
  rw [hΦ x hx]
  have h := QSVT.SVT.eval_rePoly_ofReal P x
  rw [hre, eval_map_algebraMap_ofReal] at h
  exact_mod_cast h.symm

end QSVT.QSP
