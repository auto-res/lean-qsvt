/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.RectExample
import QSVT.Examples.Sign21

/-!
# APP-2: the threshold projector (GSLW Lemma 29 / Thm 31) implemented by Route A

GSLW Thm 31 ("singular value threshold projector") applies the even rectangle polynomial of
Lemma 29 to a block encoding and obtains a block encoding of the projector onto the singular
vectors with singular value below a threshold `t`, up to `ε`, with the singular values in the
transition band `(t − δ, t + δ)` left unspecified.  Here it is restricted to the
Hermitian/eigenvector case, where it is an *eigenvalue window filter*: for a Hermitian block
encoding `E` of `A` with eigenvalues in `[-1, 1]`, the block implemented here acts as
`‖c‖₁⁻¹ · 1` on the eigenvectors with `|λ| ≤ t − δ = 0.4` and as `0` on those with
`|λ| ≥ t + δ = 0.6`, both up to `ε / ‖c‖₁`, where `‖c‖₁ = rectL1 ≈ 1.6175` is the Route A
subnormalisation and `ε = rectEps = 10⁻²`.  Combined with the loop example
(`QSVT.Examples.Loop`, iterating one block encoding), such a window is the eigenvalue-threshold
test of a ground-energy binary search: a projector onto the low-energy eigenspace, whose
expectation on the input state is the probability mass below the threshold.  Not included are
the amplitude amplification and the normalisation of GSLW Thm 31 (which remove the
subnormalisation `‖c‖₁`), nor the behaviour on the transition band `0.4 < |λ| < 0.6` (where the
polynomial is only known to be bounded by `1`).

* The polynomial is `rectPoly : PolyQ` (CERT-B, `QSVT.Certificate.RectExample`): the even
  degree-32 maximal-margin fit of the rectangle function with the kernel-checked LeanCert
  certificates `‖r‖_∞ ≤ 1`, `‖r(x) − 1‖ ≤ ε` for `|x| ≤ 0.4` and `‖r(x)‖ ≤ ε` for
  `0.6 ≤ |x| ≤ 1`.
* Its Chebyshev coefficients `rectCheb = ChebQC.ofMonomials rectPolyQC` are *computed* inside
  Lean (POLY-6): `33` entries (`rectCheb_length`), all real (`rectCheb_im_eq_zero`), both
  reproved by the kernel with `decide +kernel`.  Unlike the odd examples (`Sign21`, `Inverse`)
  the leading coefficient `c₀ = 0.3392` is nonzero: the IR node is `chebLCU c₀ (tail)`.
* The circuit is Route A (CERT-A): `rectCircuit E = chebLCU E (chebCoeffs rectPolyQC)`, the
  `33`-term LCU of the closed-form Chebyshev unitaries `U_{chebPhases k}` on the register
  `Reg 33 ℋ` (`⌈log₂ 33⌉ = 6` ancilla qubits).  It implements `r(A)` *exactly* up to the
  subnormalisation `‖c‖₁ = rectL1` (`rectCircuit_topLeft`), and
  `rectL1 = 1293999354903681376499635646837 / (8 · 10²⁹) ≈ 1.6175` exactly (`rectL1_eq`, by
  `l1_eq_l1Bound_of_real` and a kernel evaluation of `ChebQC.l1Bound`).
* On the eigenbasis of `A` (SVT-3) this gives the GSLW Thm 31-style statements
  `rectCircuit_apply_inner` / `rectCircuit_apply_outer`: every eigenvector `ψᵢ` with eigenvalue
  `|λᵢ| ≤ 0.4` is mapped by the compressed circuit to `‖c‖₁⁻¹ ψᵢ ≈ 0.6182 ψᵢ`, and every
  eigenvector with `|λᵢ| ≥ 0.6` to a vector of norm `≤ ε / ‖c‖₁ ≈ 6.2 · 10⁻³` (the first up to
  an error of the same norm); and every eigenvector is mapped to a vector of norm
  `≤ 1 / ‖c‖₁ ≈ 0.6182` (`rectCircuit_apply_norm_le`).
* Resources: `routeA_queries 33 = 528` uses of `U`/`U†` (`rectCircuit_queries`); the
  phase-based Route B would use the optimal `deg r = 32` queries and one ancilla qubit.
* The same example through the IR (IR-1/2): `rectExpr = chebLCU c₀ (tail of the real parts)
  oracle` has `spec rectExpr = rectPoly.toPoly`, `scale rectExpr = rectL1`,
  `queries rectExpr = 528`, `ancillaDim rectExpr = 33`, and the soundness theorem gives
  `base_rectExpr`.

All kernel computations (`decide +kernel` on `ofMonomials` of a degree-32 polynomial with
`30`-digit decimal coefficients) take a few seconds each; nothing here uses `native_decide`, so
every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`test/QSVTTest/Threshold.lean`).

## Mathlib API used

`abs_le`, `le_abs`, `Complex.norm_real`, `norm_inv`, `norm_smul`, `mul_le_mul_of_nonneg_left`,
`Rat.cast_list_sum`, `Rat.cast_abs`, `div_eq_inv_mul`, `sub_smul`.
-/

namespace QSVT.Examples

open QSVT.Pipeline QSVT.Certificate QSVT.SVT QSVT.Poly QSVT.Encoding QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The input: `rectPoly` and its Chebyshev coefficients -/

/-- APP-2. The degree-32 rectangle approximation `rectPoly` (CERT-B) as a polynomial with
Gaussian-rational coefficients in the monomial basis (all imaginary parts zero). -/
def rectPolyQC : PolyQC := PolyQ.toPolyQC rectPoly

/-- APP-2. The Chebyshev coefficients `c` of `rectPoly = ∑ₖ cₖ T_k`, computed by POLY-6
`ChebQC.ofMonomials`: `33` entries, the odd ones zero (the exact list is checked in the
tests). -/
abbrev rectCheb : ChebQC := ChebQC.ofMonomials rectPolyQC

/-- APP-2. The register dimension `m = 33` (one Chebyshev coefficient per degree `0, …, 32`),
reproved by the kernel. -/
theorem rectCheb_length : rectCheb.length = 33 := by decide +kernel

/-- APP-2. The register dimension is nonzero (the hypothesis of `regTopLeft` and `routeA`). -/
instance rectCheb_neZero : NeZero rectCheb.length := ⟨by rw [rectCheb_length]; norm_num⟩

/-- APP-2. All Chebyshev coefficients of `rectPoly` are real, reproved by the kernel. -/
theorem rectCheb_im_eq_zero : ∀ z ∈ rectCheb, z.2 = 0 := by decide +kernel

/-- APP-2. The subnormalisation of the Route A circuit: the `ℓ¹` norm `‖c‖₁ = ∑ₖ |cₖ|` of the
Chebyshev coefficients of `rectPoly` (`≈ 1.6175`, exactly `rectL1_eq`). -/
noncomputable def rectL1 : ℝ := l1 (chebCoeffs rectPolyQC)

/-- APP-2. The exact value of `ChebQC.l1Bound rectCheb` (a kernel evaluation):
`1293999354903681376499635646837 / (8 · 10²⁹) ≈ 1.6175`. -/
theorem l1Bound_rectCheb :
    ChebQC.l1Bound rectCheb =
      1293999354903681376499635646837 / 800000000000000000000000000000 := by
  decide +kernel

/-- APP-2. The exact subnormalisation `‖c‖₁ = 1293999354903681376499635646837 / (8 · 10²⁹)`. -/
theorem rectL1_eq :
    rectL1 =
      ((1293999354903681376499635646837 / 800000000000000000000000000000 : ℚ) : ℝ) := by
  rw [rectL1, l1_eq_l1Bound_of_real rectPolyQC rectCheb_im_eq_zero, l1Bound_rectCheb]

/-- APP-2. `‖c‖₁ > 0`. -/
theorem rectL1_pos : 0 < rectL1 := by
  rw [rectL1_eq]
  norm_num

/-- APP-2. Decimal bounds `1.6174 ≤ ‖c‖₁ ≤ 1.6175`. -/
theorem rectL1_mem_Icc : rectL1 ∈ Set.Icc (1.6174 : ℝ) 1.6175 := by
  rw [rectL1_eq]
  constructor <;> norm_num

theorem norm_inv_rectL1 : ‖((rectL1 : ℂ)⁻¹)‖ = rectL1⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg rectL1_pos.le]

/-! ### The implementation: the Route A circuit -/

section Circuit

variable (E : HermitianEncoding ℋ)

/-- APP-2. The circuit: the Route A unitary of CERT-A for the Chebyshev coefficients of
`rectPoly`, a `33`-term LCU of the Chebyshev unitaries `U_{chebPhases k}` (`k < 33`) on the
register `Reg 33 ℋ`, using `528` queries to `U`/`U†` (`rectCircuit_queries`). -/
noncomputable def rectCircuit : L (Reg rectCheb.length ℋ) := chebLCU E (chebCoeffs rectPolyQC)

/-- APP-2. The circuit is unitary. -/
theorem rectCircuit_mem_unitary : rectCircuit E ∈ unitary (L (Reg rectCheb.length ℋ)) :=
  chebLCU_mem_unitary E _

/-- APP-2 (exact implementation). The `(0,0)` block of the compressed circuit is
`‖c‖₁⁻¹ • r(A) Π` for `r = rectPoly`, with zero error:
```
(⟨0| ⊗ Π) rectCircuit E (|0⟩ ⊗ Π) = rectL1⁻¹ • (rectPoly(A) Π).
```
-/
theorem rectCircuit_topLeft :
    regTopLeft (regP E * rectCircuit E * regP E) =
      ((rectL1 : ℂ)⁻¹) • (aeval E.encoded rectPoly.toPoly * E.P) :=
  routeA E rectPolyQC rectL1_pos.ne'

variable (i : Fin (Module.finrank ℂ (rangeP E)))

/-- APP-2. On an eigenvector `ψᵢ` of `A` with eigenvalue `λᵢ`, the compressed circuit acts as
the scalar `‖c‖₁⁻¹ · r(λᵢ)` (SVT-3 `aeval_eigenVec`). -/
theorem rectCircuit_apply_eigenVec :
    regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i) =
      ((rectL1 : ℂ)⁻¹ * rectPoly.toPoly.eval (eigenValue E i : ℂ)) • eigenVec E i := by
  rw [rectCircuit_topLeft, LinearMap.smul_apply, Module.End.mul_apply, P_eigenVec,
    aeval_eigenVec, smul_smul]

/-- APP-2 (certified behaviour, inside the window; GSLW Thm 31 style). Every eigenvector `ψᵢ`
of `A` with eigenvalue `|λᵢ| ≤ 0.4 = t − δ` is mapped by the compressed circuit to
`‖c‖₁⁻¹ ψᵢ ≈ 0.6182 ψᵢ`, up to an error of norm at most `ε / ‖c‖₁ ≈ 6.2 · 10⁻³`. -/
theorem rectCircuit_apply_inner (hi : |eigenValue E i| ≤ 0.4) :
    ‖regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i) -
        ((1 / rectL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ rectEps / rectL1 := by
  have hcert := norm_eval_rectPoly_sub_one_le_of_abs hi
  have hvec : regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i) -
      ((1 / rectL1 : ℝ) : ℂ) • eigenVec E i =
      ((rectL1 : ℂ)⁻¹ * (rectPoly.toPoly.eval (eigenValue E i : ℂ) - 1)) • eigenVec E i := by
    rw [rectCircuit_apply_eigenVec, ← sub_smul]
    congr 1
    push_cast
    ring
  rw [hvec, norm_smul, norm_mul, norm_inv_rectL1, norm_eigenVec, mul_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hcert (inv_nonneg.mpr rectL1_pos.le)

/-- APP-2 (certified behaviour, outside the window; GSLW Thm 31 style). Every eigenvector `ψᵢ`
of `A` with eigenvalue `|λᵢ| ≥ 0.6 = t + δ` is mapped by the compressed circuit to a vector of
norm at most `ε / ‖c‖₁ ≈ 6.2 · 10⁻³` (it is annihilated up to `ε / ‖c‖₁`). -/
theorem rectCircuit_apply_outer (hi : 0.6 ≤ |eigenValue E i|) :
    ‖regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i)‖ ≤ rectEps / rectL1 := by
  have hcert := norm_eval_rectPoly_le_of_abs hi (abs_le.mpr (eigenValue_mem_Icc E i))
  rw [rectCircuit_apply_eigenVec, norm_smul, norm_mul, norm_inv_rectL1, norm_eigenVec, mul_one,
    div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hcert (inv_nonneg.mpr rectL1_pos.le)

/-- APP-2 (global bound). The compressed circuit maps every eigenvector `ψᵢ` (any eigenvalue in
`[-1, 1]`, including the transition band) to a vector of norm at most `1 / ‖c‖₁ ≈ 0.6182`,
from the admissibility certificate `‖rectPoly‖_∞ ≤ 1`. -/
theorem rectCircuit_apply_norm_le :
    ‖regTopLeft (regP E * rectCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / rectL1 := by
  rw [rectCircuit_apply_eigenVec, norm_smul, norm_mul, norm_inv_rectL1, norm_eigenVec, mul_one,
    one_div]
  have h : ‖rectPoly.toPoly.eval (eigenValue E i : ℂ)‖ ≤ 1 :=
    (norm_eval_le_supNorm _ (eigenValue_mem_Icc E i)).trans supNorm_rectPoly_le_one
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr rectL1_pos.le)).trans_eq (mul_one _)

end Circuit

/-! ### Resources -/

/-- APP-2. The query count of the circuit: `∑_{k<33} k = 528` uses of `U`/`U†`. The phase-based
Route B would use the optimal `deg r = 32` queries and one ancilla qubit, whereas Route A uses
`528 = 16.5 · 32` queries and a `33`-dimensional ancilla register (`⌈log₂ 33⌉ = 6` qubits) but
needs no phase-finding. -/
theorem rectCircuit_queries : routeA_queries rectCheb.length = 528 := by
  rw [rectCheb_length, routeA_queries_eq]

/-! ### The same example through the IR (IR-1/2) -/

section IR

open QSVT.IR

/-- APP-2. The real parts of the Chebyshev coefficients, as rationals. -/
def rectChebQ : List ℚ := rectCheb.map Prod.fst

/-- APP-2. The IR program: one Route A node with the Chebyshev coefficients of `rectPoly`
(leading coefficient `c₀ = rectChebQ.headD 0 ≈ 0.3392`, then the remaining `32`) applied to
the oracle. -/
def rectExpr : Expr := .chebLCU (rectChebQ.headD 0) rectChebQ.tail .oracle

theorem rectChebQ_tail_length : rectChebQ.tail.length = 32 := by decide +kernel

/-- APP-2. The coefficient list of `rectExpr` is `rectCheb` (kernel check). -/
theorem map_rectChebQ :
    (rectChebQ.headD 0 :: rectChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = rectCheb := by
  decide +kernel

/-- APP-2. The specification polynomial of `rectExpr` is `rectPoly`. -/
theorem spec_rectExpr : spec rectExpr = rectPoly.toPoly := by
  rw [rectExpr, spec_chebLCU, normSpec_oracle, comp_X, chebPoly_eq_toPoly, map_rectChebQ,
    ChebQC.toPoly_ofMonomials]
  rfl

/-- APP-2. The subnormalisation of `rectExpr` is `‖c‖₁ = rectL1`. -/
theorem scale_rectExpr : scale rectExpr = rectL1 := by
  have h : ((rectChebQ.headD 0 :: rectChebQ.tail).map fun q : ℚ => |q|).sum =
      1293999354903681376499635646837 / 800000000000000000000000000000 := by
    decide +kernel
  rw [rectExpr, scale_chebLCU, chebScale, rectL1_eq, ← h, Rat.cast_list_sum, List.map_map]
  simp [Function.comp_def, Rat.cast_abs]

/-- APP-2. `rectExpr` is well scaled. -/
theorem rectExpr_wellScaled : WellScaled rectExpr := by
  refine ⟨?_, trivial⟩
  have h : scale rectExpr ≠ 0 := by
    rw [scale_rectExpr]
    exact rectL1_pos.ne'
  exact h

/-- APP-2 (through the IR soundness theorem). The base block of `rectExpr` is
`‖c‖₁⁻¹ • rectPoly(A₀) Π`, the same operator as `rectCircuit_topLeft`. -/
theorem base_rectExpr (E₀ : HermitianEncoding ℋ) :
    base E₀ rectExpr = ((rectL1 : ℂ)⁻¹) • (aeval E₀.encoded rectPoly.toPoly * E₀.P) := by
  rw [base_eq_smul E₀ rectExpr_wellScaled, scale_rectExpr, spec_rectExpr]

/-- APP-2. `rectExpr` uses `528` oracle queries (IR-2). -/
theorem queries_rectExpr : queries rectExpr = 528 := by
  rw [rectExpr, queries_chebLCU_eq_routeA, rectChebQ_tail_length, queries_oracle, mul_one,
    routeA_queries_eq]

/-- APP-2. The ancilla of `rectExpr` is the `33`-dimensional register (IR-2). -/
theorem ancillaDim_rectExpr : ancillaDim rectExpr = 33 := by
  rw [rectExpr, ancillaDim_chebLCU, rectChebQ_tail_length, ancillaDim_oracle]

end IR

end QSVT.Examples
