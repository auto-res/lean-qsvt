/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.InvExample
import QSVT.Examples.Sign21

/-!
# APP-3: matrix inversion (the polynomial step of GSLW Thm 41) implemented by Route A

The polynomial step of GSLW's pseudoinverse / quantum linear-systems algorithm (Lemma 40,
Thm 41), restricted to the Hermitian/eigenvector case: for a Hermitian block encoding `E` of `A`
with eigenvalues in `[-1, 1]`, on the part of the spectrum with `|λ| ≥ 1/κ`, `κ = 4`, the block
implemented here acts as `(3/4) · A⁻¹ / (κ ‖c‖₁)` up to `ε / ‖c‖₁`, where `‖c‖₁ = invL1 ≈ 1.6635`
is the Route A subnormalisation and `ε = invEps = 7.5 · 10⁻⁴`.  Not included are the amplitude
amplification and the normalisation of GSLW Thm 41 (which turn this block into a block
encoding of `A⁻¹/κ` with constant subnormalisation), nor the handling of the part of the
spectrum below the gap (where the polynomial is only known to be bounded by `1`).

* The polynomial is `invPoly : PolyQ` (CERT-B, `QSVT.Certificate.InvExample`): the odd
  degree-29 approximation of `(3/4)/(4x)` with the kernel-checked LeanCert certificates
  `‖p‖_∞ ≤ 1` and `‖p(x) − (3/4)/(4x)‖ ≤ ε` for `|x| ∈ [1/4, 1]`.  The constant `3/4` is forced:
  an odd polynomial bounded by `1` cannot approximate `1/(κ x)` itself to accuracy `10⁻³` below
  degree `Ω(10³)` (see the module docstring of `QSVT.Certificate.InvExample`).
* Its Chebyshev coefficients `invCheb = ChebQC.ofMonomials invPolyQC` are *computed* inside Lean
  (POLY-6): `30` entries (`invCheb_length`), all real (`invCheb_im_eq_zero`), both reproved by
  the kernel with `decide +kernel`.
* The circuit is Route A (CERT-A): `invCircuit E = chebLCU E (chebCoeffs invPolyQC)`, the
  `30`-term LCU of the closed-form Chebyshev unitaries `U_{chebPhases k}` on the register
  `Reg 30 ℋ` (`⌈log₂ 30⌉ = 5` ancilla qubits).  It implements `p(A)` *exactly* up to the
  subnormalisation `‖c‖₁ = invL1` (`invCircuit_topLeft`), and
  `invL1 = 1663547352803317028028563806518659 / 10³³ ≈ 1.6635` exactly (`invL1_eq`, by
  `l1_eq_l1Bound_of_real` and a kernel evaluation of `ChebQC.l1Bound`).
* On the eigenbasis of `A` (SVT-3) this gives the GSLW Thm 41-style statements
  `invCircuit_apply_pos` / `invCircuit_apply_neg`: every eigenvector `ψᵢ` with eigenvalue
  `|λᵢ| ≥ 1/4` is mapped by the compressed circuit to `((3/4)/(4 λᵢ) / ‖c‖₁) ψᵢ`, i.e. to
  `(3/(16 ‖c‖₁)) · λᵢ⁻¹ ψᵢ`, up to an error of norm `≤ ε / ‖c‖₁ ≈ 4.5 · 10⁻⁴`; and every
  eigenvector is mapped to a vector of norm `≤ 1 / ‖c‖₁ ≈ 0.6011` (`invCircuit_apply_norm_le`).
* Resources: `routeA_queries 30 = 435` uses of `U`/`U†` (`invCircuit_queries`); the phase-based
  Route B would use the optimal `deg p = 29` queries and one ancilla qubit.
* The same example through the IR (IR-1/2): `invExpr = chebLCU 0 (tail of the real parts) oracle`
  has `spec invExpr = invPoly.toPoly`, `scale invExpr = invL1`, `queries invExpr = 435`,
  `ancillaDim invExpr = 30`, and the soundness theorem gives `base_invExpr`.

All kernel computations (`decide +kernel` on `ofMonomials` of a degree-29 polynomial with
`30`-digit decimal coefficients) take a few seconds each; nothing here uses `native_decide`, so
every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`test/QSVTTest/Inverse.lean`).

## Mathlib API used

`Complex.ofReal_div`, `Complex.norm_real`, `norm_inv`, `norm_smul`, `mul_le_mul_of_nonneg_left`,
`Rat.cast_list_sum`, `Rat.cast_abs`, `div_eq_inv_mul`, `sub_smul`, `mul_sub`.
-/

namespace QSVT.Examples

open QSVT.Pipeline QSVT.Certificate QSVT.SVT QSVT.Poly QSVT.Encoding QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The input: `invPoly` and its Chebyshev coefficients -/

/-- APP-3. The degree-29 inverse approximation `invPoly` (CERT-B) as a polynomial with
Gaussian-rational coefficients in the monomial basis (all imaginary parts zero). -/
def invPolyQC : PolyQC := PolyQ.toPolyQC invPoly

/-- APP-3. The Chebyshev coefficients `c` of `invPoly = ∑ₖ cₖ T_k`, computed by POLY-6
`ChebQC.ofMonomials`: `30` entries, the even ones zero (the exact list is checked in the
tests). -/
abbrev invCheb : ChebQC := ChebQC.ofMonomials invPolyQC

/-- APP-3. The register dimension `m = 30` (one Chebyshev coefficient per degree `0, …, 29`),
reproved by the kernel. -/
theorem invCheb_length : invCheb.length = 30 := by decide +kernel

/-- APP-3. The register dimension is nonzero (the hypothesis of `regTopLeft` and `routeA`). -/
instance invCheb_neZero : NeZero invCheb.length := ⟨by rw [invCheb_length]; norm_num⟩

/-- APP-3. All Chebyshev coefficients of `invPoly` are real, reproved by the kernel. -/
theorem invCheb_im_eq_zero : ∀ z ∈ invCheb, z.2 = 0 := by decide +kernel

/-- APP-3. The subnormalisation of the Route A circuit: the `ℓ¹` norm `‖c‖₁ = ∑ₖ |cₖ|` of the
Chebyshev coefficients of `invPoly` (`≈ 1.6635`, exactly `invL1_eq`). -/
noncomputable def invL1 : ℝ := l1 (chebCoeffs invPolyQC)

/-- APP-3. The exact value of `ChebQC.l1Bound invCheb` (a kernel evaluation):
`1663547352803317028028563806518659 / 10³³ ≈ 1.6635`. -/
theorem l1Bound_invCheb :
    ChebQC.l1Bound invCheb =
      1663547352803317028028563806518659 / 1000000000000000000000000000000000 := by
  decide +kernel

/-- APP-3. The exact subnormalisation `‖c‖₁ = 1663547352803317028028563806518659 / 10³³`. -/
theorem invL1_eq :
    invL1 =
      ((1663547352803317028028563806518659 / 1000000000000000000000000000000000 : ℚ) : ℝ) := by
  rw [invL1, l1_eq_l1Bound_of_real invPolyQC invCheb_im_eq_zero, l1Bound_invCheb]

/-- APP-3. `‖c‖₁ > 0`. -/
theorem invL1_pos : 0 < invL1 := by
  rw [invL1_eq]
  norm_num

/-- APP-3. Decimal bounds `1.6635 ≤ ‖c‖₁ ≤ 1.6636`. -/
theorem invL1_mem_Icc : invL1 ∈ Set.Icc (1.6635 : ℝ) 1.6636 := by
  rw [invL1_eq]
  constructor <;> norm_num

theorem norm_inv_invL1 : ‖((invL1 : ℂ)⁻¹)‖ = invL1⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg invL1_pos.le]

/-! ### The implementation: the Route A circuit -/

section Circuit

variable (E : HermitianEncoding ℋ)

/-- APP-3. The circuit: the Route A unitary of CERT-A for the Chebyshev coefficients of
`invPoly`, a `30`-term LCU of the Chebyshev unitaries `U_{chebPhases k}` (`k < 30`) on the
register `Reg 30 ℋ`, using `435` queries to `U`/`U†` (`invCircuit_queries`). -/
noncomputable def invCircuit : L (Reg invCheb.length ℋ) := chebLCU E (chebCoeffs invPolyQC)

/-- APP-3. The circuit is unitary. -/
theorem invCircuit_mem_unitary : invCircuit E ∈ unitary (L (Reg invCheb.length ℋ)) :=
  chebLCU_mem_unitary E _

/-- APP-3 (exact implementation). The `(0,0)` block of the compressed circuit is
`‖c‖₁⁻¹ • p(A) Π` for `p = invPoly`, with zero error:
```
(⟨0| ⊗ Π) invCircuit E (|0⟩ ⊗ Π) = invL1⁻¹ • (invPoly(A) Π).
```
-/
theorem invCircuit_topLeft :
    regTopLeft (regP E * invCircuit E * regP E) =
      ((invL1 : ℂ)⁻¹) • (aeval E.encoded invPoly.toPoly * E.P) :=
  routeA E invPolyQC invL1_pos.ne'

variable (i : Fin (Module.finrank ℂ (rangeP E)))

/-- APP-3. On an eigenvector `ψᵢ` of `A` with eigenvalue `λᵢ`, the compressed circuit acts as
the scalar `‖c‖₁⁻¹ · p(λᵢ)` (SVT-3 `aeval_eigenVec`). -/
theorem invCircuit_apply_eigenVec :
    regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i) =
      ((invL1 : ℂ)⁻¹ * invPoly.toPoly.eval (eigenValue E i : ℂ)) • eigenVec E i := by
  rw [invCircuit_topLeft, LinearMap.smul_apply, Module.End.mul_apply, P_eigenVec,
    aeval_eigenVec, smul_smul]

/-- APP-3 (helper). The error vector on an eigenvector, given the pointwise certificate at its
eigenvalue: `‖(circuit) ψᵢ − ((3/4)/(4 λᵢ) / ‖c‖₁) ψᵢ‖ ≤ ε / ‖c‖₁`. -/
theorem invCircuit_apply_of_cert
    (hcert : ‖invPoly.toPoly.eval (eigenValue E i : ℂ) -
      (((invScale : ℝ) / (4 * eigenValue E i) : ℝ) : ℂ)‖ ≤ invEps) :
    ‖regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i) -
        (((invScale : ℝ) / (4 * eigenValue E i) / invL1 : ℝ) : ℂ) • eigenVec E i‖ ≤
      invEps / invL1 := by
  have hvec : regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i) -
      (((invScale : ℝ) / (4 * eigenValue E i) / invL1 : ℝ) : ℂ) • eigenVec E i =
      ((invL1 : ℂ)⁻¹ * (invPoly.toPoly.eval (eigenValue E i : ℂ) -
        (((invScale : ℝ) / (4 * eigenValue E i) : ℝ) : ℂ))) • eigenVec E i := by
    rw [invCircuit_apply_eigenVec, ← sub_smul]
    congr 1
    push_cast
    ring
  rw [hvec, norm_smul, norm_mul, norm_inv_invL1, norm_eigenVec, mul_one]
  refine (mul_le_mul_of_nonneg_left hcert (inv_nonneg.mpr invL1_pos.le)).trans_eq ?_
  rw [div_eq_inv_mul]

/-- APP-3 (certified behaviour, positive spectrum; GSLW Thm 41 style). Every eigenvector `ψᵢ`
of `A` with eigenvalue `λᵢ ≥ 1/4` is mapped by the compressed circuit to
`((3/4)/(4 λᵢ) / ‖c‖₁) ψᵢ = (3/(16 ‖c‖₁)) λᵢ⁻¹ ψᵢ`, up to an error of norm at most
`ε / ‖c‖₁ ≈ 4.5 · 10⁻⁴`. -/
theorem invCircuit_apply_pos (hi : 1 / 4 ≤ eigenValue E i) :
    ‖regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i) -
        (((invScale : ℝ) / (4 * eigenValue E i) / invL1 : ℝ) : ℂ) • eigenVec E i‖ ≤
      invEps / invL1 :=
  invCircuit_apply_of_cert E i
    (norm_eval_invPoly_sub_inv_le _ ⟨hi, (eigenValue_mem_Icc E i).2⟩)

/-- APP-3 (certified behaviour, negative spectrum). Every eigenvector `ψᵢ` of `A` with
eigenvalue `λᵢ ≤ -1/4` is mapped to `((3/4)/(4 λᵢ) / ‖c‖₁) ψᵢ` (a negative multiple), up to an
error of norm at most `ε / ‖c‖₁ ≈ 4.5 · 10⁻⁴`. -/
theorem invCircuit_apply_neg (hi : eigenValue E i ≤ -(1 / 4)) :
    ‖regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i) -
        (((invScale : ℝ) / (4 * eigenValue E i) / invL1 : ℝ) : ℂ) • eigenVec E i‖ ≤
      invEps / invL1 :=
  invCircuit_apply_of_cert E i
    (norm_eval_invPoly_sub_inv_le_neg _ ⟨(eigenValue_mem_Icc E i).1, hi⟩)

/-- APP-3 (global bound). The compressed circuit maps every eigenvector `ψᵢ` (any eigenvalue in
`[-1, 1]`, gapped or not) to a vector of norm at most `1 / ‖c‖₁ ≈ 0.6011`, from the
admissibility certificate `‖invPoly‖_∞ ≤ 1`. -/
theorem invCircuit_apply_norm_le :
    ‖regTopLeft (regP E * invCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / invL1 := by
  rw [invCircuit_apply_eigenVec, norm_smul, norm_mul, norm_inv_invL1, norm_eigenVec, mul_one,
    one_div]
  have h : ‖invPoly.toPoly.eval (eigenValue E i : ℂ)‖ ≤ 1 :=
    (norm_eval_le_supNorm _ (eigenValue_mem_Icc E i)).trans supNorm_invPoly_le_one
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr invL1_pos.le)).trans_eq (mul_one _)

end Circuit

/-! ### Resources -/

/-- APP-3. The query count of the circuit: `∑_{k<30} k = 435` uses of `U`/`U†`. The phase-based
Route B would use the optimal `deg p = 29` queries and one ancilla qubit, whereas Route A uses
`435 = 15 · 29` queries and a `30`-dimensional ancilla register (`⌈log₂ 30⌉ = 5` qubits) but
needs no phase-finding. -/
theorem invCircuit_queries : routeA_queries invCheb.length = 435 := by
  rw [invCheb_length, routeA_queries_eq]

/-! ### The same example through the IR (IR-1/2) -/

section IR

open QSVT.IR

/-- APP-3. The real parts of the Chebyshev coefficients, as rationals. -/
def invChebQ : List ℚ := invCheb.map Prod.fst

/-- APP-3. The IR program: one Route A node with the Chebyshev coefficients of `invPoly`
(leading coefficient `c₀ = 0`, then the remaining `29`) applied to the oracle. -/
def invExpr : Expr := .chebLCU 0 invChebQ.tail .oracle

theorem invChebQ_tail_length : invChebQ.tail.length = 29 := by decide +kernel

/-- APP-3. The coefficient list of `invExpr` is `invCheb` (kernel check). -/
theorem map_invChebQ : (0 :: invChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = invCheb := by
  decide +kernel

/-- APP-3. The specification polynomial of `invExpr` is `invPoly`. -/
theorem spec_invExpr : spec invExpr = invPoly.toPoly := by
  rw [invExpr, spec_chebLCU, normSpec_oracle, comp_X, chebPoly_eq_toPoly, map_invChebQ,
    ChebQC.toPoly_ofMonomials]
  rfl

/-- APP-3. The subnormalisation of `invExpr` is `‖c‖₁ = invL1`. -/
theorem scale_invExpr : scale invExpr = invL1 := by
  have h : ((0 :: invChebQ.tail).map fun q : ℚ => |q|).sum =
      1663547352803317028028563806518659 / 1000000000000000000000000000000000 := by
    decide +kernel
  rw [invExpr, scale_chebLCU, chebScale, invL1_eq, ← h, Rat.cast_list_sum, List.map_map]
  simp [Function.comp_def, Rat.cast_abs]

/-- APP-3. `invExpr` is well scaled. -/
theorem invExpr_wellScaled : WellScaled invExpr := by
  refine ⟨?_, trivial⟩
  have h : scale invExpr ≠ 0 := by
    rw [scale_invExpr]
    exact invL1_pos.ne'
  exact h

/-- APP-3 (through the IR soundness theorem). The base block of `invExpr` is
`‖c‖₁⁻¹ • invPoly(A₀) Π`, the same operator as `invCircuit_topLeft`. -/
theorem base_invExpr (E₀ : HermitianEncoding ℋ) :
    base E₀ invExpr = ((invL1 : ℂ)⁻¹) • (aeval E₀.encoded invPoly.toPoly * E₀.P) := by
  rw [base_eq_smul E₀ invExpr_wellScaled, scale_invExpr, spec_invExpr]

/-- APP-3. `invExpr` uses `435` oracle queries (IR-2). -/
theorem queries_invExpr : queries invExpr = 435 := by
  rw [invExpr, queries_chebLCU_eq_routeA, invChebQ_tail_length, queries_oracle, mul_one,
    routeA_queries_eq]

/-- APP-3. The ancilla of `invExpr` is the `30`-dimensional register (IR-2). -/
theorem ancillaDim_invExpr : ancillaDim invExpr = 30 := by
  rw [invExpr, ancillaDim_chebLCU, invChebQ_tail_length, ancillaDim_oracle]

end IR

end QSVT.Examples
