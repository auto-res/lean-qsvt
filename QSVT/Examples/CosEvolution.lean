/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.CosExample
import QSVT.Examples.Sign21

/-!
# APP-4 (lite): the real part of Hamiltonian simulation, `cos (2A)`, implemented by Route A

The second end-to-end application of the library (formal-spec APP-4, GSLW Thm 58 "Hamiltonian
simulation", restricted to the Hermitian/eigenvector case and to the real part of the target).
For a Hermitian block encoding `E` of `A` (eigenvalues in `[-1, 1]`) and the evolution time
`t = 2`, the target `e^{-itA}` has real part `cos (tA)` and imaginary part `-sin (tA)`; this module
implements the even polynomial approximation of `cos (2x)` certified in
`QSVT.Certificate.CosExample` (CERT-B) exactly, by the Route A circuit of CERT-A.

* The polynomial is the degree-10 Jacobi–Anger truncation `cos2Poly : PolyQ` of `cos (2x)`
  (`J₀(2) + 2 ∑_{k=1}^{5} (-1)^k J_{2k}(2) T_{2k}`), with the kernel-checked certificates
  `|p(x) − cos (2x)| ≤ 10⁻⁶` and `‖p‖_∞ ≤ 1` on `[-1, 1]` (the true error is `3.9 · 10⁻⁹`).
* Its Chebyshev coefficients `cosCheb = ChebQC.ofMonomials cosPoly` are *computed* inside Lean
  (POLY-6): `11` entries (`cosCheb_length`), all real (`cosCheb_im_eq_zero`), the odd ones zero,
  reproved by the kernel with `decide +kernel`.  Because the Chebyshev coefficients alternate in
  sign and `T_{2k}(0) = (-1)^k`, the `ℓ¹` norm `‖c‖₁ = ∑ₖ |cₖ|` equals `p(0) = 1 − 3.9 · 10⁻⁹`
  exactly (`cosL1_eq`): the Route A subnormalisation is essentially trivial for this target, in
  contrast with the sign example (`‖c‖₁ ≈ 2.21`).
* The circuit is Route A (CERT-A): `cosCircuit E = chebLCU E (chebCoeffs cosPoly)`, the `11`-term
  LCU of the closed-form Chebyshev unitaries `U_{chebPhases k}` on the register `Reg 11 ℋ`
  (`⌈log₂ 11⌉ = 4` ancilla qubits).  It implements `p(A)` *exactly* up to the subnormalisation
  `‖c‖₁ = cosL1` (`cosCircuit_topLeft`).
* On the eigenbasis of `A` (SVT-3) this gives the GSLW Thm 58-style statement `cosCircuit_apply`:
  *every* eigenvector `ψᵢ` (no spectral gap is needed, unlike the sign function) is mapped by the
  compressed circuit to `(cos (2ςᵢ) / ‖c‖₁) ψᵢ` up to an error of norm `≤ 10⁻⁶ / ‖c‖₁`, and to a
  vector of norm `≤ 1 / ‖c‖₁` (`cosCircuit_apply_norm_le`).
* Resources: `routeA_queries 11 = 55` uses of `U`/`U†` (`cosCircuit_queries`); the phase-based
  Route B would use the optimal `deg p = 10` queries and one ancilla qubit.
* The same example through the IR (IR-1/2): `cosExpr = chebLCU c₀ (c₁, …, c₁₀) oracle` has
  `spec cosExpr = cos2Poly.toPoly`, `scale cosExpr = cosL1`, `queries cosExpr = 55`,
  `ancillaDim cosExpr = 11`, and the soundness theorem gives `base_cosExpr`.

## Towards the full `e^{-itA}` (follow-up)

The imaginary part `-sin (tx)` is an odd function whose Jacobi–Anger expansion
`sin (tx) = 2 ∑_{k ≥ 0} (-1)^k J_{2k+1}(t) T_{2k+1}(x)` is handled identically (an odd `PolyQ`,
the same certificates with `Real.sin`, the same Route A circuit).  Combining the two parts into
one block encoding of `cos (tA) − i sin (tA)` needs the complex-coefficient LCU `lcu_complex`
(CERT-A) with the coefficient list `(c_k) ∪ (-i s_k)`; this is a follow-up (APP-4 proper), as is
the phase-based Route B implementation.

All kernel computations (`decide +kernel` on `ofMonomials` of a degree-10 polynomial with
`30`-digit decimal coefficients) take about a second in total; nothing here uses `native_decide`,
so every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`test/QSVTTest/CosExample.lean`).
-/

namespace QSVT.Examples

open QSVT.Pipeline QSVT.Certificate QSVT.SVT QSVT.Poly QSVT.Encoding QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The input: `cos2Poly` and its Chebyshev coefficients -/

/-- APP-4. The degree-10 approximation `cos2Poly` of `cos (2x)` (CERT-B) as a polynomial with
Gaussian-rational coefficients in the monomial basis (all imaginary parts zero). -/
def cosPoly : PolyQC := PolyQ.toPolyQC cos2Poly

/-- APP-4. The Chebyshev coefficients `c` of `cos2Poly = ∑ₖ cₖ T_k`, computed by POLY-6
`ChebQC.ofMonomials`: `11` entries, the odd ones zero (the exact list is checked in the tests). -/
abbrev cosCheb : ChebQC := ChebQC.ofMonomials cosPoly

/-- APP-4. The register dimension `m = 11` (one Chebyshev coefficient per degree `0, …, 10`),
reproved by the kernel. -/
theorem cosCheb_length : cosCheb.length = 11 := by decide +kernel

/-- APP-4. The register dimension is nonzero (the hypothesis of `regTopLeft` and `routeA`). -/
instance cosCheb_neZero : NeZero cosCheb.length := ⟨by rw [cosCheb_length]; norm_num⟩

/-- APP-4. All Chebyshev coefficients of `cos2Poly` are real, reproved by the kernel. -/
theorem cosCheb_im_eq_zero : ∀ z ∈ cosCheb, z.2 = 0 := by decide +kernel

/-- APP-4. The subnormalisation of the Route A circuit: the `ℓ¹` norm `‖c‖₁ = ∑ₖ |cₖ|` of the
Chebyshev coefficients of `cos2Poly` (`= p(0) = 1 − 3.9 · 10⁻⁹`, exactly `cosL1_eq`). -/
noncomputable def cosL1 : ℝ := l1 (chebCoeffs cosPoly)

/-- APP-4. The exact value of `ChebQC.l1Bound cosCheb` (a kernel evaluation): the constant
coefficient `p(0)` of `cos2Poly`,
`62499999757066272271938848645232619 / 62500000000000000000000000000000000`. -/
theorem l1Bound_cosCheb :
    ChebQC.l1Bound cosCheb =
      62499999757066272271938848645232619 / 62500000000000000000000000000000000 := by
  decide +kernel

/-- APP-4. The exact subnormalisation `‖c‖₁ = p(0) = 1 − 3.9 · 10⁻⁹`. -/
theorem cosL1_eq :
    cosL1 =
      ((62499999757066272271938848645232619 / 62500000000000000000000000000000000 : ℚ) : ℝ) := by
  rw [cosL1, l1_eq_l1Bound_of_real cosPoly cosCheb_im_eq_zero, l1Bound_cosCheb]

/-- APP-4. `‖c‖₁ > 0`. -/
theorem cosL1_pos : 0 < cosL1 := by
  rw [cosL1_eq]
  norm_num

/-- APP-4. Decimal bounds `0.9999999 ≤ ‖c‖₁ ≤ 1`. -/
theorem cosL1_mem_Icc : cosL1 ∈ Set.Icc (0.9999999 : ℝ) 1 := by
  rw [cosL1_eq]
  constructor <;> norm_num

theorem norm_inv_cosL1 : ‖((cosL1 : ℂ)⁻¹)‖ = cosL1⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg cosL1_pos.le]

/-! ### The implementation: the Route A circuit -/

section Circuit

variable (E : HermitianEncoding ℋ)

/-- APP-4. The circuit: the Route A unitary of CERT-A for the Chebyshev coefficients of
`cos2Poly`, an `11`-term LCU of the Chebyshev unitaries `U_{chebPhases k}` (`k < 11`) on the
register `Reg 11 ℋ`, using `55` queries to `U`/`U†` (`cosCircuit_queries`). -/
noncomputable def cosCircuit : L (Reg cosCheb.length ℋ) := chebLCU E (chebCoeffs cosPoly)

/-- APP-4. The circuit is unitary. -/
theorem cosCircuit_mem_unitary : cosCircuit E ∈ unitary (L (Reg cosCheb.length ℋ)) :=
  chebLCU_mem_unitary E _

/-- APP-4 (exact implementation). The `(0,0)` block of the compressed circuit is
`‖c‖₁⁻¹ • p(A) Π` for `p = cos2Poly`, with zero error:
```
(⟨0| ⊗ Π) cosCircuit E (|0⟩ ⊗ Π) = cosL1⁻¹ • (cos2Poly(A) Π).
```
-/
theorem cosCircuit_topLeft :
    regTopLeft (regP E * cosCircuit E * regP E) =
      ((cosL1 : ℂ)⁻¹) • (aeval E.encoded cos2Poly.toPoly * E.P) :=
  routeA E cosPoly cosL1_pos.ne'

variable (i : Fin (Module.finrank ℂ (rangeP E)))

/-- APP-4. On an eigenvector `ψᵢ` of `A` with eigenvalue `ςᵢ`, the compressed circuit acts as
the scalar `‖c‖₁⁻¹ · p(ςᵢ)` (SVT-3 `aeval_eigenVec`). -/
theorem cosCircuit_apply_eigenVec :
    regTopLeft (regP E * cosCircuit E * regP E) (eigenVec E i) =
      ((cosL1 : ℂ)⁻¹ * cos2Poly.toPoly.eval (eigenValue E i : ℂ)) • eigenVec E i := by
  rw [cosCircuit_topLeft, LinearMap.smul_apply, Module.End.mul_apply, P_eigenVec,
    aeval_eigenVec, smul_smul]

/-- APP-4 (certified behaviour; GSLW Thm 58 style, real part). Every eigenvector `ψᵢ` of `A`
(eigenvalue `ςᵢ ∈ [-1, 1]`, no gap needed) is mapped by the compressed circuit to
`(cos (2ςᵢ) / ‖c‖₁) ψᵢ`, up to an error of norm at most `10⁻⁶ / ‖c‖₁ ≈ 10⁻⁶`. -/
theorem cosCircuit_apply :
    ‖regTopLeft (regP E * cosCircuit E * regP E) (eigenVec E i) -
        ((Real.cos (2 * eigenValue E i) / cosL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ 0.000001 / cosL1 := by
  have hcert := norm_eval_cos2Poly_sub_cos_le _ (eigenValue_mem_Icc E i)
  have hvec : regTopLeft (regP E * cosCircuit E * regP E) (eigenVec E i) -
      ((Real.cos (2 * eigenValue E i) / cosL1 : ℝ) : ℂ) • eigenVec E i =
      ((cosL1 : ℂ)⁻¹ * (cos2Poly.toPoly.eval (eigenValue E i : ℂ) -
        ((Real.cos (2 * eigenValue E i) : ℝ) : ℂ))) • eigenVec E i := by
    rw [cosCircuit_apply_eigenVec, ← sub_smul, Complex.ofReal_div, div_eq_inv_mul, mul_sub]
  rw [hvec, norm_smul, norm_mul, norm_inv_cosL1, norm_eigenVec, mul_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hcert (inv_nonneg.mpr cosL1_pos.le)

/-- APP-4 (global bound). The compressed circuit maps every eigenvector `ψᵢ` to a vector of norm
at most `1 / ‖c‖₁ ≈ 1`, from the admissibility certificate `‖cos2Poly‖_∞ ≤ 1`. -/
theorem cosCircuit_apply_norm_le :
    ‖regTopLeft (regP E * cosCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / cosL1 := by
  rw [cosCircuit_apply_eigenVec, norm_smul, norm_mul, norm_inv_cosL1, norm_eigenVec, mul_one,
    one_div]
  have h : ‖cos2Poly.toPoly.eval (eigenValue E i : ℂ)‖ ≤ 1 :=
    (norm_eval_le_supNorm _ (eigenValue_mem_Icc E i)).trans supNorm_cos2Poly_le_one
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr cosL1_pos.le)).trans_eq (mul_one _)

end Circuit

/-! ### Resources -/

/-- APP-4. The query count of the circuit: `∑_{k<11} k = 55` uses of `U`/`U†`. The phase-based
Route B (QSVT with `10` phases) would use the optimal `deg p = 10` queries and one ancilla qubit;
Route A uses `55 = 5.5 · 10` queries and an `11`-dimensional ancilla register (`⌈log₂ 11⌉ = 4`
qubits) but needs no phase-finding. -/
theorem cosCircuit_queries : routeA_queries cosCheb.length = 55 := by
  rw [cosCheb_length, routeA_queries_eq]

/-! ### The same example through the IR (IR-1/2) -/

section IR

open QSVT.IR

/-- APP-4. The real parts of the Chebyshev coefficients, as rationals. -/
def cosChebQ : List ℚ := cosCheb.map Prod.fst

/-- APP-4. The leading Chebyshev coefficient `c₀ = J₀(2)` (rounded to 30 digits). -/
def cosChebQ0 : ℚ := 4477815582824713361036549093 / 20000000000000000000000000000

/-- APP-4. The IR program: one Route A node with the Chebyshev coefficients of `cos2Poly`
(leading coefficient `c₀`, then the remaining `10`) applied to the oracle. -/
def cosExpr : Expr := .chebLCU cosChebQ0 cosChebQ.tail .oracle

theorem cosChebQ_tail_length : cosChebQ.tail.length = 10 := by decide +kernel

/-- APP-4. The coefficient list of `cosExpr` is `cosCheb` (kernel check). -/
theorem map_cosChebQ :
    (cosChebQ0 :: cosChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = cosCheb := by
  decide +kernel

/-- APP-4. The specification polynomial of `cosExpr` is `cos2Poly`. -/
theorem spec_cosExpr : spec cosExpr = cos2Poly.toPoly := by
  rw [cosExpr, spec_chebLCU, normSpec_oracle, comp_X, chebPoly_eq_toPoly, map_cosChebQ,
    ChebQC.toPoly_ofMonomials]
  rfl

/-- APP-4. The subnormalisation of `cosExpr` is `‖c‖₁ = cosL1`. -/
theorem scale_cosExpr : scale cosExpr = cosL1 := by
  have h : ((cosChebQ0 :: cosChebQ.tail).map fun q : ℚ => |q|).sum =
      62499999757066272271938848645232619 / 62500000000000000000000000000000000 := by
    decide +kernel
  rw [cosExpr, scale_chebLCU, chebScale, cosL1_eq, ← h, Rat.cast_list_sum, List.map_map]
  simp [Function.comp_def, Rat.cast_abs]

/-- APP-4. `cosExpr` is well scaled. -/
theorem cosExpr_wellScaled : WellScaled cosExpr := by
  refine ⟨?_, trivial⟩
  have h : scale cosExpr ≠ 0 := by
    rw [scale_cosExpr]
    exact cosL1_pos.ne'
  exact h

/-- APP-4 (through the IR soundness theorem). The base block of `cosExpr` is
`‖c‖₁⁻¹ • cos2Poly(A₀) Π`, the same operator as `cosCircuit_topLeft`. -/
theorem base_cosExpr (E₀ : HermitianEncoding ℋ) :
    base E₀ cosExpr = ((cosL1 : ℂ)⁻¹) • (aeval E₀.encoded cos2Poly.toPoly * E₀.P) := by
  rw [base_eq_smul E₀ cosExpr_wellScaled, scale_cosExpr, spec_cosExpr]

/-- APP-4. `cosExpr` uses `55` oracle queries (IR-2). -/
theorem queries_cosExpr : queries cosExpr = 55 := by
  rw [cosExpr, queries_chebLCU_eq_routeA, cosChebQ_tail_length, queries_oracle, mul_one,
    routeA_queries_eq]

/-- APP-4. The ancilla of `cosExpr` is the `11`-dimensional register (IR-2). -/
theorem ancillaDim_cosExpr : ancillaDim cosExpr = 11 := by
  rw [cosExpr, ancillaDim_chebLCU, cosChebQ_tail_length, ancillaDim_oracle]

end IR

end QSVT.Examples
