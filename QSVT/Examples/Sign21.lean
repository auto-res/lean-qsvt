/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.Sign21
import QSVT.Pipeline.ChebLCU
import QSVT.IR.Sound
import QSVT.IR.Cost

/-!
# APP-1 (lite): a certified sign-function transformation implemented by Route A

The first end-to-end application of the library (formal-spec APP-1, GSLW Thm 26 "singular vector
transformation", restricted to the Hermitian/eigenvector case). The ingredients are composed as
follows.

* The polynomial is the degree-21 odd approximation `sign21 : PolyQ` of `c · sign x`,
  `c = sign21Scale ≈ 0.8924`, with the kernel-checked LeanCert certificates of CERT-B:
  `‖p‖_∞ ≤ 1` and `|p(x) − c| ≤ 0.0236` on `[0.15, 1]` (mirror on `[-1, -0.15]`).
* Its Chebyshev coefficients `signCheb = ChebQC.ofMonomials signPoly` are *computed* inside Lean
  (POLY-6); the list has `22` entries (`signCheb_length`), all real (`signCheb_im_eq_zero`), both
  facts reproved by the kernel with `decide +kernel`.
* The circuit is Route A (CERT-A): `signCircuit E = chebLCU E (chebCoeffs signPoly)`, the
  `22`-term LCU of the closed-form Chebyshev unitaries `U_{chebPhases k}`, acting on the register
  `Reg 22 ℋ` (a `22`-dimensional ancilla, `⌈log₂ 22⌉ = 5` qubits). It implements `p(A)` *exactly*
  up to the subnormalisation `‖c‖₁ = signL1` (`signCircuit_topLeft`), and
  `signL1 = 159582649048909303 / 72057594037927936 ≈ 2.2147` exactly (`signL1_eq`, by
  `l1_eq_l1Bound_of_real` and a kernel evaluation of `ChebQC.l1Bound`).
* On the eigenbasis of `A` (SVT-3, `QSVT.SVT.EigenBasis`) this gives the GSLW Thm 26-style
  statement `signCircuit_apply_pos`/`signCircuit_apply_neg`: every eigenvector `ψᵢ` with
  eigenvalue `|ςᵢ| ≥ 0.15` is mapped by the compressed circuit to
  `± (sign21Scale / signL1) ψᵢ ≈ ± 0.4029 ψᵢ` up to an error of norm `≤ 0.0236 / signL1 ≈ 0.0107`,
  and every eigenvector is mapped to a vector of norm `≤ 1 / signL1 ≈ 0.4515`
  (`signCircuit_apply_norm_le`).
* Resources: `routeA_queries 22 = 231` uses of `U`/`U†` (`signCircuit_queries`). The phase-based
  Route B (QSVT with the phases of CERT-B part 2, pending) would use the optimal `21 = deg p`
  queries and a single ancilla qubit; Route A trades a factor `11` in queries and `⌈log₂ 22⌉ = 5`
  ancilla qubits for an implementation without any phase-finding.
* The same example through the IR (IR-1/2): `signExpr = chebLCU 0 (tail of the real parts) oracle`
  has `spec signExpr = sign21.toPoly`, `scale signExpr = signL1`, `queries signExpr = 231`,
  `ancillaDim signExpr = 22`, and the soundness theorem gives `base_signExpr`.

All kernel computations (`decide +kernel` on `ofMonomials` of a degree-21 polynomial with
dyadic coefficients of about `60` bits) take well under a second each; nothing here uses
`native_decide`, so every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`
(audited in `test/QSVTTest/Examples.lean`).

## Mathlib API used

`Fin.sum_univ_eq_sum_range`, `List.getD_eq_getElem`, `List.getElem_mem`, `List.getElem_map`,
`List.get_eq_getElem`, `Rat.cast_sum`, `Rat.cast_list_sum`, `Rat.cast_abs`,
`Complex.norm_ratCast`, `Complex.ofReal_div`, `Complex.norm_real`, `norm_inv`, `norm_smul`,
`mul_le_mul_of_nonneg_left`.
-/

namespace QSVT.Examples

open QSVT.Pipeline QSVT.Certificate QSVT.SVT QSVT.Poly QSVT.Encoding QuantumState
open Polynomial
-- Only `T` is opened: `Polynomial.Chebyshev.C` (third kind) would shadow `Polynomial.C`.
open Polynomial.Chebyshev (T)

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The input: `sign21` and its Chebyshev coefficients -/

/-- APP-1. The degree-21 sign approximation `sign21` (CERT-B) as a polynomial with
Gaussian-rational coefficients in the monomial basis (all imaginary parts zero). -/
def signPoly : PolyQC := PolyQ.toPolyQC sign21

/-- APP-1. The Chebyshev coefficients `c` of `sign21 = ∑ₖ cₖ T_k`, computed by POLY-6
`ChebQC.ofMonomials`: `22` entries, the even ones zero (the exact list is checked in the tests). -/
abbrev signCheb : ChebQC := ChebQC.ofMonomials signPoly

/-- APP-1. The register dimension `m = 22` (one Chebyshev coefficient per degree `0, …, 21`),
reproved by the kernel. -/
theorem signCheb_length : signCheb.length = 22 := by decide +kernel

/-- APP-1. The register dimension is nonzero (the hypothesis of `regTopLeft` and `routeA`). -/
instance signCheb_neZero : NeZero signCheb.length := ⟨by rw [signCheb_length]; norm_num⟩

/-- APP-1. All Chebyshev coefficients of `sign21` are real, reproved by the kernel. -/
theorem signCheb_im_eq_zero : ∀ z ∈ signCheb, z.2 = 0 := by decide +kernel

/-- APP-1 (helper). For a polynomial whose Chebyshev coefficients are all real, the `ℓ¹` norm
`l1 (chebCoeffs l)` of CERT-A equals the computable rational `ChebQC.l1Bound` of POLY-6
(in general only `l1 ≤ l1Bound`, `ChebQC.l1_le_l1Bound`). -/
theorem l1_eq_l1Bound_of_real (l : PolyQC) (h : ∀ z ∈ ChebQC.ofMonomials l, z.2 = 0) :
    l1 (chebCoeffs l) = (ChebQC.l1Bound (ChebQC.ofMonomials l) : ℝ) := by
  rw [ChebQC.l1Bound, QC.sum_map_eq_sum_range, Rat.cast_sum]
  change ∑ k : Fin (ChebQC.ofMonomials l).length,
    ‖QC.toC ((ChebQC.ofMonomials l).getD k 0)‖ = _
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖QC.toC ((ChebQC.ofMonomials l).getD k 0)‖)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (ChebQC.ofMonomials l).length := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem _ _ hk']
  have h0 := h _ (List.getElem_mem hk')
  simp only [QC.toC, h0]
  simp [Complex.norm_ratCast, Rat.cast_abs]

/-- APP-1. The subnormalisation of the Route A circuit: the `ℓ¹` norm `‖c‖₁ = ∑ₖ |cₖ|` of the
Chebyshev coefficients of `sign21` (`≈ 2.2147`, exactly `signL1_eq`). -/
noncomputable def signL1 : ℝ := l1 (chebCoeffs signPoly)

/-- APP-1. The exact value of `ChebQC.l1Bound signCheb` (a kernel evaluation):
`159582649048909303 / 72057594037927936 ≈ 2.2147`. -/
theorem l1Bound_signCheb : ChebQC.l1Bound signCheb = 159582649048909303 / 72057594037927936 := by
  decide +kernel

/-- APP-1. The exact subnormalisation `‖c‖₁ = 159582649048909303 / 72057594037927936 ≈ 2.2147`. -/
theorem signL1_eq : signL1 = ((159582649048909303 / 72057594037927936 : ℚ) : ℝ) := by
  rw [signL1, l1_eq_l1Bound_of_real signPoly signCheb_im_eq_zero, l1Bound_signCheb]

/-- APP-1. `‖c‖₁ > 0`. -/
theorem signL1_pos : 0 < signL1 := by
  rw [signL1_eq]
  norm_num

/-- APP-1. Decimal bounds `2.2146 ≤ ‖c‖₁ ≤ 2.2147`. -/
theorem signL1_mem_Icc : signL1 ∈ Set.Icc (2.2146 : ℝ) 2.2147 := by
  rw [signL1_eq]
  constructor <;> norm_num

theorem norm_inv_signL1 : ‖((signL1 : ℂ)⁻¹)‖ = signL1⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg signL1_pos.le]

/-! ### The implementation: the Route A circuit -/

section Circuit

variable (E : HermitianEncoding ℋ)

/-- APP-1. The circuit: the Route A unitary of CERT-A for the Chebyshev coefficients of
`sign21`, a `22`-term LCU of the Chebyshev unitaries `U_{chebPhases k}` (`k < 22`) on the
register `Reg 22 ℋ`, using `231` queries to `U`/`U†` (`signCircuit_queries`). -/
noncomputable def signCircuit : L (Reg signCheb.length ℋ) := chebLCU E (chebCoeffs signPoly)

/-- APP-1. The circuit is unitary. -/
theorem signCircuit_mem_unitary : signCircuit E ∈ unitary (L (Reg signCheb.length ℋ)) :=
  chebLCU_mem_unitary E _

/-- APP-1 (exact implementation). The `(0,0)` block of the compressed circuit is
`‖c‖₁⁻¹ • p(A) Π` for `p = sign21`, with zero error:
```
(⟨0| ⊗ Π) signCircuit E (|0⟩ ⊗ Π) = signL1⁻¹ • (sign21(A) Π).
```
-/
theorem signCircuit_topLeft :
    regTopLeft (regP E * signCircuit E * regP E) =
      ((signL1 : ℂ)⁻¹) • (aeval E.encoded sign21.toPoly * E.P) :=
  routeA E signPoly signL1_pos.ne'

variable (i : Fin (Module.finrank ℂ (rangeP E)))

/-- APP-1. On an eigenvector `ψᵢ` of `A` with eigenvalue `ςᵢ`, the compressed circuit acts as
the scalar `‖c‖₁⁻¹ · p(ςᵢ)` (SVT-3 `aeval_eigenVec`). -/
theorem signCircuit_apply_eigenVec :
    regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i) =
      ((signL1 : ℂ)⁻¹ * sign21.toPoly.eval (eigenValue E i : ℂ)) • eigenVec E i := by
  rw [signCircuit_topLeft, LinearMap.smul_apply, Module.End.mul_apply, P_eigenVec,
    aeval_eigenVec, smul_smul]

/-- APP-1 (certified behaviour, positive spectrum; GSLW Thm 26 style). Every eigenvector `ψᵢ`
of `A` with eigenvalue `ςᵢ ≥ 0.15` is mapped by the compressed circuit to
`(sign21Scale / ‖c‖₁) ψᵢ ≈ 0.4029 ψᵢ`, up to an error of norm at most
`0.0236 / ‖c‖₁ ≈ 0.0107`. -/
theorem signCircuit_apply_pos (hi : 0.15 ≤ eigenValue E i) :
    ‖regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i) -
        (((sign21Scale : ℝ) / signL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ 0.0236 / signL1 := by
  have hx : eigenValue E i ∈ Set.Icc (0.15 : ℝ) 1 := ⟨hi, (eigenValue_mem_Icc E i).2⟩
  have hcert := norm_eval_sign21_sub_scale_le _ hx
  have hvec : regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i) -
      (((sign21Scale : ℝ) / signL1 : ℝ) : ℂ) • eigenVec E i =
      ((signL1 : ℂ)⁻¹ * (sign21.toPoly.eval (eigenValue E i : ℂ) - ((sign21Scale : ℝ) : ℂ))) •
        eigenVec E i := by
    rw [signCircuit_apply_eigenVec, ← sub_smul, Complex.ofReal_div, div_eq_inv_mul, mul_sub]
  rw [hvec, norm_smul, norm_mul, norm_inv_signL1, norm_eigenVec, mul_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hcert (inv_nonneg.mpr signL1_pos.le)

/-- APP-1 (certified behaviour, negative spectrum). Every eigenvector `ψᵢ` of `A` with
eigenvalue `ςᵢ ≤ -0.15` is mapped to `-(sign21Scale / ‖c‖₁) ψᵢ ≈ -0.4029 ψᵢ`, up to an error of
norm at most `0.0236 / ‖c‖₁ ≈ 0.0107`. -/
theorem signCircuit_apply_neg (hi : eigenValue E i ≤ -0.15) :
    ‖regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i) -
        ((-(sign21Scale : ℝ) / signL1 : ℝ) : ℂ) • eigenVec E i‖ ≤ 0.0236 / signL1 := by
  have hx : eigenValue E i ∈ Set.Icc (-1 : ℝ) (-0.15) := ⟨(eigenValue_mem_Icc E i).1, hi⟩
  have hcert := norm_eval_sign21_add_scale_le _ hx
  have hvec : regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i) -
      ((-(sign21Scale : ℝ) / signL1 : ℝ) : ℂ) • eigenVec E i =
      ((signL1 : ℂ)⁻¹ * (sign21.toPoly.eval (eigenValue E i : ℂ) + ((sign21Scale : ℝ) : ℂ))) •
        eigenVec E i := by
    rw [signCircuit_apply_eigenVec, ← sub_smul, Complex.ofReal_div, Complex.ofReal_neg,
      div_eq_inv_mul, mul_neg, sub_neg_eq_add, mul_add]
  rw [hvec, norm_smul, norm_mul, norm_inv_signL1, norm_eigenVec, mul_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hcert (inv_nonneg.mpr signL1_pos.le)

/-- APP-1 (global bound). The compressed circuit maps every eigenvector `ψᵢ` (any eigenvalue in
`[-1, 1]`) to a vector of norm at most `1 / ‖c‖₁ ≈ 0.4515`, from the admissibility certificate
`‖sign21‖_∞ ≤ 1`. -/
theorem signCircuit_apply_norm_le :
    ‖regTopLeft (regP E * signCircuit E * regP E) (eigenVec E i)‖ ≤ 1 / signL1 := by
  rw [signCircuit_apply_eigenVec, norm_smul, norm_mul, norm_inv_signL1, norm_eigenVec, mul_one,
    one_div]
  have h : ‖sign21.toPoly.eval (eigenValue E i : ℂ)‖ ≤ 1 :=
    (norm_eval_le_supNorm _ (eigenValue_mem_Icc E i)).trans supNorm_sign21_le_one
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr signL1_pos.le)).trans_eq (mul_one _)

end Circuit

/-! ### Resources -/

/-- APP-1. The query count of the circuit: `∑_{k<22} k = 231` uses of `U`/`U†`. For comparison,
the phase-based Route B (QSVT with the `21` phases of CERT-B part 2, pending) uses the optimal
`deg p = 21` queries and one ancilla qubit, whereas Route A uses `231 = 11 · 21` queries and a
`22`-dimensional ancilla register (`⌈log₂ 22⌉ = 5` qubits) but needs no phase-finding. -/
theorem signCircuit_queries : routeA_queries signCheb.length = 231 := by
  rw [signCheb_length, routeA_queries_eq]

/-! ### The same example through the IR (IR-1/2) -/

section IR

open QSVT.IR

/-- APP-1. The real parts of the Chebyshev coefficients, as rationals. -/
def signChebQ : List ℚ := signCheb.map Prod.fst

/-- APP-1. The IR program: one Route A node with the Chebyshev coefficients of `sign21`
(leading coefficient `c₀ = 0`, then the remaining `21`) applied to the oracle. -/
def signExpr : Expr := .chebLCU 0 signChebQ.tail .oracle

theorem signChebQ_tail_length : signChebQ.tail.length = 21 := by decide +kernel

/-- APP-1. The coefficient list of `signExpr` is `signCheb` (kernel check). -/
theorem map_signChebQ : (0 :: signChebQ.tail).map (fun q : ℚ => ((q, 0) : QC)) = signCheb := by
  decide +kernel

/-- APP-1 (helper). The polynomial of a `chebLCU c₀ c` node is the `ChebQC.toPoly` of the
real coefficient list `c₀ :: c`. -/
theorem chebPoly_eq_toPoly (c₀ : ℚ) (c : List ℚ) :
    chebPoly c₀ c = ChebQC.toPoly ((c₀ :: c).map fun q : ℚ => ((q, 0) : QC)) := by
  have hterm : ∀ k : Fin (c.length + 1), C (chebCoeffC c₀ c k) * T ℂ (k : ℕ) =
      C (QC.toC (((c₀ :: c).map fun q : ℚ => ((q, 0) : QC)).getD k 0)) * T ℂ (k : ℕ) := by
    intro k
    congr 2
    rw [chebCoeffC, chebCoeff, List.get_eq_getElem,
      List.getD_eq_getElem _ _ (by simpa using k.isLt), List.getElem_map, PolyQ.toC_mk_zero]
  rw [chebPoly, ChebQC.toPoly, List.length_map, List.length_cons]
  simp only [hterm]
  exact Fin.sum_univ_eq_sum_range
    (fun k => C (QC.toC (((c₀ :: c).map fun q : ℚ => ((q, 0) : QC)).getD k 0)) * T ℂ k) _

/-- APP-1. The specification polynomial of `signExpr` is `sign21`. -/
theorem spec_signExpr : spec signExpr = sign21.toPoly := by
  rw [signExpr, spec_chebLCU, normSpec_oracle, comp_X, chebPoly_eq_toPoly, map_signChebQ,
    ChebQC.toPoly_ofMonomials]
  rfl

/-- APP-1. The subnormalisation of `signExpr` is `‖c‖₁ = signL1`. -/
theorem scale_signExpr : scale signExpr = signL1 := by
  have h : ((0 :: signChebQ.tail).map fun q : ℚ => |q|).sum =
      159582649048909303 / 72057594037927936 := by
    decide +kernel
  rw [signExpr, scale_chebLCU, chebScale, signL1_eq, ← h, Rat.cast_list_sum, List.map_map]
  simp [Function.comp_def, Rat.cast_abs]

/-- APP-1. `signExpr` is well scaled. -/
theorem signExpr_wellScaled : WellScaled signExpr := by
  refine ⟨?_, trivial⟩
  have h : scale signExpr ≠ 0 := by
    rw [scale_signExpr]
    exact signL1_pos.ne'
  exact h

/-- APP-1 (through the IR soundness theorem). The base block of `signExpr` is
`‖c‖₁⁻¹ • sign21(A₀) Π`, the same operator as `signCircuit_topLeft`. -/
theorem base_signExpr (E₀ : HermitianEncoding ℋ) :
    base E₀ signExpr = ((signL1 : ℂ)⁻¹) • (aeval E₀.encoded sign21.toPoly * E₀.P) := by
  rw [base_eq_smul E₀ signExpr_wellScaled, scale_signExpr, spec_signExpr]

/-- APP-1. `signExpr` uses `231` oracle queries (IR-2). -/
theorem queries_signExpr : queries signExpr = 231 := by
  rw [signExpr, queries_chebLCU_eq_routeA, signChebQ_tail_length, queries_oracle, mul_one,
    routeA_queries_eq]

/-- APP-1. The ancilla of `signExpr` is the `22`-dimensional register (IR-2). -/
theorem ancillaDim_signExpr : ancillaDim signExpr = 22 := by
  rw [signExpr, ancillaDim_chebLCU, signChebQ_tail_length, ancillaDim_oracle]

end IR

end QSVT.Examples
