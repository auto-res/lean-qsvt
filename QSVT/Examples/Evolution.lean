/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Certificate.SinExample
import QSVT.Examples.CosEvolution

/-!
# APP-4: Hamiltonian simulation `e^{-2iA}` by Route A with complex Chebyshev coefficients

The polynomial step of GSLW Thm 58 ("Hamiltonian simulation") for the evolution time `t = 2`,
restricted to the Hermitian/eigenvector case: for a Hermitian block encoding `E` of `A`
(eigenvalues in `[-1, 1]`) the target `e^{-itA} = cos (tA) − i sin (tA)` is approximated by the
Jacobi–Anger truncations of its real and imaginary parts, certified separately in
`QSVT.Certificate.CosExample` (`cos2Poly`, degree `10`) and `QSVT.Certificate.SinExample`
(`sin2Poly`, degree `11`), and the *complex* polynomial `p = cos2Poly − i · sin2Poly` is
implemented exactly by the Route A circuit of CERT-A, whose coefficient layer
(`chebEncoding`, `routeA`) is already complex.  Not included are the amplitude-amplification and
renormalisation steps of GSLW Thm 58 (which remove the `1/‖c‖₁` subnormalisation): the block
implemented here is `e^{-2iA} / ‖c‖₁` on the spectrum of `A`, up to `2ε / ‖c‖₁`.

* The input is `evoPoly : PolyQC`, the Gaussian-rational coefficient list `(cₖ, −sₖ)` of
  `cos2Poly − i · sin2Poly` (`12` entries, `evoPoly_toPoly`), with the pointwise certificate
  `norm_eval_evoPoly_sub_exp_le : ‖p(x) − e^{-2ix}‖ ≤ 2ε` on `[-1, 1]`, `ε = 10⁻⁶`, from the two
  real certificates and `e^{-2ix} = cos 2x − i sin 2x` (`Complex.exp_mul_I`).
* Its Chebyshev coefficients `evoCheb = ChebQC.ofMonomials evoPoly` are *computed* inside Lean
  (POLY-6): `12` entries (`evoCheb_length`), real at even and purely imaginary at odd degrees
  (`evoCheb_axis`), reproved by the kernel with `decide +kernel`.  Because every coefficient lies
  on a coordinate axis, `‖c‖₁ = ∑ₖ ‖cₖ‖` equals the computable `ChebQC.l1Bound` exactly
  (`l1_eq_l1Bound_of_axis`, the complex analogue of `l1_eq_l1Bound_of_real`), giving the exact
  subnormalisation `evoL1 = cosL1 + ‖s‖₁ ≈ 2.4258` (`evoL1_eq`, `evoL1_mem_Icc`).
* The circuit is Route A (CERT-A): `evoCircuit E = chebLCU E (chebCoeffs evoPoly)`, the
  `12`-term LCU of the closed-form Chebyshev unitaries `U_{chebPhases k}` with the complex phases
  of `cₖ / ‖c‖₁` absorbed into the unitaries, on the register `Reg 12 ℋ` (`⌈log₂ 12⌉ = 4` ancilla
  qubits); packaged as the projected unitary encoding `evoEncoding E` (not a Hermitian encoding:
  `p(A)` is not self-adjoint).  It implements `p(A)` *exactly* up to the subnormalisation `‖c‖₁`
  (`evoCircuit_topLeft`).
* On the eigenbasis of `A` (SVT-3) this gives the GSLW Thm 58-style statement `evoCircuit_apply`:
  *every* eigenvector `ψᵢ` (no spectral gap needed) is mapped by the compressed circuit to
  `(e^{-2iςᵢ} / ‖c‖₁) ψᵢ` up to an error of norm `≤ 2ε / ‖c‖₁ ≈ 8.2 · 10⁻⁷`, and to a vector of
  norm `≤ (1 + 2ε) / ‖c‖₁` (`evoCircuit_apply_norm_le`).
* Resources: `routeA_queries 12 = 66` uses of `U`/`U†` (`evoCircuit_queries`); the phase-based
  Route B would use the optimal `deg p = 11` queries and one ancilla qubit, but needs complex QSP
  phases (not yet available).

## Follow-ups

* The IR (`QSVT.IR.Expr.chebLCU`) takes *real* coefficient lists (`List ℚ`), so this example has
  no IR counterpart yet; extending the IR to Gaussian-rational coefficients (`QC`) would make
  `spec`/`scale`/`queries` available for `evoPoly` as for `cosExpr`.
* GSLW Thm 58 proper: remove the `1/‖c‖₁` with amplitude amplification (or implement the real
  and imaginary parts with one ancilla each by Route B and combine them by an LCU of two terms).

All kernel computations (`decide +kernel` on `ofMonomials` of a degree-11 polynomial with
`30`-digit decimal coefficients) take about a second in total; nothing here uses `native_decide`,
so every theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited in
`test/QSVTTest/Evolution.lean`).

## Mathlib API used

`Complex.exp_mul_I`, `Complex.cos_neg`, `Complex.sin_neg`, `Complex.ofReal_cos`,
`Complex.ofReal_sin`, `Complex.norm_exp_ofReal_mul_I`, `Complex.norm_I`, `norm_sub_le`,
`norm_add_le`, `Fin.sum_univ_eq_sum_range`, `List.getD_eq_getElem`, `List.getElem_mem`,
`Rat.cast_sum`, `Rat.cast_abs`, `Complex.norm_ratCast`, `map_neg`, `map_mul`.
-/

namespace QSVT.Examples

open QSVT.Pipeline QSVT.Certificate QSVT.SVT QSVT.Poly QSVT.Encoding QuantumState
open Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-! ### The input: `cos2Poly − i · sin2Poly` -/

/-- APP-4. The coefficient list of `−i · l` for a real coefficient list `l`: `(0, −lₖ)`. -/
def negIMul : PolyQ → PolyQC
  | [] => []
  | s :: l => ((0, -s) : QC) :: negIMul l

@[simp] theorem negIMul_nil : negIMul [] = [] := rfl

@[simp] theorem negIMul_cons (s : ℚ) (l : PolyQ) :
    negIMul (s :: l) = ((0, -s) : QC) :: negIMul l := rfl

/-- APP-4. `toPoly (negIMul l) = −i · toPoly l`. -/
theorem toPoly_negIMul (l : PolyQ) :
    PolyQC.toPoly (negIMul l) = -(C Complex.I * PolyQ.toPoly l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [negIMul_cons, PolyQC.toPoly_cons, ih, PolyQ.toPoly_cons]
    have h : QC.toC ((0, -a) : QC) = -((a : ℂ) * Complex.I) := by simp [QC.toC]
    rw [h, map_neg, map_mul]
    ring

/-- APP-4. The complex polynomial `cos2Poly − i · sin2Poly` as a Gaussian-rational coefficient
list in the monomial basis: the pairs `(cₖ, −sₖ)` (`12` entries; `cos2Poly` is padded with a zero
at degree `11`). -/
def evoPoly : PolyQC := QC.addList (PolyQ.toPolyQC cos2Poly) (negIMul sin2Poly)

/-- APP-4. `evoPoly` is the polynomial `cos2Poly − i · sin2Poly`. -/
theorem evoPoly_toPoly :
    PolyQC.toPoly evoPoly = cos2Poly.toPoly - C Complex.I * sin2Poly.toPoly := by
  rw [evoPoly, PolyQC.toPoly_addList, toPoly_negIMul, sub_eq_add_neg]
  rfl

/-- APP-4 (helper). `p(x) − e^{-2ix} = (cos2Poly(x) − cos 2x) − i (sin2Poly(x) − sin 2x)` at
real points, from `e^{-2ix} = cos 2x − i sin 2x`. -/
theorem eval_evoPoly_sub_exp (x : ℝ) :
    (PolyQC.toPoly evoPoly).eval (x : ℂ) - Complex.exp (-(2 * (x : ℂ)) * Complex.I) =
      (cos2Poly.toPoly.eval (x : ℂ) - ((Real.cos (2 * x) : ℝ) : ℂ)) -
        Complex.I * (sin2Poly.toPoly.eval (x : ℂ) - ((Real.sin (2 * x) : ℝ) : ℂ)) := by
  rw [evoPoly_toPoly, eval_sub, eval_mul, eval_C, Complex.exp_mul_I, Complex.cos_neg,
    Complex.sin_neg]
  push_cast
  ring

/-- APP-4 (certified input). `‖p(x) − e^{-2ix}‖ ≤ 2ε` on `[-1, 1]` with `ε = 10⁻⁶`, from the two
real certificates `norm_eval_cos2Poly_sub_cos_le` and `norm_eval_sin2Poly_sub_sin_le`. -/
theorem norm_eval_evoPoly_sub_exp_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(PolyQC.toPoly evoPoly).eval (x : ℂ) - Complex.exp (-(2 * (x : ℂ)) * Complex.I)‖ ≤
        2 * 0.000001 := by
  intro x hx
  rw [eval_evoPoly_sub_exp]
  have hc := norm_eval_cos2Poly_sub_cos_le x hx
  have hs := norm_eval_sin2Poly_sub_sin_le x hx
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  linarith

/-- APP-4. `‖p(x)‖ ≤ 1 + 2ε` on `[-1, 1]`, since `‖e^{-2ix}‖ = 1`. -/
theorem norm_eval_evoPoly_le :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(PolyQC.toPoly evoPoly).eval (x : ℂ)‖ ≤ 1 + 2 * 0.000001 := by
  intro x hx
  have h := norm_eval_evoPoly_sub_exp_le x hx
  have he : ‖Complex.exp (-(2 * (x : ℂ)) * Complex.I)‖ = 1 := by
    have := Complex.norm_exp_ofReal_mul_I (-(2 * x))
    push_cast at this
    exact this
  calc ‖(PolyQC.toPoly evoPoly).eval (x : ℂ)‖
      = ‖((PolyQC.toPoly evoPoly).eval (x : ℂ) - Complex.exp (-(2 * (x : ℂ)) * Complex.I)) +
          Complex.exp (-(2 * (x : ℂ)) * Complex.I)‖ := by rw [sub_add_cancel]
    _ ≤ ‖(PolyQC.toPoly evoPoly).eval (x : ℂ) - Complex.exp (-(2 * (x : ℂ)) * Complex.I)‖ +
          ‖Complex.exp (-(2 * (x : ℂ)) * Complex.I)‖ := norm_add_le _ _
    _ ≤ 2 * 0.000001 + 1 := add_le_add h he.le
    _ = 1 + 2 * 0.000001 := by ring

/-! ### The Chebyshev coefficients and the subnormalisation -/

/-- APP-4. The Chebyshev coefficients `c` of `evoPoly = ∑ₖ cₖ T_k`, computed by POLY-6
`ChebQC.ofMonomials`: `12` entries, real at even and purely imaginary at odd degrees (the exact
list is checked in the tests). -/
abbrev evoCheb : ChebQC := ChebQC.ofMonomials evoPoly

/-- APP-4. The register dimension `m = 12` (one Chebyshev coefficient per degree `0, …, 11`),
reproved by the kernel. -/
theorem evoCheb_length : evoCheb.length = 12 := by decide +kernel

/-- APP-4. The register dimension is nonzero (the hypothesis of `regTopLeft` and `routeA`). -/
instance evoCheb_neZero : NeZero evoCheb.length := ⟨by rw [evoCheb_length]; norm_num⟩

/-- APP-4. Every Chebyshev coefficient of `evoPoly` lies on a coordinate axis (real or purely
imaginary), reproved by the kernel. -/
theorem evoCheb_axis : ∀ z ∈ evoCheb, z.1 = 0 ∨ z.2 = 0 := by decide +kernel

/-- APP-4. For Chebyshev coefficients on the coordinate axes, the `ℓ¹` norm `∑ₖ ‖cₖ‖` of
`chebCoeffs l` is the computable bound `ChebQC.l1Bound (ofMonomials l) = ∑ₖ (|Re cₖ| + |Im cₖ|)`
exactly (the complex analogue of `l1_eq_l1Bound_of_real`). -/
theorem l1_eq_l1Bound_of_axis (l : PolyQC)
    (h : ∀ z ∈ ChebQC.ofMonomials l, z.1 = 0 ∨ z.2 = 0) :
    l1 (chebCoeffs l) = (ChebQC.l1Bound (ChebQC.ofMonomials l) : ℝ) := by
  rw [ChebQC.l1Bound, QC.sum_map_eq_sum_range, Rat.cast_sum]
  change ∑ k : Fin (ChebQC.ofMonomials l).length,
    ‖QC.toC ((ChebQC.ofMonomials l).getD k 0)‖ = _
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖QC.toC ((ChebQC.ofMonomials l).getD k 0)‖)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (ChebQC.ofMonomials l).length := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem _ _ hk']
  rcases h _ (List.getElem_mem hk') with h0 | h0
  · simp only [QC.toC, h0]
    simp [Complex.norm_ratCast, Rat.cast_abs]
  · simp only [QC.toC, h0]
    simp [Complex.norm_ratCast, Rat.cast_abs]

/-- APP-4. The subnormalisation of the Route A circuit: the `ℓ¹` norm `‖c‖₁ = ∑ₖ ‖cₖ‖` of the
Chebyshev coefficients of `evoPoly` (`= ‖c^{cos}‖₁ + ‖c^{sin}‖₁ ≈ 2.4258`, exactly `evoL1_eq`). -/
noncomputable def evoL1 : ℝ := l1 (chebCoeffs evoPoly)

/-- APP-4. The exact value of `ChebQC.l1Bound evoCheb` (a kernel evaluation):
`970308109900781462706584760376036893 / 400000000000000000000000000000000000 ≈ 2.4258`. -/
theorem l1Bound_evoCheb :
    ChebQC.l1Bound evoCheb =
      970308109900781462706584760376036893 / 400000000000000000000000000000000000 := by
  decide +kernel

/-- APP-4. The exact subnormalisation `‖c‖₁ ≈ 2.4258`. -/
theorem evoL1_eq :
    evoL1 =
      ((970308109900781462706584760376036893 / 400000000000000000000000000000000000 : ℚ) : ℝ) := by
  rw [evoL1, l1_eq_l1Bound_of_axis evoPoly evoCheb_axis, l1Bound_evoCheb]

/-- APP-4. `‖c‖₁ > 0`. -/
theorem evoL1_pos : 0 < evoL1 := by
  rw [evoL1_eq]
  norm_num

/-- APP-4. Decimal bounds `2.4257 ≤ ‖c‖₁ ≤ 2.4258`. -/
theorem evoL1_mem_Icc : evoL1 ∈ Set.Icc (2.4257 : ℝ) 2.4258 := by
  rw [evoL1_eq]
  constructor <;> norm_num

theorem norm_inv_evoL1 : ‖((evoL1 : ℂ)⁻¹)‖ = evoL1⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg evoL1_pos.le]

/-! ### The implementation: the Route A circuit -/

section Circuit

variable (E : HermitianEncoding ℋ)

/-- APP-4. The circuit: the Route A unitary of CERT-A for the complex Chebyshev coefficients of
`evoPoly`, a `12`-term LCU of the Chebyshev unitaries `U_{chebPhases k}` (`k < 12`, the phases of
`cₖ / ‖c‖₁` absorbed) on the register `Reg 12 ℋ`, using `66` queries to `U`/`U†`
(`evoCircuit_queries`). -/
noncomputable def evoCircuit : L (Reg evoCheb.length ℋ) := chebLCU E (chebCoeffs evoPoly)

/-- APP-4. The circuit is unitary. -/
theorem evoCircuit_mem_unitary : evoCircuit E ∈ unitary (L (Reg evoCheb.length ℋ)) :=
  chebLCU_mem_unitary E _

/-- APP-4. The circuit as a projected unitary encoding on `Reg 12 ℋ` (CERT-A `chebEncoding`):
the unitary is `evoCircuit E`, both projections are `1 ⊗ Π`. -/
noncomputable def evoEncoding : ProjUnitaryEncoding (Reg evoCheb.length ℋ) :=
  chebEncoding E (chebCoeffs evoPoly)

@[simp] theorem evoEncoding_U : (evoEncoding E).U = evoCircuit E := rfl

@[simp] theorem evoEncoding_P : (evoEncoding E).P = regP E := rfl

@[simp] theorem evoEncoding_P' : (evoEncoding E).P' = regP E := rfl

/-- APP-4 (exact implementation). The `(0,0)` block of the compressed circuit is
`‖c‖₁⁻¹ • p(A) Π` for `p = cos2Poly − i · sin2Poly`, with zero error:
```
(⟨0| ⊗ Π) evoCircuit E (|0⟩ ⊗ Π) = evoL1⁻¹ • (evoPoly(A) Π).
```
-/
theorem evoCircuit_topLeft :
    regTopLeft (regP E * evoCircuit E * regP E) =
      ((evoL1 : ℂ)⁻¹) • (aeval E.encoded (PolyQC.toPoly evoPoly) * E.P) :=
  routeA E evoPoly evoL1_pos.ne'

/-- APP-4. The same statement for the encoded operator of `evoEncoding E`. -/
theorem evoEncoding_regTopLeft_encoded :
    regTopLeft (evoEncoding E).encoded =
      ((evoL1 : ℂ)⁻¹) • (aeval E.encoded (PolyQC.toPoly evoPoly) * E.P) :=
  evoCircuit_topLeft E

variable (i : Fin (Module.finrank ℂ (rangeP E)))

/-- APP-4. On an eigenvector `ψᵢ` of `A` with eigenvalue `ςᵢ`, the compressed circuit acts as
the scalar `‖c‖₁⁻¹ · p(ςᵢ)` (SVT-3 `aeval_eigenVec`). -/
theorem evoCircuit_apply_eigenVec :
    regTopLeft (regP E * evoCircuit E * regP E) (eigenVec E i) =
      ((evoL1 : ℂ)⁻¹ * (PolyQC.toPoly evoPoly).eval (eigenValue E i : ℂ)) • eigenVec E i := by
  rw [evoCircuit_topLeft, LinearMap.smul_apply, Module.End.mul_apply, P_eigenVec,
    aeval_eigenVec, smul_smul]

/-- APP-4 (certified behaviour; GSLW Thm 58 style, polynomial step). Every eigenvector `ψᵢ` of
`A` (eigenvalue `ςᵢ ∈ [-1, 1]`, no gap needed) is mapped by the compressed circuit to
`(e^{-2iςᵢ} / ‖c‖₁) ψᵢ`, up to an error of norm at most `2ε / ‖c‖₁ ≈ 8.2 · 10⁻⁷`. -/
theorem evoCircuit_apply :
    ‖regTopLeft (regP E * evoCircuit E * regP E) (eigenVec E i) -
        ((evoL1 : ℂ)⁻¹ * Complex.exp (-(2 * (eigenValue E i : ℂ)) * Complex.I)) • eigenVec E i‖ ≤
      2 * 0.000001 / evoL1 := by
  have hcert := norm_eval_evoPoly_sub_exp_le _ (eigenValue_mem_Icc E i)
  have hvec : regTopLeft (regP E * evoCircuit E * regP E) (eigenVec E i) -
      ((evoL1 : ℂ)⁻¹ * Complex.exp (-(2 * (eigenValue E i : ℂ)) * Complex.I)) • eigenVec E i =
      ((evoL1 : ℂ)⁻¹ * ((PolyQC.toPoly evoPoly).eval (eigenValue E i : ℂ) -
        Complex.exp (-(2 * (eigenValue E i : ℂ)) * Complex.I))) • eigenVec E i := by
    rw [evoCircuit_apply_eigenVec, ← sub_smul, mul_sub]
  rw [hvec, norm_smul, norm_mul, norm_inv_evoL1, norm_eigenVec, mul_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hcert (inv_nonneg.mpr evoL1_pos.le)

/-- APP-4 (global bound). The compressed circuit maps every eigenvector `ψᵢ` to a vector of norm
at most `(1 + 2ε) / ‖c‖₁`, from `‖p(x)‖ ≤ 1 + 2ε` on `[-1, 1]`. -/
theorem evoCircuit_apply_norm_le :
    ‖regTopLeft (regP E * evoCircuit E * regP E) (eigenVec E i)‖ ≤
      (1 + 2 * 0.000001) / evoL1 := by
  rw [evoCircuit_apply_eigenVec, norm_smul, norm_mul, norm_inv_evoL1, norm_eigenVec, mul_one,
    div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_eval_evoPoly_le _ (eigenValue_mem_Icc E i))
    (inv_nonneg.mpr evoL1_pos.le)

end Circuit

/-! ### Resources -/

/-- APP-4. The query count of the circuit: `∑_{k<12} k = 66` uses of `U`/`U†`. The phase-based
Route B (QSVT with `11` complex phases) would use the optimal `deg p = 11` queries and one
ancilla qubit; Route A uses `66 = 6 · 11` queries and a `12`-dimensional ancilla register
(`⌈log₂ 12⌉ = 4` qubits) but needs no phase-finding. -/
theorem evoCircuit_queries : routeA_queries evoCheb.length = 66 := by
  rw [evoCheb_length, routeA_queries_eq]

end QSVT.Examples
