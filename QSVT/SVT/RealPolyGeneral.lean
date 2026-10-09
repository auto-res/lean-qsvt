/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.SVT.QSVT
import QSVT.SVT.RealPoly
import QSVT.SVT.SingularPair

/-!
# Real polynomials for general projected unitary encodings (formal-spec SVT-8, GSLW Cor 18)

`QSVT.SVT.RealPoly` proves GSLW Cor 18 for *Hermitian* encodings (`Π̃ = Π`, `A† = A`) through
the eigenvalue transformation `qet`. This module proves it for an arbitrary projected unitary
encoding `E` (encoded operator `A = Π̃ U Π`) through the general QSVT theorem `qsvt_odd`
(SVT-7): for a phase list `Φ` of odd length with QSP polynomial `P = P_Φ = (qspPoly Φ).1`,
```
(|0⟩⟨0| ⊗ Π̃) lcu2 U_Φ U_{−Φ} (|0⟩⟨0| ⊗ Π) = |0⟩⟨0| ⊗ Re[P]^{(SV)}(A)        (`qsvt_real_odd`)
```
where `Re[P] = rePoly P = (P + P^*)/2` and `Re[P]^{(SV)}(A) = svTransform (rePoly P) E` is the
SVD-free singular value transformation of SVT-5. The proof is three rewrites: `proj_lcu2_proj`
(ENC-3, with different projectors `Π̃` on the left and `Π` on the right), `qsvt_odd` for `Φ` and
for `−Φ` (whose polynomial is `P^*`, `qspPoly_neg`), and linearity of `svTransform`
(`svTransform_add`, `svTransform_smul`). The even-length companion with `Π` on both sides is
`qsvt_real_even`.

The vector form on an arbitrary singular pair `(ψ, σ)` (`IsSingularPair`, SVT-7) is
```
(⟨0| ⊗ Π̃) lcu2 U_Φ U_{−Φ} (|0⟩ ⊗ Π) ψ = Re[P](σ) ψ̃      (`topLeft_qsvt_real_apply_singular`)
```
with `ψ̃ = lvOf E ψ σ`; it follows from `proj_altSeq_apply_singular_odd` for `Φ` and `−Φ`.

Finally `ProjUnitaryEncoding.qsvtReal E Φ : ProjUnitaryEncoding (Anc ℋ)` packages the LCU
circuit with the projections `|0⟩⟨0| ⊗ Π` (input) and `|0⟩⟨0| ⊗ Π̃` (output) as a projected
unitary encoding on one more qubit, whose encoded operator is `|0⟩⟨0| ⊗ Re[P_Φ]^{(SV)}(A)` for
odd `Φ.length` (`qsvtReal_encoded_odd`); it is the general-encoding analogue of
`HermitianEncoding.qsvtReal`.

## Resource count

As in the Hermitian case: one ancilla qubit, two ancilla Hadamards, `Φ.length` (controlled)
uses of `U`/`U†`; the gate list is `compileQsvtReal Φ` of CIRC-3.
-/

namespace QSVT.SVT

open QuantumState QSVT.Encoding QSVT.QSP Polynomial

universe u

variable {ℋ : Type u} [Qudit ℋ]

section General

variable (E : ProjUnitaryEncoding ℋ)

/-- SVT-8 (GSLW Cor 18, general projected unitary encoding, odd length). Compressing the
two-term LCU of `U_Φ` and `U_{−Φ}` by `|0⟩⟨0| ⊗ Π̃` on the left and `|0⟩⟨0| ⊗ Π` on the right
gives `|0⟩⟨0| ⊗ Re[P_Φ]^{(SV)}(A)`:
```
(|0⟩⟨0| ⊗ Π̃) lcu2 U_Φ U_{−Φ} (|0⟩⟨0| ⊗ Π) = |0⟩⟨0| ⊗ svTransform (rePoly P_Φ) E,
```
where `P_Φ = (qspPoly Φ).1`. -/
theorem qsvt_real_odd {Φ : List ℝ} (hodd : Odd Φ.length) :
    blockDiag E.P' 0 * lcu2 (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) * blockDiag E.P 0 =
      blockDiag (svTransform (rePoly (qspPoly Φ).1) E) 0 := by
  have hodd' : Odd (Φ.map Neg.neg).length := by rw [List.length_map]; exact hodd
  rw [proj_lcu2_proj, qsvt_odd E hodd, qsvt_odd E hodd', qspPoly_neg_fst, rePoly, svTransform_smul,
    svTransform_add]

/-- SVT-8 (GSLW Cor 18, general projected unitary encoding, even length). With `|0⟩⟨0| ⊗ Π` on
both sides,
```
(|0⟩⟨0| ⊗ Π) lcu2 U_Φ U_{−Φ} (|0⟩⟨0| ⊗ Π) = |0⟩⟨0| ⊗ svTransform (rePoly P_Φ) E.
```
-/
theorem qsvt_real_even {Φ : List ℝ} (heven : Even Φ.length) :
    blockDiag E.P 0 * lcu2 (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) * blockDiag E.P 0 =
      blockDiag (svTransform (rePoly (qspPoly Φ).1) E) 0 := by
  have heven' : Even (Φ.map Neg.neg).length := by rw [List.length_map]; exact heven
  rw [proj_lcu2_proj, qsvt_even E heven, qsvt_even E heven', qspPoly_neg_fst, rePoly,
    svTransform_smul, svTransform_add]

/-- SVT-8 (GSLW Cor 18, `(0,0)` block). `(⟨0| ⊗ Π̃) lcu2 U_Φ U_{−Φ} (|0⟩ ⊗ Π) = Re[P_Φ]^{(SV)}(A)`
for odd `Φ.length`. -/
theorem topLeft_qsvt_real_odd {Φ : List ℝ} (hodd : Odd Φ.length) :
    topLeft (blockDiag E.P' 0 * lcu2 (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) * blockDiag E.P 0) =
      svTransform (rePoly (qspPoly Φ).1) E := by
  rw [qsvt_real_odd E hodd, topLeft_blockDiag]

/-- SVT-8. `Re[p](σ) = (p(σ) + p^*(σ))/2` for every `σ : ℂ` (evaluation of `rePoly`). -/
theorem eval_rePoly (p : ℂ[X]) (z : ℂ) :
    (rePoly p).eval z = (1 / 2 : ℂ) * (p.eval z + (conjP p).eval z) := by
  rw [rePoly, eval_smul, eval_add, smul_eq_mul]

/-- SVT-8 (GSLW Cor 18, vector form on a singular pair). For a singular pair `(ψ, σ)` of `E`
(`IsSingularPair`) and odd `Φ.length`,
```
(⟨0| ⊗ Π̃) lcu2 U_Φ U_{−Φ} (|0⟩ ⊗ Π) ψ = Re[P_Φ](σ) ψ̃,     ψ̃ = lvOf E ψ σ.
```
-/
theorem topLeft_qsvt_real_apply_singular {ψ : ℋ} {σ : ℝ} (h : IsSingularPair E ψ σ)
    {Φ : List ℝ} (hodd : Odd Φ.length) :
    topLeft (blockDiag E.P' 0 * lcu2 (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) * blockDiag E.P 0)
        ψ =
      ((rePoly (qspPoly Φ).1).eval (σ : ℂ)) • lvOf E ψ σ := by
  have hodd' : Odd (Φ.map Neg.neg).length := by rw [List.length_map]; exact hodd
  rw [topLeft_proj_lcu2_proj, LinearMap.smul_apply, LinearMap.add_apply]
  simp only [Module.End.mul_apply]
  rw [h.P_eq, proj_altSeq_apply_singular_odd h hodd, proj_altSeq_apply_singular_odd h hodd',
    qspPoly_neg_fst, eval_rePoly, ← add_smul, smul_smul]

end General

/-! ### Packaging as a projected unitary encoding on `Anc ℋ` -/

/-- SVT-8 (GSLW Cor 18, general). The projected unitary encoding of `Re[P_Φ]^{(SV)}(A)` on `ℋ`
with one ancilla qubit: the unitary is the LCU circuit `lcu2 U_Φ U_{−Φ}` on `Anc ℋ`, the input
projection is `|0⟩⟨0| ⊗ Π` and the output projection is `|0⟩⟨0| ⊗ Π̃`. For odd `Φ.length` its
encoded operator is `|0⟩⟨0| ⊗ svTransform (rePoly P_Φ) E` (`qsvtReal_encoded_odd`). -/
noncomputable def _root_.QSVT.Encoding.ProjUnitaryEncoding.qsvtReal (E : ProjUnitaryEncoding ℋ)
    (Φ : List ℝ) : ProjUnitaryEncoding (Anc ℋ) where
  U := lcu2 (altSeq E Φ) (altSeq E (Φ.map Neg.neg))
  hU := lcu2_mem_unitary _ _ (altSeq_mem_unitary _ _) (altSeq_mem_unitary _ _)
  P := blockDiag E.P 0
  P' := blockDiag E.P' 0
  hP := blockDiag_isProjective E.hP
  hP' := blockDiag_isProjective E.hP'

section Packaged

variable (E : ProjUnitaryEncoding ℋ)

@[simp] theorem qsvtReal_U_general (Φ : List ℝ) :
    (E.qsvtReal Φ).U = lcu2 (altSeq E Φ) (altSeq E (Φ.map Neg.neg)) := rfl

@[simp] theorem qsvtReal_P_general (Φ : List ℝ) : (E.qsvtReal Φ).P = blockDiag E.P 0 := rfl

@[simp] theorem qsvtReal_P'_general (Φ : List ℝ) : (E.qsvtReal Φ).P' = blockDiag E.P' 0 := rfl

/-- SVT-8 (GSLW Cor 18, general). The encoded operator of `E.qsvtReal Φ` is
`|0⟩⟨0| ⊗ Re[P_Φ]^{(SV)}(A)` for odd `Φ.length`. -/
theorem qsvtReal_encoded_odd {Φ : List ℝ} (hodd : Odd Φ.length) :
    (E.qsvtReal Φ).encoded = blockDiag (svTransform (rePoly (qspPoly Φ).1) E) 0 :=
  qsvt_real_odd E hodd

/-- SVT-8. The `(0,0)` block of the encoded operator of `E.qsvtReal Φ` is
`Re[P_Φ]^{(SV)}(A)` for odd `Φ.length`. -/
theorem topLeft_qsvtReal_encoded_odd {Φ : List ℝ} (hodd : Odd Φ.length) :
    topLeft (E.qsvtReal Φ).encoded = svTransform (rePoly (qspPoly Φ).1) E := by
  rw [qsvtReal_encoded_odd E hodd, topLeft_blockDiag]

end Packaged

end QSVT.SVT
