/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shosonoda
-/
import QSVT.Encoding.Ancilla

/-!
# Two-term linear combination of unitaries (formal-spec ENC-3)

The LCU circuit with one ancilla qubit, two unitaries `U₀`, `U₁` on `ℋ` and the uniform
weights `y = (1/2, 1/2)` (state preparation `V = H`, GSLW Lemma 52 in the case `j ∈ {0, 1}`):

`lcu2 U₀ U₁ = (H ⊗ I) (|0⟩⟨0| ⊗ U₀ + |1⟩⟨1| ⊗ U₁) (H ⊗ I)`

is a unitary on `Anc ℋ` (`lcu2_mem_unitary`) whose top-left block is `(U₀ + U₁)/2`
(`topLeft_lcu2`); in the terminology of ENC-2 it is a `(1, 1, 0)`-block-encoding of
`(U₀ + U₁)/2`. The closed form `lcu2_eq` gives all four blocks.

## GSLW Cor 18 (SVT-8)

Once SVT-3/SVT-7 are available, Cor 18 is this module applied to `U₀ = altSeq E Φ` and
`U₁ = altSeq E (−Φ)`: by SVT-7, `P' * altSeq E Φ * P = P^{(SV)}(A)` and
`P' * altSeq E (−Φ) * P = (P^*)^{(SV)}(A)` (the lemma `qspPoly (−Φ) = (P^*, …)` of SVT-8), so
`proj_lcu2_proj` / `topLeft_proj_lcu2_proj` with `Pl = P'`, `Pr = P` yield

`(⟨0| ⊗ P') lcu2 (U_Φ) (U_{−Φ}) (|0⟩ ⊗ P) = (P^{(SV)}(A) + (P^*)^{(SV)}(A)) / 2 = Re[P]^{(SV)}(A)`,

i.e. `(⟨+| ⊗ Π̃)(|0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ})(|+⟩ ⊗ Π) = Re[P]^{(SV)}(A)` in GSLW's notation.
-/

namespace QSVT.Encoding

open QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- ENC-3. The two-term LCU with uniform weights:
`lcu2 U₀ U₁ = (H ⊗ I) (|0⟩⟨0| ⊗ U₀ + |1⟩⟨1| ⊗ U₁) (H ⊗ I)`. -/
noncomputable def lcu2 (U₀ U₁ : L ℋ) : L (Anc ℋ) := hadA * blockDiag U₀ U₁ * hadA

variable (U₀ U₁ : L ℋ)

/-- ENC-3. The LCU circuit is unitary when `U₀` and `U₁` are. -/
theorem lcu2_mem_unitary (h₀ : U₀ ∈ unitary (L ℋ)) (h₁ : U₁ ∈ unitary (L ℋ)) :
    lcu2 U₀ U₁ ∈ unitary (L (Anc ℋ)) :=
  mul_mem (mul_mem hadA_mem_unitary (blockDiag_mem_unitary h₀ h₁)) hadA_mem_unitary

/-- ENC-3. Closed form of the LCU circuit:
`lcu2 U₀ U₁ = (1/2) [[U₀ + U₁, U₀ − U₁], [U₀ − U₁, U₀ + U₁]]`. -/
theorem lcu2_eq :
    lcu2 U₀ U₁ = (1 / 2 : ℂ) • block (U₀ + U₁) (U₀ - U₁) (U₀ - U₁) (U₀ + U₁) := by
  rw [lcu2, hadA, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul, invSqrtTwo_mul_self,
    blockDiag, block_mul_block, block_mul_block]
  simp only [one_mul, mul_one, mul_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
    sub_eq_add_neg]

/-- ENC-3. The top-left block `(⟨0| ⊗ I) lcu2 U₀ U₁ (|0⟩ ⊗ I)` is `(U₀ + U₁)/2`. -/
theorem topLeft_lcu2 : topLeft (lcu2 U₀ U₁) = (1 / 2 : ℂ) • (U₀ + U₁) := by
  rw [lcu2_eq, topLeft_smul, topLeft_block]

/-- ENC-3. Compressing the LCU circuit by the ancilla projector `|0⟩⟨0| ⊗ I`. -/
theorem anc0_lcu2_anc0 :
    anc0 * lcu2 U₀ U₁ * anc0 = blockDiag ((1 / 2 : ℂ) • (U₀ + U₁)) 0 := by
  rw [anc0_mul_mul_anc0, topLeft_lcu2]

/-- ENC-3 / GSLW Cor 18. Compressing the LCU circuit by `|0⟩⟨0| ⊗ Pl` on the left and
`|0⟩⟨0| ⊗ Pr` on the right gives `|0⟩⟨0| ⊗ (Pl U₀ Pr + Pl U₁ Pr)/2`. -/
theorem proj_lcu2_proj (Pl Pr : L ℋ) :
    blockDiag Pl 0 * lcu2 U₀ U₁ * blockDiag Pr 0 =
      blockDiag ((1 / 2 : ℂ) • (Pl * U₀ * Pr + Pl * U₁ * Pr)) 0 := by
  rw [lcu2_eq, mul_smul_comm, smul_mul_assoc]
  simp only [blockDiag, block_mul_block, block_smul, zero_mul, mul_zero, add_zero, smul_zero,
    mul_add, add_mul]

/-- ENC-3 / GSLW Cor 18. The `(0,0)` block of the compressed LCU circuit:
`(⟨0| ⊗ Pl) lcu2 U₀ U₁ (|0⟩ ⊗ Pr) = (Pl U₀ Pr + Pl U₁ Pr)/2`. -/
theorem topLeft_proj_lcu2_proj (Pl Pr : L ℋ) :
    topLeft (blockDiag Pl 0 * lcu2 U₀ U₁ * blockDiag Pr 0) =
      (1 / 2 : ℂ) • (Pl * U₀ * Pr + Pl * U₁ * Pr) := by
  rw [proj_lcu2_proj, topLeft_blockDiag]

end QSVT.Encoding
