# 形式化仕様: Lean で定義・証明する対象の一覧

- 作成日: 2026-10-08
- 本体: [plan.md](plan.md)．ここでは各フェーズで扱う定義・定理を ID 付きで精密に書く．
- 参照: GSLW = Gilyén–Su–Low–Wiebe, arXiv:1806.01838（定理番号は v1 PDF で確認済み）．
- 難易度: ★（定義・簡単な補題）〜 ★★★★（数週間規模）．
- Lean シグネチャは**方向性を示すスケッチ**であり，Phase 0 の API 確認後に確定する．

## 進捗と命名の差異（2026-10-08 更新）

| ID | 状態 | Lean での実体（spec からの差異） |
|---|---|---|
| POLY-1/2 | 済 | `QSVT/Polynomial/Parity.lean`．`HasParity P n := (Even n → IsEven P) ∧ (Odd n → IsOdd P)` もここ |
| POLY-3 | 済 | `SqrtPart.lean`: `sqrtPart` ではなく `evenRoot P := contract 2 P`，`oddRoot P := contract 2 P.divX`．`IsEven.eq_evenRoot_comp`，`IsOdd.eq_X_mul_oddRoot_comp` |
| POLY-4 | 済 | `SupNorm.lean`: `supNorm`，`norm_eval_le_supNorm`，`supNorm_le_of_forall`（$0\le M$ 不要），`supNorm_le_sum_norm_coeff` |
| POLY-5/6 | 済 | `Chebyshev.lean`: ℕ 添字ラッパ `T_eval_cos`，`norm_eval_T_le_one`，`T_parity`，`natDegree_T`；`ChebSeries`（`toPoly`，`l1`，`supNorm_toPoly_le_l1`）．`ChebCoeff.lean`: 計算可能な `QC := ℚ × ℚ`，`PolyQC`，`ChebQC`，`ofMonomials`（Horner + `mulX`）と正当性 `toPoly_ofMonomials`，`l1Bound`．`#eval` 可 |
| QSP-1 | 済 | `QSP/Conventions.lean` |
| QSP-3 | 済 | `QSP/Poly.lean`（`qspPoly4`，`qspPoly`，`conjP`，`negX`），`QSP/Structure.lean`（`seqR_eval4`，`seqR_eval`，`natDegree_*_le`，`hasParity_*`，`norm_identity`，`qspPoly_neg`，`seqR_apply_zero_zero/one_zero`） |
| QSP-4 | 済 | `QSP/Chebyshev.lean`: `chebPhases`，`seqR_chebPhases_eq`（全行列，$d\ge 0$），`seqR_chebPhases` |
| QSP-5 | 済 | `QSP/Endpoints.lean`: `seqR_one`，`seqR_neg_one`，`alt`，`seqR_zero_of_even/odd` |
| QSP-7 | 済 | `QSP/PolyW.lean`（`qspPolyW`，`seqW_eval`），`QSP/Existence.lean`（**`exists_phases`**: Thm 3 ⇐），`QSP/Complementary.lean`（**Lemma 6 `exists_sumsq_decomposition`**: 非負偶多項式 $A=B^2+(1-x^2)C^2$，平方和表現 `SOSRep` の積閉性と根の 3 分類による帰納法；**Thm 5 `exists_complement`**，**Cor 10 `exists_phases_real`/`exists_phases_R_real`**: $[-1,1]$ で $|\tilde P|\le1$ の parity 付き実多項式は反射規約の位相列で $\Re$ として実現可能）．Thm 4 の必要性方向は未 |
| ENC-1 | 済 | `Encoding/Projected.lean`: 射影のフィールド名は `P`（$\Pi$），`P'`（$\tilde\Pi$）．`Π` は Lean の識別子に使えない．`HermitianEncoding`（`P'_eq`，`encoded_selfAdjoint`） |
| ENC-2/3 | 済 | **設計変更 D8**: 補助 1 qubit は `Anc ℋ := WithLp 2 (ℋ × ℋ)`，2×2 ブロック作用素 `block`，`blockDiag`，`topLeft`，`anc0`，`hadA`，`lcu2`（`Ancilla.lean`，`LCU.lean`）．$m$ レジスタは `Reg m ℋ := PiLp 2 (fun _ : Fin m => ℋ)`，`matOp`，`selectOp`，`regTopLeft`，`reg0`，`lcu V W`，Householder 状態準備 `householder`，`lcu_complex`（`Register.lean`，`LCUm.lean`）．テンソル積は回路層まで使わない |
| SVT-1/2 | 済 | `SVT/AltSeq.lean`（`altSeq`，`altSeq_mem_unitary`，`altSeq_one/two/three`），`SVT/PhaseOp.lean` |
| SVT-3 | 済 | `SVT/EigenBasis.lean`（`eigenVec`，`eigenValue`，`aeval_eigenVec`，`ext_of_eigenVec`），`SVT/TwoVector.lean`（(R0)–(R5)，`altSeq_apply_eigen`，`proj_altSeq_apply_eigen(_eval)`），`SVT/QET.lean`: **`qet : P * altSeq Φ * P = aeval A (qspPoly Φ).1 * P`**，`qspPoly_chebPhases`，`qet_chebyshev` |
| SVT-6/7 | 済 | `SVT/SVD.lean`（$A^\dagger A$ の固有基底から特異ベクトル対 `rv`/`lv`，`σ`，`svTransform_apply_rv_of_isEven/isOdd`），`SVT/TwoFrame.lean`（2 フレームの関係式と `altSeq_apply_rv`，σ に条件なし），`SVT/QSVT.lean`: **`qsvt_odd`/`qsvt_even`**（GSLW Thm 17，一般の射影ユニタリ符号化），`qet_of_qsvt` |
| SVT-4/5 | 済 | `SVT/NormBound.lean`（`norm_aeval_apply_le`，`opNorm_aeval_mul_P_le`），`SVT/SVTransform.lean`（`svTransform`，`svTransform_of_isEven/isOdd`，`svTransform_eq_aeval`） |
| SVT-8 | 済 | `SVT/RealPoly.lean`: `rePoly`，`aeval_adjoint`，`P_mul_aeval`，**`qet_real`**（Cor 18），合成子 `HermitianEncoding.qsvtReal E Φ : HermitianEncoding (Anc ℋ)` と `qsvtReal_encoded` |
| CERT-A | 済 | `Pipeline/ChebLCU.lean`: `chebLCU E c`，`regTopLeft_regP_chebLCU_regP`，**`routeA`**（計算可能入力 `PolyQC` から $f(A)P/\|c\|_1$ の符号化，exact），`chebHermitianEncoding`，`routeA_queries` |
| CERT-B | 済 | `Certificate/Bound.lean`（LeanCert の kernel 検証と `supNorm` の接続），`Sign21.lean`（次数 21 の符号関数近似: $\|p\|\le1$，$[0.15,1]$ で $\pm c$ に 0.0236 以内），`CosExample.lean`（$\cos 2x$ の次数 10 近似，Taylor 多項式経由で $10^{-6}$），`ChebC.lean`/`PhaseCheck.lean`（位相列からの Chebyshev 係数の区間再帰 `check`/`checkRe` と **`checkRe_sound`**），`Sign21Phases.lean`（次数 21 の位相証明書を kernel で 45 s，`target_sign21_eq`） |
| APP-1 | 済 | `Examples/Sign21.lean`（Route A: 231 クエリ），`Examples/Sign21RouteB.lean`（**Route B: 21 クエリ，補助 1 qubit**），`SVT/SingularPair.lean`（任意の特異ベクトル対 `IsSingularPair`），`SVT/RealPolyGeneral.lean`（一般符号化の Cor 18 `qsvt_real_odd`），`Examples/FixedPointAA.lean`（**GSLW Thm 27**: rank-1 射影 $|\psi_0\rangle\langle\psi_0|$ と良い部分空間の射影で符号化し，初期重なり $a\ge0.15$ から成功振幅 $\ge0.869$，21 クエリ） |
| APP-3 | 済 | `Certificate/InvExample.lean`（$\kappa=4$，次数 29，$|4x\,p(x)-3/4|\le 7.5\times10^{-4}$ on $[1/4,1]$，kernel 115 s），`Examples/Inverse.lean`（固有値 $|\lambda|\ge1/4$ で $c/(4\lambda\|c\|_1)$ 倍に $\varepsilon/\|c\|_1$ 以内，435 クエリ）．注: $|p|\le1$ の制約下で $1/(\kappa x)$ そのもの（$c=1$）は $x=1/\kappa$ の折れ点のため次数 $\Omega(1/\varepsilon)$ が必要で，$c=3/4$ を採用 |
| APP-2 | 済 | `Certificate/RectExample.lean`（次数 32 の偶多項式，$|x|\le0.4$ で $[0.99,1]$，$|x|\ge0.6$ で $|r|\le0.01$，LP で証明書の余裕 $2.4\times10^{-3}$ を最大化），`Examples/Threshold.lean`（固有値の窓フィルタ，528 クエリ） |
| APP-5 | 済 | `Lang/Loop.lean`（`iterate`，`qsvtIter` のコスト $|\Phi|^k$ と `spec = compIter`，`totalQueries`，`expectedQueries`），`Examples/Loop.lean`（反復 sign，二分探索スケルトン `bisect`/`visited`，窓プログラム `windowProg t`） |
| ENC-4 | 済 | `Encoding/Swap.lean`（`swapReg : Reg a (Reg b ℋ) ≃ₗᵢ Reg b (Reg a ℋ)`，`outerLift`/`innerLift`），`Encoding/Product.lean`（`prodU`，`prodEncoding`，**`topLeft₂_prodU`**: Lemma 53）．IR への `prod` 統合は未（`Expr` の変更が `Lang` を壊すため，入れ子の補助空間の一般化が必要） |
| CIRC-1/5 ($m=2^k$) | 済 | `Qubit/RegBridge.lean`（`regEquiv : Reg (2^k) (Qubits n) ≃ₗᵢ Qubits (n+k)`，`liftReg_selectOp`（多重化 select），`liftReg_matOp`（$k$ qubit ゲート），`liftReg_lcu`，`liftReg_chebLCU`） |
| CLI | 済 | `tools/qsvt`（`lake env lean --run tools/qsvt_cli.lean`）: `info`，`qasm`，`check`（`checkRe` の untrusted プレビュー），`emit-cert`（`decide +kernel` の Lean モジュール生成）．起動 8 s，sign21 の `checkRe` は IO 評価 0.4 s / kernel 47 s |
| LANG-1 | 済 | `Lang/ExprQ.lean`（有理データの `ExprQ`，`toExpr`，計算可能なコスト `queriesQ`/`ancillaDimQ`/`scaleQ`/`wellScaledQ` と IR との一致定理，**`baseQ_eq`**），`Lang/Notation.lean`（`U₀`，`qsvt[Φ] e`，`cheb[c] e`，`poly[l] e`），`Lang/Info.lean`（`#qsvt_info` コマンド: クエリ数・補助次元・次数・スケール・ゲート数・OpenQASM） |
| APP-4 (AA 結合) | 済 | `Examples/Compose.lean`（正規化補題，スペクトル関数計算 `funCalc` と Parseval，`norm_aeval_apply_ge`，Route A 回路から AA 用データ `regGood`/`regAmp`，`regAA_amplitude`），`Examples/EvolutionAA.lean`（**`evolutionAA_amplitude`**: $e^{-2iA}b$ の準備を固定点振幅増幅で成功振幅 $\ge0.869$，出力誤差 $\le0.0237$，1386 クエリ．GSLW Thm 58 相当，定数 $c\approx0.892$） |
| CERT-B ($\delta=0.1$) | 済（heavy） | `QSVTHeavy/SignD01.lean`，`SignD01Phases.lean`: 次数 35，$c=79/80$，plateau $\pm0.012$ on $[0.1,1]$，位相証明書 $\varepsilon=10^{-12}$（kernel 265 s）．ビルドに約 9 分かかるため既定ターゲット外 |
| APP-4 | 済 | `Examples/CosEvolution.lean`（$\cos 2A$，55 クエリ），`Certificate/SinExample.lean`，`Examples/Evolution.lean`（複素係数 Route A で $e^{-2iA}/\|c\|_1$，全固有ベクトルで $2\times10^{-6}/\|c\|_1$ 以内，66 クエリ）．振幅増幅による正規化（Thm 58 の残り）は未 |
| CIRC-4/5/6 | 済 | `Qubit/Space.lean`，`Gates.lean`，`Bridge.lean`（`Anc (Qubits n) ≃ₗᵢ Qubits (n+1)`，`liftAnc`，`liftAnc_cpiNot_diagProj = ctrlX`），`Qubit/Compile.lean`（`compileQ`，**`compileQ_qsvtReal`**: qubit ゲート列の意味 = `liftAnc` した Route B ユニタリ），`Qubit/Qasm.lean`（OpenQASM 3 出力，untrusted） |
| IR-1/2 | 済 | `IR/Expr.lean`（`Expr = oracle \| qsvtReal Φ e \| chebLCU c₀ c e`，`spec`，`scale`，`WellScaled`），`IR/Denote.lean`（`space`，`denote`，`chebEnc0`: 次段の射影は `atZero Π = \|0⟩⟨0\| ⊗ Π`），`IR/Sound.lean`（**`compress_aeval_mul_P`**，`base_eq_smul`），`IR/Cost.lean`（`queries`，`ancillaDim`，`natDegree_spec_le`） |
| CIRC-1/3 | 済 | `Circuit/Gadget.lean`（`cpiNot`，`gadget_eq`: Fig. 1b，`gadgetSeq_eq`，`qsvtReal_U_eq_gadget`），`Circuit/Primitive.lean`（`Prim`，`Circuit.denote`，`compileQsvtReal`，`denote_compileQsvtReal`，資源数 `oracleCount = n`，`cpiNotCount = 2n`，`phaseCount = n`） |
| QSP-2/6 | 済 | `QSP/Conversion.lean`（`Wrot_eq_Rref`，`seqW_eq_seqR`，`seqW_apply_zero_zero_eq`: Cor 8 の対応を一般の $d$ で），`QSP/Perturb.lean`（`norm_seqR_sub_seqR_le`: 定数 1，作用素ノルムは `Matrix.Norms.L2Operator`） |
| 作用素層 | 済 | `Operator/Basic.lean`: lean-quantum の `QuantumState` 名前空間を同名で複製（Apache-2.0 表示） |


---

## 0. 記法と規約

- $\mathcal H$: 有限次元複素 Hilbert 空間．lean-quantum の `Qudit ℋ`，作用素は `L ℋ := ℋ →ₗ[ℂ] ℋ`，随伴は `X†`．
- 射影: `IsProjective Π := Π† = Π ∧ Π * Π = Π`（lean-quantum の `QuantumState.IsProjective`）．
- 多項式: `Polynomial ℂ`（記号 `ℂ[X]`）．$P^*$ は係数の複素共役（`Polynomial.map (starRingEnd ℂ)`）．
- 位相列: `Phases d := Fin d → ℝ`．添字は GSLW と同じく $\phi_1,\dots,\phi_d$（Lean では `Fin d` の 0 始まりに +1 で読み替え）．
- 1 qubit 行列: `M₂ := Matrix (Fin 2) (Fin 2) ℂ`．$\sigma_z = \mathrm{diag}(1,-1)$，$e^{i\phi\sigma_z} = \mathrm{diag}(e^{i\phi}, e^{-i\phi})$．
- **QSP 規約（D2）**: 主規約は反射規約
  $$R(x) = \begin{pmatrix} x & \sqrt{1-x^2} \\ \sqrt{1-x^2} & -x \end{pmatrix},\qquad \mathrm{seqR}(\Phi, x) = \prod_{j=1}^{d} e^{i\phi_j\sigma_z} R(x)$$
  （GSLW Def 7, Cor 8）．回転規約 $W(x) = \begin{pmatrix} x & i\sqrt{1-x^2} \\ i\sqrt{1-x^2} & x\end{pmatrix}$ と
  $\mathrm{seqW}(\Phi', x) = e^{i\phi'_0\sigma_z}\prod_{j=1}^{k} W(x)e^{i\phi'_j\sigma_z}$（GSLW Thm 3）は変換補題で接続．
- **交代列（GSLW Def 15）**: $\Phi\in\mathbb R^n$，
  $$U_\Phi = \begin{cases} e^{i\phi_1(2\tilde\Pi-I)}\,U\prod_{j=1}^{(n-1)/2}\big(e^{i\phi_{2j}(2\Pi-I)}U^\dagger e^{i\phi_{2j+1}(2\tilde\Pi-I)}U\big) & n\ \text{odd}\\[4pt] \prod_{j=1}^{n/2}\big(e^{i\phi_{2j-1}(2\Pi-I)}U^\dagger e^{i\phi_{2j}(2\tilde\Pi-I)}U\big) & n\ \text{even}\end{cases}$$

---

## 1. 多項式層（Phase 1）

| ID | 内容 | Lean スケッチ | 難易度 |
|---|---|---|---|
| POLY-1 | parity: `IsEven P := ∀ k odd, P.coeff k = 0`，`IsOdd` 同様．`HasParity P (n : ℕ)` | `def Polynomial.IsEven (P : ℂ[X]) : Prop` | ★ |
| POLY-2 | 偶奇分解 `evenPart P + oddPart P = P`，一意性 | `def evenPart (P : ℂ[X]) : ℂ[X]` | ★ |
| POLY-3 | 偶多項式の表現: `IsEven P ↔ ∃ R, P = R.comp (X^2)`．奇: `P = X * R.comp (X^2)`．`sqrtPart P := R` を構成的に（`coeff (2k)` を集める） | `def sqrtPart (P : ℂ[X]) : ℂ[X]` と `evenPart_eq_sqrtPart_comp` | ★★ |
| POLY-4 | $[-1,1]$ 上 sup ノルム `supNorm P := sSup {‖P.eval x‖ \| x ∈ Icc (-1) 1}`，有限性，三角不等式，$\|P\|_\infty\le\sum_k \|c_k\|$（Chebyshev 基底では $|T_k|\le 1$ を使う） | `noncomputable def supNorm (P : ℂ[X]) : ℝ` | ★★ |
| POLY-5 | Chebyshev: Mathlib `Polynomial.Chebyshev.T ℂ n` の流用．$T_n(\cos\theta)=\cos n\theta$（`Polynomial.Chebyshev.T_real_cos` 系），parity，$xT_k = (T_{k+1}+T_{k-1})/2$，$T_mT_n = (T_{m+n}+T_{\|m-n\|})/2$ | 既存 API の確認が主 | ★ |
| POLY-6 | Chebyshev 展開: `chebCoeff : ℂ[X] → (ℕ → ℂ)`（単項式基底→Chebyshev 基底の有理線形変換）と `eval_eq_sum_chebCoeff` | `def chebCoeff (P : ℂ[X]) (k : ℕ) : ℂ` | ★★ |

---

## 2. QSP 層（Phase 1）

### QSP-1 定義（★）
```lean
def Rref (x : ℝ) : M₂            -- GSLW Def 7
def phaseZ (φ : ℝ) : M₂           -- diag (exp (I φ), exp (-I φ))
def seqR : (Φ : List ℝ) → ℝ → M₂  -- [] ↦ 1, (φ :: Φ) ↦ phaseZ φ * Rref x * seqR Φ x
def Wrot (x : ℝ) : M₂
def seqW (φ₀ : ℝ) (Φ : List ℝ) (x : ℝ) : M₂
```
補題: `Rref x ∈ unitaryGroup` for $x\in[-1,1]$（$\sqrt{1-x^2}$ は `Real.sqrt`），`Rref x * Rref x = 1`，`phaseZ φ` ユニタリ．

### QSP-2 規約変換（★★）
**検証済（2026-10-08，`tools/phases/qsp_conventions.py`，$d\le 8$）**: GSLW 式 (16) は印刷では右側が $e^{+i\frac\pi4\sigma_z}$ だが，正しくは両側とも $-\pi/4$:
$$W(x) = i\,e^{-i\frac\pi4\sigma_z}\,R(x)\,e^{-i\frac\pi4\sigma_z}.$$
位相の対応は Cor 8 の主張どおり $\phi_1 = \phi'_0+\phi'_d+(d-1)\tfrac\pi2,\ \phi_j = \phi'_{j-1}-\tfrac\pi2\ (j\ge2)$ で左上成分が一致．行列全体の厳密な関係は（$\theta := \phi'_d-\pi/4$，$\tilde\Phi := (\phi'_0-\pi/4,\ \phi'_1-\pi/2,\dots,\phi'_{d-1}-\pi/2)$）
$$\mathrm{seqW}(\Phi';x) = i^d\,\mathrm{seqR}(\tilde\Phi;x)\,e^{i\theta\sigma_z} = \sigma_z^d\,e^{-i\theta\sigma_z}\,\mathrm{seqR}(\Phi;x)\,e^{i\theta\sigma_z}.$$
ソルバー（pyqsp，qsppack はいずれも seqW 規約）の出力を主規約に写すのに使う．各ソルバーの規約差（対称位相，$\pm\pi/4$ オフセット，$\Re P$ か $\Im P$ か）は [qsp-convention-check.md](qsp-convention-check.md) の表を参照．

### QSP-3 構造定理（評価定理）（★★★）
**検証済（数値・記号，$d\le 8$）**の $R$ 規約の再帰．$Q$ は**左下**成分の多項式:
```lean
/-- QSP-3. seqR Φ x = [[P(x), Q*(−x)·s], [Q(x)·s, P*(−x)]],  s = √(1-x²),  d = Φ.length -/
def qspPoly : List ℝ → ℂ[X] × ℂ[X]
| []       => (1, 0)
| (φ :: Φ) => let (P, Q) := qspPoly Φ
              ( C (exp (I * φ)) * (X * P + (1 - X ^ 2) * Q),
                C (exp (-(I * φ))) * (P - X * Q) )
```
ここで $P^*$ は係数の複素共役（`P.map (starRingEnd ℂ)`），$Q^*(-x)$ はそれを $-X$ で合成したもの．右列は左列から決まる（帰納法で閉じる）ので再帰は 2 項で十分．
**定理 `seqR_eval`**: $\forall x\in[-1,1]$，$s=$ `Real.sqrt (1 - x^2)` として
`seqR Φ x = !![P.eval x, (Q.map conj).eval (-x) * s; Q.eval x * s, (P.map conj).eval (-x)]`．
**系**: (i) $\deg P\le d$, $\deg Q\le d-1$；(ii) parity $P\equiv d$, $Q\equiv d-1 \pmod 2$；(iii) $|P(x)|^2+(1-x^2)|Q(x)|^2=1$（ユニタリ性から）；(iv) `qspPoly (Φ.map Neg.neg) = (P.map conj, Q.map conj)`（Cor 18 で使用）．
等価な 4 項版（$P,Q_t,Q_b,P_b$，基底 $(1,0,0,1)$）: $P'=e^{i\phi}(xP+(1-x^2)Q_b)$，$Q_t'=e^{i\phi}(xQ_t+P_b)$，$Q_b'=e^{-i\phi}(P-xQ_b)$，$P_b'=e^{-i\phi}((1-x^2)Q_t-xP_b)$，帰納法で $Q_t=Q_b^*(-x)$，$P_b=P^*(-x)$ が閉じる．帰納法の仮定を強くしたいときはこちらを使う．$x=\cos\theta$ 版 `seqR_eval_cos`（$s=\sin\theta$）も用意．

### QSP-4 Chebyshev の閉形式位相（GSLW Lemma 9）（★★）
$\Phi = ((1-d)\pi/2, \pi/2, \dots, \pi/2)$ に対し $P_\Phi = T_d$（数値検証済；行列全体は $[[T_d,\ U_{d-1}s],[(-1)^{d+1}U_{d-1}s,\ (-1)^dT_d]]$，$U_{d-1}$ は第 2 種 Chebyshev）．証明: $e^{i\frac\pi2\sigma_z}R(x) = i\sigma_z R(x)$ は角 $\arccos x$ の回転なので $d$ 個の積は角 $d\arccos x$ の回転．`POLY-5` の $T_d(\cos\theta)=\cos d\theta$ で閉じる．Route A（exact パイプライン）の基盤．

### QSP-5 端点公式（GSLW Cor 8 moreover）（★）
$P_\Phi(\pm1) = (\pm1)^d\prod_j e^{i\phi_j}$；$d$ 偶なら $P_\Phi(0) = e^{-i\sum_j(-1)^j\phi_j}$．$x=\pm1$ で $R$ が対角，$x=0$ で $R=\sigma_x$ になることから．

### QSP-6 摂動補題（★）
$\|\mathrm{seqR}(\Phi,x)-\mathrm{seqR}(\Phi',x)\|\le\sum_j\|e^{i\phi_j\sigma_z}-e^{i\phi'_j\sigma_z}\|\le 2\sum_j|\phi_j-\phi'_j|$．ユニタリ積の telescoping．有理数位相と理論位相の差を評価するときに使う（Route B の補助）．

### QSP-7 存在定理（Phase 1 後半 or 後回し）
| ID | 内容 | GSLW | 難易度 |
|---|---|---|---|
| QSP-7a | Lemma 6: 偶・非負実多項式 $A$（$\deg\le 2k$）は $A = B^2+(1-x^2)C^2$ と書ける（parity 付き）．根の多重度と複素共役対の処理 | Lemma 6 | ★★★★ |
| QSP-7b | Thm 4: $P$ に対する相補多項式 $Q$ の存在 ⇔ (iv.a–c) | Thm 4 | ★★★ |
| QSP-7c | Thm 3 (⇐): (i)–(iii) を満たす $(P,Q)$ に対し $\Phi$ が存在（次数下げの帰納法，式 (6)–(8)） | Thm 3 | ★★★ |
| QSP-7d | Cor 8 / Cor 10: 反射規約・実多項式版の存在 | Cor 8, 10 | ★★ |

G2 のパイプラインには不要（位相は外部で求め証明書で検査）だが，言語の意味論「許容多項式は必ず実装できる」の根拠として Phase 6 までには欲しい．

---

## 3. 符号化層（Phase 2a / 4）

### ENC-1 射影ユニタリ符号化（GSLW Def 11 の前半）（★）
```lean
structure ProjUnitaryEncoding (ℋ : Type*) [Qudit ℋ] where
  U  : L ℋ
  hU : U† * U = 1 ∧ U * U† = 1
  Π  : L ℋ
  Π' : L ℋ            -- Π̃
  hΠ : IsProjective Π
  hΠ' : IsProjective Π'
def ProjUnitaryEncoding.encoded (E) : L ℋ := E.Π' * E.U * E.Π   -- A
lemma encoded_norm_le_one : ‖E.encoded‖ ≤ 1
```
Hermitian 版: `structure HermitianEncoding extends ProjUnitaryEncoding` with `Π' = Π ∧ encoded† = encoded`．

### ENC-2 ブロック符号化（GSLW Def 43）（★★）
```lean
/-- (α, a, ε)-block-encoding: ‖A − α (⟨0|^a ⊗ I) U (|0⟩^a ⊗ I)‖ ≤ ε -/
structure BlockEncoding (s a : ℕ) (α ε : ℝ) (A : Op s) where
  U   : Op (a + s)
  hU  : IsUnitary U
  hA  : ‖A - α • topLeftBlock a U‖ ≤ ε
```
`Op n` は $n$-qubit 作用素（`L (QubitSpace n)` または `Matrix (Fin n → Bool) …`，D1）．`toProjEncoding : BlockEncoding → ProjUnitaryEncoding` で $\Pi=\tilde\Pi=\ket0\bra0^{\otimes a}\otimes I$．

### ENC-3 LCU（GSLW Lemma 52 相当）（★★★）
状態準備 $V\ket0 = \sum_j\sqrt{y_j/\|y\|_1}\ket j$ と select $\sum_j\ket j\bra j\otimes U_j$ から $\sum_j y_jA_j$ の $(\|y\|_1\alpha,\ a+b,\ \|y\|_1\varepsilon)$-符号化．Cor 18 の $\Re P$ 実装では $j\in\{0,1\}$，$y=(1/2,1/2)$，$U_0=U_\Phi$，$U_1=U_{-\Phi}$，$V=H$．

### ENC-4 積（GSLW Lemma 53）（★★）
$(\alpha,a,\delta)$-符号化 $\times$ $(\beta,b,\varepsilon)$-符号化 $\Rightarrow$ $AB$ の $(\alpha\beta,\ a+b,\ \alpha\delta+\beta\varepsilon)$-符号化．

### ENC-5 制御化（GSLW Lemma 19 後半）（★★）
`controlled (altSeq Φ) = altSeq' (controlled phases)`: 制御ビット付きの交代列は位相ゲートだけを制御化すれば得られる（$n$ 奇なら $U$ を 1 回制御化）．Fig. 1c．

### ENC-6 例（★）
自明符号化（Def 44），ユニタリの符号化，対角行列，密度作用素の purification（Lemma 45）．回路層のテストに使う．

---

## 4. SVT 層（Phase 2a / 2b）

### SVT-1 交代列（GSLW Def 15）（★）
```lean
/-- 先頭から剥がす再帰．rest の長さが偶数なら e^{iφ(2Π̃−I)} U，奇数なら e^{iφ(2Π−I)} U† -/
def altSeq (E : ProjUnitaryEncoding ℋ) : List ℝ → L ℋ
| []       => 1
| (φ :: Φ) => (if Even Φ.length then phaseOp E.Π' φ * E.U else phaseOp E.Π φ * E.U†) * altSeq E Φ
```
検算: $n=1$: $e^{i\phi_1(2\tilde\Pi-I)}U$；$n=2$: $e^{i\phi_1(2\Pi-I)}U^\dagger e^{i\phi_2(2\tilde\Pi-I)}U$；$n=3$: Def 15 の odd 形．`altSeq_unitary`．

### SVT-2 位相作用素（★）
`phaseOp Π φ := exp(I φ) • Π + exp(-I φ) • (1 - Π)`（$=e^{i\phi(2\Pi-I)}$）．ユニタリ，$\Pi$ と可換，`phaseOp Π φ * Π = exp(I φ) • Π`．

### SVT-3 QET: Hermitian 符号化の固有値変換（★★★★，Phase 2a の中核）
**定理**: `E : HermitianEncoding`，$A = E.\text{encoded}$，$\Phi$ 長さ $n$，$(P,\_) = \texttt{qspPoly Φ}$ のとき
$$\Pi\,U_\Phi\,\Pi = P(A)\,\Pi\qquad(\texttt{Polynomial.aeval A P * E.Π}).$$
証明（ベクトル単位の帰納法）:
1. `LinearMap.IsSymmetric.eigenvectorBasis` を $A|_{\operatorname{ran}\Pi}$ に適用し ONB $\{\psi_i\}$，固有値 $\varsigma_i\in[-1,1]$（$\|A\|\le1$ から）．
2. $|\varsigma|<1$: $s:=\sqrt{1-\varsigma^2}$，$\psi^\perp := (I-\Pi)U\psi/s$．補題: $\|\psi^\perp\|=1$，$\Pi\psi^\perp=0$，
   $U\psi = \varsigma\psi + s\psi^\perp$，$U\psi^\perp = s\psi-\varsigma\psi^\perp$，$U^\dagger\psi = \varsigma\psi+s\psi^\perp$，$U^\dagger\psi^\perp = s\psi-\varsigma\psi^\perp$，
   $\mathrm{phaseOp}\,\Pi\,\phi$ は $\psi\mapsto e^{i\phi}\psi$，$\psi^\perp\mapsto e^{-i\phi}\psi^\perp$．
   （$U\psi^\perp$ の式は $\|U\psi\|=1$ と $\langle\psi,U\psi^\perp\rangle = \langle U^\dagger\psi,\psi^\perp\rangle$ と $A=A^\dagger$ から．）
3. **帰納補題**: `altSeq E Φ ψ = (seqR Φ ς) 0 0 • ψ + (seqR Φ ς) 1 0 • ψ^⊥`（列ベクトル $e_1$ への作用）．
4. $\Pi$ を掛け `QSP-3` で $P(\varsigma)\psi$．$|\varsigma|=1$ は $U\psi=\varsigma\psi$（$\|A\psi\|=\|U\psi\|$ から $(I-\Pi)U\psi=0$）と `QSP-5`．
5. $P(A)\psi_i = P(\varsigma_i)\psi_i$（`Polynomial.aeval` と固有ベクトル）．ONB 上で一致し，$\ker\Pi$ 上は両辺 0．

### SVT-4 ノルム補題（★★）
$\|g(A)\Pi\|\le\sup_{x\in[-1,1]}|g(x)|$（Hermitian, $\|A\|\le1$）．CFC の `norm_cfc_le` 系か固有分解で．一般 QSVT 版は `SVT-6` の後．

### SVT-5 SVD 無しの特異値変換（D3）（★★）
```lean
def svTransform (P : ℂ[X]) (E : ProjUnitaryEncoding ℋ) : L ℋ :=
  let A := E.encoded
  if IsOdd P then A * aeval (A† * A) (sqrtPart P)            -- P = x R(x²)
  else E.Π * aeval (A† * A) (sqrtPart P) * E.Π                -- P = R(x²)
```
補題: Hermitian かつ $\tilde\Pi=\Pi$ なら `svTransform P E = aeval A P * Π`（`SVT-3` との整合）．

### SVT-6 射影ユニタリの SVD（GSLW Def 11，必要最小限）（★★★）
$A^\dagger A|_{\operatorname{ran}\Pi}$ の固有 ONB $\{\psi_i\}$，固有値 $\varsigma_i^2$．$\varsigma_i>0$ なら $\tilde\psi_i := A\psi_i/\varsigma_i$ は正規直交で $\operatorname{ran}\tilde\Pi$ に入る．`svTransform P E ψ_i = P(ς_i) ψ̃_i`（奇），`= P(ς_i) ψ_i`（偶）．

### SVT-7 QSVT（GSLW Thm 17）（★★★★，Phase 2b の中核）
**定理**: $n$ 奇なら $\tilde\Pi U_\Phi\Pi = \texttt{svTransform } P_\Phi\ E$，$n$ 偶なら $\Pi U_\Phi\Pi = \texttt{svTransform } P_\Phi\ E$．
証明: `SVT-3` と同型だが 2 組の対 $\{\psi,\psi^\perp\}$（$\Pi$ 側），$\{\tilde\psi,\tilde\psi^\perp\}$（$\tilde\Pi$ 側）を $U,U^\dagger$ が交互に写す（GSLW 式 (29)(30)）:
$U\psi=\varsigma\tilde\psi+s\tilde\psi^\perp$，$U\psi^\perp = s\tilde\psi-\varsigma\tilde\psi^\perp$，$U^\dagger\tilde\psi = \varsigma\psi+s\psi^\perp$，$U^\dagger\tilde\psi^\perp = s\psi-\varsigma\psi^\perp$．
端点: $\varsigma=0$（$\tilde\psi$ 未定義．$U\psi\in\ker\tilde\Pi$ なので奇数長なら $\tilde\Pi U_\Phi\psi=0=P(0)$，偶数長なら位相のみで `QSP-5`），$\varsigma=1$（$U\psi=\tilde\psi$）．

### SVT-8 実多項式（GSLW Cor 18）（★★）
`ENC-3` で $U_\Phi,U_{-\Phi}$ を $1/2$ ずつ LCU: $(\bra+\otimes\tilde\Pi)(\ket0\bra0\otimes U_\Phi+\ket1\bra1\otimes U_{-\Phi})(\ket+\otimes\Pi) = \Re[P]^{(SV)}(A)$．`qspPoly (−Φ) = (P^*, …)` の補題が必要．

### SVT-9 ロバスト性（GSLW Lemma 22, 23）（★★★，任意）
$\|P^{(SV)}(A)-P^{(SV)}(\tilde A)\|\le 4n\sqrt{\|A-\tilde A\|}$；特異値が 1 から離れていれば線形．近似ブロック符号化の誤差伝播に使う．

---

## 5. IR・回路層（Phase 4 / 5）

### IR-1 抽象 IR（★★）
```lean
inductive Expr : (s : ℕ) → Type
| oracle  (E : BlockEncoding s a α ε A) : Expr s
| qsvt    (Φ : List ℝ) (e : Expr s) : Expr s          -- 奇数長/偶数長で Π̃/Π を自動選択
| lcu     (y : Fin m → ℝ) (es : Fin m → Expr s) : Expr s
| prod    (e₁ e₂ : Expr s) : Expr s
| control (e : Expr s) : Expr (s+1)
| adjoint (e : Expr s) : Expr s
def Expr.denote : Expr s → Σ a α ε, BlockEncoding s a α ε (…)   -- 定理を束ねた依存型
structure Resources where (queries ancilla phaseGates cpiNot : ℕ)
def Expr.cost : Expr s → Resources
```
`qsvt` の意味は `SVT-7`（または `SVT-3`）+ `SVT-8` のインスタンス．`cost (qsvt Φ e) = ⟨Φ.length * e.cost.queries, e.cost.ancilla + 1, Φ.length, Φ.length⟩`（Lemma 19）．

### IR-2 計算量の自動化（★★）
`simp` 補題集 `cost_qsvt`, `cost_lcu`, `cost_prod` で `Expr.cost` を数値に落とす．G3 の実体．

### CIRC-1〜6 回路層
| ID | 内容 | 難易度 |
|---|---|---|
| CIRC-1 | ゲート `Gate n`（H, X, Z, Rz φ, CNOT, MCX, oracle, oracle†, cΠNOT）と `Circuit n := List (Gate n)`．添字 `Fin n → Bool`．Kronecker・reindex・制御化の補題 | ★★★ |
| CIRC-2 | `denote : Circuit n → Matrix …`，ユニタリ性保存，`denote_append` | ★★ |
| CIRC-3 | Lemma 19 / Fig. 1b: `phaseOp Π φ = cΠNOT * (I ⊗ Rz(−2φ)) * cΠNOT`（補助 1 qubit），Fig. 1c 制御版 | ★★★ |
| CIRC-4 | `compile : Expr s → Circuit (s + ancilla)`，`compile_correct`，`compile_cost` | ★★★★ |
| CIRC-5 | $\Pi=\ket0\bra0^{\otimes a}\otimes I$ のとき `cΠNOT = MCX`（$O(a)$ ゲート） | ★★ |
| CIRC-6 | OpenQASM 3 出力（untrusted）と Qiskit 照合テスト | ★ |

---

## 6. 証明書層（Phase 3）

### FE-1 前処理（★★）
```lean
structure Admissible (d : ℕ) where
  P : ℂ[X]; hdeg : P.natDegree ≤ d; hpar : HasParity P d; hbound : supNorm P ≤ 1
def normalize (f : ℂ[X]) : ℝ × List (ℂ × Admissible _)   -- (α_f, LCU 係数と許容成分)
theorem normalize_spec : f = α_f • Σ c_j • P_j
```
$\alpha_f$ は係数の $\ell^1$ ノルム等の計算可能な上界で保守的に取る（`supNorm` は非計算的）．複素 $f$ は実部・虚部に分け，各々 `SVT-8` で実装し LCU（係数 $1, i$）．

### CERT-A Route A: Chebyshev-LCU（exact）（★★）
`chebCoeff`（POLY-6）で $f=\sum_{k\le d}c_kT_k$．各 $T_k$ は `QSP-4` の位相で `qsvt`，`lcu` で合成．`denote = f^{(SV)}(A)/\|c\|_1$，`cost.queries = Σ k ≤ d(d+1)/2`，誤差 0．

### CERT-B Route B: 位相の証明書（★★★★）
```lean
structure PhaseCert (d : ℕ) where
  Φ : Fin d → ℚ            -- 二進小数で受け取る
  f : ℂ[X]; ε : ℚ
def check (c : PhaseCert d) : Bool    -- 区間演算: Σ_k |chebCoeff (P_Φ) k − chebCoeff f k| ≤ ε を検査
theorem check_sound (c) (h : check c = true) :
  ∀ x ∈ Icc (-1:ℝ) 1, ‖(qspPoly (c.Φ.map (↑))).1.eval x - c.f.eval x‖ ≤ c.ε
```
実装方針: `qspPoly` の再帰を Chebyshev 係数ベクトル上の再帰に書き直す（$xT_k$, $(1-x^2)T_k$ の線形則）．係数は $\{\cos\phi_j,\sin\phi_j\}$ の多項式なので，区間 `cos`/`sin`（LeanCert）で囲い込む．健全性は「区間演算の各ステップが真値を含む」の帰納法 + `POLY-4` の $\ell^1$ 上界．

### CERT-C 作用素への持ち上げ（★）
`SVT-4` から $\|P_{\tilde\Phi}^{(SV)}(A)-f^{(SV)}(A)\|\le\varepsilon$．`BlockEncoding` の `hA` を合成．

---

## 7. 応用層（Phase 6）

| ID | 内容 | GSLW | 必要な多項式 | 難易度 |
|---|---|---|---|---|
| APP-1 | 特異ベクトル変換・固定点振幅増幅 | Thm 26, 27 | 符号関数近似（Lemma 25，Route B） | ★★★ |
| APP-2 | 閾値射影・特異値判別 | Thm 31, 32 | 矩形関数近似（Lemma 29） | ★★★ |
| APP-3 | 擬似逆・線形方程式 | Lemma 40, Thm 41 | $1/x$ 近似 $g(x)=4\sum_j(-1)^j[\cdot]T_{2j+1}$（明示的．近似次数定理の最初の形式化候補） | ★★★★ |
| APP-4 | Hamiltonian simulation | Thm 58 | Jacobi–Anger（Bessel 係数，Route B） | ★★★ |
| APP-5 | ループ例: (a) 閾値二分探索で基底エネルギー推定（古典ループ × APP-2），(b) QSVT の反復合成 $P\circ Q$（Lemma 53 + SVT-7） | — | — | ★★★ |
| APP-6 | 後選択の成功確率と POVM，固定点振幅増幅による除去パターン | Thm 27 | — | ★★ |

---

## 8. 依存関係（要約）

```
POLY-1..6 ─┬─► QSP-1 ─► QSP-2
           ├─► QSP-3 ─┬─► QSP-4 (Chebyshev 位相) ──► CERT-A ─┐
           │          ├─► QSP-5 ─► SVT-3 (QET) ─► SVT-4 ─► CERT-C ├─► IR-1/2 ─► CIRC-4 ─► APP-*
           │          └─► QSP-6 ─► CERT-B ──────────────────────┘
ENC-1 ─► SVT-1/2 ─► SVT-3 ─► SVT-5/6 ─► SVT-7 (QSVT) ─► SVT-8 (Cor 18) ─► SVT-9
ENC-2..6 ─► IR-1 ─► CIRC-1..5
QSP-7 (存在定理) は独立．Phase 6 までに．
```
