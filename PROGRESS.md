# PROGRESS

進捗ログ（新しいものを上に）．計画は [dev/plan.md](dev/plan.md)，仕様 ID は
[dev/formal-spec.md](dev/formal-spec.md) を参照．

## 2026-10-09 (9) — 線形方程式 + 固定点振幅増幅（Thm 41 相当，heavy）

- `QSVTHeavy/FixedPointAAD01.lean`: $\delta=0.1$ の証明済み位相（35 個）による固定点 AA（plateau $0.9755$）．
- `QSVTHeavy/InverseAA.lean`: 擬似逆ブロック（435 クエリ）+ AA（35 回）．スペクトル台が $|\lambda|\ge1/4$ の $b$ に対し，初期振幅 $\approx0.112\ge0.1$，
  成功振幅 $\ge0.975$（確率 $\ge0.95$），良い成分は正規化した $A^{-1}b$ の $c$ 倍（$c=79/80$）に $0.02$ 以内．`encoded_idealInv` で理想状態が $A^{-1}b$ に比例することを証明．15,225 クエリ．
- これで GSLW の主要応用（Thm 27, 31, 41, 58）がすべて「証明書 + 定理」の形で揃った（定数は近似多項式の plateau に依存）．

## 2026-10-09 (8) — 振幅増幅との結合（Thm 58 相当），$\delta=0.1$ の証明書，重い証明書の分離

- `Examples/Compose.lean`: 結合の共通機構（正規化，スペクトル関数計算と Parseval による $\|p(A)b\|$ の上下界，Route A 回路から固定点 AA の入力を作る）．
- `Examples/EvolutionAA.lean`: $e^{-2iA}b$ の準備 + 固定点振幅増幅．初期振幅 $a\ge(1-2\varepsilon)/\|c\|_1\approx0.41$，成功振幅 $\ge0.869$，良い成分は理想状態の $c$ 倍に $0.0237$ 以内，1386 クエリ．
- `QSVTHeavy/`（新ライブラリ，既定ターゲット外）: $\delta=0.1$ の符号関数近似（次数 35，LP），位相証明書（pyqsp `sym_qsp`，kernel 265 s）．線形方程式の AA 結合に使う（初期振幅 $\approx0.11<0.15$ のため sign21 では不足）．
  CI には `[heavy]` 付きコミットまたは手動実行でのみ走るジョブを追加．
- 判断: doc-gen4 は不採用（ユーザー指示）．重いオプションは既定で省略．

## 2026-10-09 (7) — 相補多項式の存在（GSLW Lemma 6・Thm 5・Cor 10）

- `QSP/Complementary.lean`: Lemma 6 を GSLW の大域的な根の分解ではなく，述語 `SOSRep k A`（$A=B^2+(1-x^2)C^2$ と次数・parity）の積閉性
  （Brahmagupta–Fibonacci 恒等式）と，複素根 $s$ の $s^2$ による 3 分類（非実: 4 次因子，実で $(0,1)$ 外: 2 次因子，$(0,1)$ 内: 符号変化論法で重根）
  の強帰納法で証明．Thm 5（実版）と Cor 10 を導出し，`exists_phases` と合わせて「許容な実多項式は必ず位相列で実現できる」が Lean で閉じた．
- CI の `no-sorry` ジョブを失敗扱いに変更（ライブラリは sorry なし）．
- 規模: Lean 約 22,300 行．GSLW 3.1 節（Thm 3–5，Lemma 6，Cor 8–10），3.2 節（Thm 17，Cor 18，Lemma 19）が形式化済み．
- 残り: Thm 4 の必要性方向，近似次数の漸近定理（Lemma 25/29/40），振幅増幅との結合（Thm 41/58 の残り），IR の `prod`．

## 2026-10-09 (6) — 閾値射影，ループ例，符号化の積，$k$ qubit レジスタ，CLI

- **APP-2 閾値射影**: 次数 32 の偶多項式（LP で証明書余裕を最大化），3 つの kernel 証明書（各 35–55 s），`Examples/Threshold.lean`（固有値の窓フィルタ，528 クエリ）．
- **APP-5 ループ**: `Lang/Loop.lean`（`iterate`，`qsvtIter`: クエリ $|\Phi|^k$，`spec = compIter`，掃引の総クエリ，後選択の期待クエリ），`Examples/Loop.lean`（反復 sign，二分探索スケルトンと窓プログラム）．
- **ENC-4 積**（GSLW Lemma 53）: `Encoding/Swap.lean`，`Encoding/Product.lean`（`topLeft₂_prodU`）．IR への統合は入れ子補助空間の一般化が必要なため保留．
- **$k$ qubit レジスタ**: `Qubit/RegBridge.lean`（`regEquiv`，`liftReg_lcu`，`liftReg_chebLCU`）で Route A 回路も qubit 化．
- **CLI** `tools/qsvt`: `info`/`qasm`/`check`/`emit-cert`．証明書の kernel 検査は生成した Lean モジュールで行う（trust story は `tools/README.md`）．
- 規模: Lean 約 21,000 行，sorry なし，公理は標準 3 つ．CI は LeanCert 込みで成功．
- 進行中: QSP-7b（相補多項式の存在，Thm 4/Lemma 6）．完全に証明できた補題のみ取り込む方針．

## 2026-10-09 (5) — 固定点振幅増幅，線形方程式，言語層の表面構文

- **APP-1 固定点振幅増幅（GSLW Thm 27）**: `SVT/SingularPair.lean`（任意の特異ベクトル対に対する 2 フレーム補題），`SVT/RealPolyGeneral.lean`（一般符号化の Cor 18），
  `Examples/FixedPointAA.lean`: $U$，良い部分空間の射影 $G$，$G U\psi_0 = a\,\psi_G$ から rank-1 符号化を作り，証明済み sign21 位相で $a\ge0.15\Rightarrow$ 成功振幅 $\ge0.869$（21 クエリ，86 ゲート）．
- **APP-3 線形方程式の多項式ステップ**: $\kappa=4$，次数 29 の奇多項式で $c/(\kappa x)$（$c=3/4$）を相対誤差 $10^{-3}$ で近似（LP による minimax，LeanCert Bernstein 証明書 115 s）．
  `Examples/Inverse.lean`: 固有値 $|\lambda|\ge1/4$ で $A^{-1}$ 方向に作用（435 クエリ，Route A）．$c=1$ は $|p|\le1$ の制約で不可能に近い（折れ点）という知見を docstring に記録．
- **LANG-1 言語層**: `ExprQ`（有理データ）と記法 `qsvt[Φ] U₀`，`poly[l] U₀`，コスト関数と IR との一致定理，`baseQ_eq`（表面構文で書いたプログラムに正しさ定理が付く），
  `#qsvt_info` コマンド（クエリ数・補助次元・次数上界・スケール・ゲート数・OpenQASM を表示）．
- 規模: Lean 約 18,500 行，sorry なし，公理は標準 3 つ．
- 未着手: APP-2（閾値射影），APP-5（ループを含む例），ENC-4（積）と IR の `prod`，$m$ レジスタの qubit 橋渡し，QSP-7b（相補多項式の存在）．

## 2026-10-09 (4) — 一般 QSVT 定理（G1 達成），qubit 層とコンパイル，$e^{-2iA}$

- **SVT-6/7 `qsvt_odd`/`qsvt_even`**（`QSVT/SVT/QSVT.lean`）: 任意の射影ユニタリ符号化で $\tilde\Pi U_\Phi\Pi = P_\Phi^{(SV)}(A)$（奇），$\Pi U_\Phi \Pi = P_\Phi^{(SV)}(A)$（偶）．
  SVD は $A^\dagger A$ の固有基底から最小限に構成（`SVD.lean`），2 フレームの帰納法（`TwoFrame.lean`）は $\sigma\in\{0,1\}$ でも場合分け不要（$(\sqrt0)^{-1}=0$ の規約で枠ベクトルが消える）．
  Hermitian 版 `qet` は系として再導出（`qet_of_qsvt`）．
- **CIRC-1/4/5/6**（`QSVT/Qubit/`）: qubit レジスタ `Qubits n = EuclideanSpace ℂ (Fin n → Bool)`，等長同型 `ancEquiv : Anc (Qubits n) ≃ Qubits (n+1)`，
  `liftAnc (cpiNot (diagProj d)) = ctrlX d`（$C_\Pi$NOT = 多重制御 X，一般の対角 0/1 射影で証明），`compileQ_qsvtReal`（qubit ゲート列の意味が Route B ユニタリに一致），
  OpenQASM 3 出力 `toQasm`（untrusted．sign21 の回路は 86 ゲート: `negctrl(2) @ x`，`rz`，`h`，opaque な `U_oracle`）．
- **APP-4 完成**: $\sin 2x$ の証明書（Taylor 橋渡し + Bernstein）と複素係数 Route A による $e^{-2iA}/\|c\|_1$（誤差 $2\times10^{-6}/\|c\|_1$，66 クエリ）．
- 規模: Lean 約 16,000 行，sorry なし，公理は標準 3 つ．`lake build` 3848 ジョブ．
- 次: 固定点振幅増幅（Thm 27，rank-1 符号化 + `qsvt_odd`），擬似逆 $1/x$ の証明書と線形方程式の例，言語層の表面構文（`#qsvt_info`），ENC-4 積と IR の `prod`．

## 2026-10-09 (3) — Route B 完成（M4），証明書付き応用例 2 件

- **CERT-B 完成**: LeanCert v4.34.1 を依存に追加（`lake update leancert` 11 s，LeanCert ソースビルド 3 分 22 秒，以後キャッシュ）．
  - B1 `Certificate/Bound.lean`, `Sign21.lean`: 明示多項式の区間評価を `leancert (trust := kernel)`（Bernstein 証明書，`decide +kernel`）で証明．
    次数 21 の符号関数近似（qsppack の目標多項式）: $[-1,1]$ で $|p|\le1$（25 s），$[0.15,1]$ で $|p-c|\le0.0236$（40 s），$c\approx0.8924$．
  - B2 `ChebC.lean`, `PhaseCheck.lean`: `qspPoly` の Chebyshev 基底再帰を ℂ 上（仕様層）と `IntervalRat` 上（計算層）で定義し，
    `checkRe Φ̃ t ε n : Bool` と健全性 `checkRe_sound`（$\|\Re P_{\tilde\Phi}-\sum t_kT_k\|_\infty\le\varepsilon$）．次数 21 の位相で $\varepsilon=10^{-12}$ を kernel 45 s で検査．
    注: ソルバー出力は $\Re P$ のみ目標に合う（$\Im P\approx0.7$）ので実部版 `checkRe` が本命．
- **APP-1**: `Examples/Sign21.lean`（Route A, 231 クエリ）と **`Examples/Sign21RouteB.lean`（Route B, 21 クエリ・補助 1 qubit）**．
  固有値 $\lambda\ge0.15$ の固有ベクトルは $\pm c$ 倍に $10^{-12}+0.0236$ 以内（`signB_apply_pos`）．資源数は `compileQsvtReal` の定理から（oracle 21，$C_\Pi$NOT 42，位相 21，H 2）．
- **APP-4-lite**: `Certificate/CosExample.lean`, `Examples/CosEvolution.lean`: $\cos 2x$ の次数 10 近似（Jacobi–Anger）．LeanCert は `Real.cos` との差を直接は証明できず
  （区間演算の依存問題），次数 16 の Taylor 多項式を橋渡しにして Mathlib の `Complex.exp_bound'` で閉じた．全固有ベクトルで $10^{-6}$ 以内，55 クエリ．
- 規模: Lean 約 13,000 行，sorry なし，公理は標準 3 つ．`lake build` 全体 3838 ジョブ（増分 6 s，証明書モジュールは 45 s）．
- 進行中: `Qubit/`（qubit レジスタ `Fin n → Bool` と `Anc`/`Reg` の等長同型，ゲート，$C_\Pi$NOT の多重制御 X への対応）．
- 次: 複素 LCU で $e^{-itA}$（sin 部），ENC-4 積と IR の `prod`，qubit 回路の OpenQASM 出力，固定点振幅増幅（Thm 27）の定式化．

## 2026-10-09 (2) — Route A 完成（M3），IR・回路層・存在定理，Route B 着手

- **CERT-A `routeA`**（`QSVT/Pipeline/ChebLCU.lean`）: 計算可能な入力 `PolyQC` → Chebyshev 係数 → 各 $T_k$ を閉形式位相の QET で実装 →
  Householder 状態準備 + $m$ 項 LCU で合成．`regTopLeft (regP * chebLCU * regP) = ‖c‖₁⁻¹ • (f(A) * P)`（exact）．G2 の最初の達成．
- **IR-1/2**（`QSVT/IR/`）: `Expr`（`oracle`，`qsvtReal Φ`，`chebLCU c`），`denote`（符号化の合成），`compress`，健全性
  `compress_aeval_mul_P`（`WellScaled` が必要），`queries`/`ancillaDim`，`natDegree_spec_le`．
  設計上の発見: LCU 出力を次段の QSVT に渡すときの射影は `|0⟩⟨0| ⊗ Π`（`atZero`）でなければならない（GSLW Def 43 と同じ）．
- **CIRC-1/3**（`QSVT/Circuit/`）: $C_\Pi\mathrm{NOT}$ ガジェット `gadget_eq`（Fig. 1b），`gadgetSeq_eq = blockDiag (U_Φ) (U_{−Φ})`，
  原始ゲート列 `compileQsvtReal` と `denote_compileQsvtReal`，資源数定理（GSLW Lemma 19 の $n, 2n, n$）．
- QSP-2/6（`Conversion.lean`，`Perturb.lean`），QSP-7c（`Existence.lean`: Thm 3 ⇐）．
- README に主要定理の表と使い方を追加．
- 進行中: Route B1（LeanCert v4.34.1 を依存に追加，次数 21 の符号関数近似の sup ノルム証明書を kernel 検証）．
- 規模: Lean 約 9,300 行，sorry なし．`lake build` 増分 6 s（LeanCert 追加後はソースビルド約 5 分が初回に加わる）．

## 2026-10-09 — Phase 2a (QET) 完了，Cor 18・LCU・Chebyshev 変換が揃う（M2 達成，M3 組み立て中）

- **SVT-3 `qet`**（`QSVT/SVT/QET.lean`）: $P\,U_\Phi\,P = P_\Phi(A)\,P$ を Hermitian ブロック符号化で証明（SVD 不要，固有ベクトル単位の帰納法）．
  `qspPoly_chebPhases`（$P_{\text{cheb}(d)} = T_d$，無限個の点での一致から多項式の等式）と `qet_chebyshev`．
- SVT-4 `NormBound.lean`（$\|p(A)x\|\le\|p\|_\infty\|x\|$，作用素ノルム版も），SVT-5 `SVTransform.lean`（SVD 不要の `svTransform`，Hermitian で `aeval A p * P` に一致）．
- SVT-8 `RealPoly.lean`: `qet_real`（GSLW Cor 18）と合成子 `HermitianEncoding.qsvtReal`（出力が再び `HermitianEncoding (Anc ℋ)`）．
- ENC-2/3: `Ancilla.lean`/`LCU.lean`（1 補助 qubit = 直和 `WithLp 2 (ℋ × ℋ)`，2 項 LCU），`Register.lean`/`LCUm.lean`
  （$m$ レジスタ = `PiLp 2`，`matOp`/`selectOp`，Householder 状態準備，`lcu_complex`）．
  注: `topLeft` の名前衝突（Ancilla と Register）を `regTopLeft` への改名で解消．パイプ経由のビルド確認で失敗が隠れた反省から，
  以後は `lake build` の終了コードを直接見る．
- POLY-6 `ChebCoeff.lean`: 計算可能な Gauss 有理係数多項式と単項式→Chebyshev 変換（`#eval` 可，`decide +kernel` で検算）．
- 進行中: `Pipeline/ChebLCU.lean`（Route A: `routeA` 定理 = G2 の最初の達成），`QSP/Conversion.lean`，`QSP/Perturb.lean`．
- 規模: Lean 約 6,000 行，全モジュール sorry なし，公理は標準 3 つのみ．`lake build` 増分 6 s．

## 2026-10-08 — Phase 0 完了，Phase 1 (QSP) 完了，Phase 2a (QET) 組み立て中

subagent による並列開発（1 エージェント＝1 ファイル集合，親がコミット）で進めた．
全モジュール sorry なし，公理は標準 3 つのみ（各テストファイルで `#print axioms` 監査）．

### Phase 0（済）
- リポジトリを `auto-res/lean-qsvt` へ移管．開発ブランチ `ss`（`00note/prompt.md` は `ss` のみ）．
- 調査 `dev/survey.md`: LeanCert v4.34.1 採用（kernel 検証の区間演算），lean-quantum は
  v4.34.1 で `QuantumChannel` が壊れるため `QuantumState` 相当を `QSVT/Operator/Basic.lean` に複製，
  Mathlib に SVD 無しを確認．ツール選定は `dev/tooling.md`．
- 数値検算 `tools/phases/`: GSLW 式 (16) の符号誤りを発見（正: $W=i\,e^{-i\pi/4\sigma_z}Re^{-i\pi/4\sigma_z}$），
  反射規約の多項式再帰を確定（$Q$ は左下成分），pyqsp / qsppack の規約を記録．

### Phase 1（済）: `QSVT/QSP/`
- QSP-3 `Poly.lean`, `Structure.lean`: `qspPoly` と評価定理 `seqR_eval`，次数・parity・単位恒等式，`qspPoly_neg`．
- QSP-4 `Chebyshev.lean`: `chebPhases d` で `seqR` の全行列が $[[T_d, U_{d-1}s],[\pm U_{d-1}s, \pm T_d]]$．
- QSP-5 `Endpoints.lean`: $x=\pm1, 0$ の閉形式．

### 多項式層（済）: `QSVT/Polynomial/`
- `Parity.lean`（parity 補題を集約），`SqrtPart.lean`（`evenRoot`/`oddRoot`），`SupNorm.lean`，
  `Chebyshev.lean`（`ChebSeries`，`supNorm_toPoly_le_l1`）．

### Phase 2a（進行中）: `QSVT/Encoding/`, `QSVT/SVT/`
- ENC-1 `Projected.lean`（射影は `P`/`P'`），SVT-2 `PhaseOp.lean`，SVT-1 `AltSeq.lean`．
- SVT-3 部品: `EigenBasis.lean`（ran P 上の固有基底，`ext_of_eigenVec`），`TwoVector.lean`
  （関係式 (R0)–(R5)，`altSeq_apply_eigen`，`proj_altSeq_apply_eigen`）．
  注: Hermitian の場合でも $\psi^\perp$（$U^\dagger$ 側）と $\tilde\psi^\perp$（$U$ 側）は位相だけ異なり得るので両方を使う．
- 進行中: `QET.lean`（`qet`: $P\,U_\Phi\,P = P_\Phi(A)\,P$），`NormBound.lean`（SVT-4），`SVTransform.lean`（SVT-5），
  `Ancilla.lean`/`LCU.lean`（D8: 補助 qubit を直和で表現，2 項 LCU）．

### ビルド
- `lake build` 2775 ジョブ，増分 6 s．`lake test` 8 s．

### 次のアクション
- `qet` 完成後: Cor 18（`SVT-8`，実多項式）を `lcu2` と `qspPoly_neg` で組み立てる．
- Route A（CERT-A）: `ChebSeries` の各 $T_k$ を `chebPhases k` の QET で実装し，$m$ 項 LCU（`PiLp`）で合成．
- IR-1/2: コンビネータとコスト関数．QSP-2 の Lean 化は Route B 着手時．

## 2026-10-08 — Phase 0: プロジェクト骨組みの作成

### 環境
- Lean ツールチェーン: `leanprover/lean4:v4.34.1`（`lean-toolchain` に固定）．
- Mathlib: `leanprover-community/mathlib` タグ `v4.34.1`
  （commit `d13f23b723b8a846827a245b89c10fc7d3f11612`）．`lake-manifest.json` に固定．
- `lakefile.toml`: パッケージ `lean-qsvt`，`defaultTargets = ["QSVT"]`，
  `relaxedAutoImplicit = false`，`weak.linter.mathlibStandardSet = true`，
  `pp.unicode.fun = true`，`maxSynthPendingDepth = 3`，
  header linter のライセンス行を MIT に設定（`weak.linter.style.header.license`）．
  ライブラリ `QSVT`（`QSVT/`）と テストライブラリ `QSVTTest`（`test/`，`testDriver`）．
- `.gitignore`: `.lake/`, `*.olean`, `.DS_Store`, `site/`, `__pycache__/`．

### ビルド状況（ローカル，macOS）
- `lake update`: 273 s（Mathlib + 依存 8 パッケージの clone．post-update hook で
  `~/.cache/mathlib` から 8907 ファイルを展開，約 40 s）．
- `lake exe cache get`: 6 s（ダウンロード 0 件，すべてローカルキャッシュ済）．
- `lake build`: 成功，21 s（1967 ジョブ，Mathlib は全てキャッシュ）．
- `lake test`: 成功，8 s．
- Mathlib をソースからビルドしていない．

### 追加したモジュール
- `QSVT.lean` — ルート（全モジュールを import）．
- `QSVT/QSP/Conventions.lean`（QSP-1）— `namespace QSVT.QSP`:
  `M₂`, `Rref`, `phaseZ`, `seqR`, `Wrot`, `seqW` の定義と補題
  `seqR_nil`, `seqR_cons`（simp），`phaseZ_mul_phaseZ`, `phaseZ_zero`,
  `phaseZ_conjTranspose`, `phaseZ_neg_mul_phaseZ`, `phaseZ_mul_phaseZ_neg`,
  `phaseZ_mem_unitaryGroup`, `Rref_conjTranspose`, `Rref_mul_Rref`,
  `Rref_mem_unitaryGroup`, `seqR_mem_unitaryGroup`．**sorry なし**．
- `QSVT/Polynomial/Parity.lean`（POLY-1, POLY-2）— `namespace QSVT.Poly`:
  `IsEven`, `IsOdd`, `evenPart`, `oddPart`（係数 `Finsupp` の `filter` で定義），
  `coeff_evenPart`, `coeff_oddPart`（simp），`evenPart_add_oddPart`,
  `isEven_evenPart`, `isOdd_oddPart`，一意性 `evenPart_eq_of_add`, `oddPart_eq_of_add`，
  `IsEven.evenPart_eq`, `IsOdd.oddPart_eq`．**sorry なし**．
- `test/QSVTTest.lean` — `example`/`#guard` による回帰テストと，
  `#guard_msgs in #print axioms` による公理監査（標準 3 公理のみ）．

### CI
- `.github/workflows/ci.yml`: `leanprover/lean-action`（sha 固定）で
  `use-mathlib-cache: true`, `build: true`, `test: true`, `lint: false`．
  push / pull_request（全ブランチ）で実行．
- ジョブ `no-sorry`: `QSVT/` 以下の `sorry` を grep して検出．当面は
  `continue-on-error: true`（開発初期の sorry を許容）．sorry-free が定着したら false に戻す．

### Mathlib v4.34.1 で気づいた API メモ
- `AddMonoidAlgebra` は構造体（`ofCoeff :: coeff : M →₀ R`）になっており，
  `Polynomial.coeff : R[X] → ℕ →₀ R`．多項式の係数フィルタは
  `⟨⟨P.toFinsupp.coeff.filter p⟩⟩` と書く．
- `Mathlib.Algebra.Polynomial.Degree.Definitions` は消滅（`Degree/Defs.lean` 等に分割）．
- `Mathlib.Data.Complex.Basic` は deprecated → `Mathlib.Basic.Complex.Basic`．
- `if_pos`/`if_neg` は deprecated → `ite_eq_left`/`ite_eq_right`．
- `Matrix.Notation`（`!![...]`, `Matrix.mul_fin_two`）は `Mathlib.LinearAlgebra.Matrix.Notation`．

### 次のアクション
- QSP-2（規約変換 `Wrot = i • phaseZ (-π/4) * Rref * phaseZ (π/4)`）と
  QSP-3（`qspPoly` と評価定理 `seqR_eval`）の定義ファイル・定理ファイルを分けて追加．
- POLY-3（`sqrtPart`，偶多項式 `= R.comp (X^2)`）．
- lean-quantum 依存可否の調査（`dev/survey.md`）．
