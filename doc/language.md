# lean-qsvt 言語仕様と使い方

- 対象読者: この言語で QSVT（量子特異値変換）に基づくアルゴリズムを書き，回路とその正しさの定理を得たい人．
- 前提知識: ブロック符号化（GSLW, arXiv:1806.01838 Def. 43）と多項式変換の考え方．Lean 4 の基本操作．
- 本文書の対応モジュール: `QSVT/Lang/`（言語），`QSVT/IR/`（中間表現と健全性），`QSVT/Qubit/`（回路出力），`QSVT/Certificate/`（証明書），`tools/qsvt`（CLI）．

---

## 1. この言語でできること

プログラムは「オラクル $U_0$（Hermitian 作用素 $A_0$ のブロック符号化）に多項式変換を施す手順」を記述します．
ユーザーは量子回路を意識せず，**施したい多項式（または QSP の位相列）**だけを書きます．すると

1. **意味**: プログラムが実装する作用素が定理として確定します．補助量子ビットをすべて $|0\rangle$ に射影した「基底ブロック」が
   $$\text{base} = \frac{1}{\text{scale}}\;\mathrm{spec}(A_0)\,\Pi_0$$
   であること（`baseQ_eq`）．ここで `spec` はプログラムから計算される多項式，`scale` は LCU による正規化定数です．
2. **コスト**: オラクル $U_0, U_0^\dagger$ の呼び出し回数 `queriesQ`，補助レジスタの次元 `ancillaDimQ`，多項式の次数上界 `degreeBoundQ` が計算可能な関数として得られ，意味論上の値と一致することが定理（`queriesQ_eq` など）で保証されます．
3. **回路**: 単一ステップのプログラム `qsvt[Φ] U₀` は GSLW Lemma 19 のゲート列（$C_\Pi\mathrm{NOT}$・位相・Hadamard・オラクル）にコンパイルされ，qubit 回路としての意味が一致すること（`compileQ_qsvtReal`）が証明されています．OpenQASM 3 として出力できます（出力文字列自体は検証対象外）．

**信頼境界**: Lean の定理（意味・コスト・コンパイルの正しさ・証明書の健全性）は信頼されます．位相列を求める数値ソルバー，CLI の構文解析，OpenQASM 文字列は信頼されません．数値由来の入力（位相列）は Lean カーネルで検査する証明書（§5）で裏付けます．

---

## 2. 準備

```lean
import QSVT
open QSVT.Lang          -- 記法 U₀, qsvt[..], cheb[..], poly[..] を有効化
```

ビルドは `lake exe cache get` のあと `lake build`（既定ターゲット．数分かかる証明書は `lake build QSVTHeavy` で別途）．

**オラクル**: 意味論は任意の有限次元 Hilbert 空間 `ℋ`（`[Qudit ℋ]`）上の Hermitian ブロック符号化
`E₀ : QSVT.Encoding.HermitianEncoding ℋ`（フィールド `U`（ユニタリ），`P`（射影 $\Pi$），`encoded := P * U * P`（$= A_0$，自己随伴））に対して与えられます．
qubit レジスタ上で使う場合は `QSVT.Qubit.QubitHermitianEncoding n`（`U : L (Qubits n)`，射影はビットパターン `d` の対角射影 `diagProj d`）から `toHermitian` で得ます．

---

## 3. 構文

プログラムの型は `QSVT.Lang.ExprQ`（すべてのデータは有理数．`#eval` 可能）です．

| 記法 | 項 | 意味（施す変換） |
|---|---|---|
| `U₀` | `ExprQ.oracle` | オラクルそのもの（$A_0$ を実装） |
| `qsvt[Φ] e` | `ExprQ.qsvt Φ e` | 位相列 `Φ : List ℚ` の QSVT を `e` に施す．実装される多項式は $\Re[P_\Phi]$（GSLW Cor. 18）．補助 1 qubit．exact |
| `cheb[c] e` | `ExprQ.cheb c e` | Chebyshev 係数 `c : List ℚ` の多項式 $\sum_k c_k T_k$ を Chebyshev-LCU で `e` に施す．正規化 $\|c\|_1$．exact |
| `poly[l] e` | `ExprQ.poly l e` | 単項式係数 `l : List ℚ`（次数順）の多項式 $\sum_i l_i x^i$ を同様に施す（内部で Chebyshev 係数に変換） |

- ステップは右結合で入れ子にできます: `qsvt[Φ] poly[l] U₀` は `qsvt[Φ] (poly[l] U₀)` で，「まず $p_l(A_0)$ を作り，その上で $\Re P_\Phi$ を施す」，すなわち合成 $\Re P_\Phi \circ p_l$ を実装します．
- 括弧内は 1 つの項です．名前付きリストが使えます: `qsvt[QSVT.Certificate.sign21Phases] U₀`．
- `qsvt` の位相は反射規約（GSLW Cor. 8，$d$ 個の位相で次数 $d$）です．ソルバー出力（回転規約）からの変換は `tools/phases/qsp_conventions.py` が行います．

**ループ**（`QSVT.Lang.Loop`）: 古典的な繰り返しは Lean の関数で書きます．

```lean
iterate k f e            -- f を k 回適用（Nat.rec）
qsvtIter Φ k             -- iterate k (qsvt[Φ]) U₀ : 同じ位相列を k 段ネスト
totalQueries ps          -- プログラムのリストの総クエリ数（掃引ループ用）
expectedQueries p s      -- 成功確率 s の後選択を繰り返すときの期待クエリ数（= queriesQ p / s）
```

量子データ上の条件分岐は存在しません（観測で状態が壊れるため）．分岐は制御ユニタリとしてコンパイル側が扱い，古典的なループと後選択はメタ言語側で扱います．

---

## 4. 意味論

翻訳 `toExpr : ExprQ → QSVT.IR.Expr` を通して，各プログラムに次の 2 つの量が定まります．

| プログラム `e` | `spec (toExpr e)`（$A_0$ に施す多項式） | `scaleQ e`（正規化定数） |
|---|---|---|
| `U₀` | $X$ | $1$ |
| `qsvt[Φ] e'` | $\Re[P_\Phi]\circ\bigl(\tfrac{1}{\text{scale}(e')}\,\mathrm{spec}(e')\bigr)$ | $1$ |
| `cheb[c] e'` | $\bigl(\sum_k c_kT_k\bigr)\circ\bigl(\tfrac{1}{\text{scale}(e')}\,\mathrm{spec}(e')\bigr)$ | $\|c\|_1=\sum_k|c_k|$ |
| `poly[l] e'` | 同上（$\sum_i l_ix^i$ を Chebyshev 展開） | その Chebyshev 係数の $\|c\|_1$ |

**正しさの定理**（`QSVT.Lang.baseQ_eq`）: `wellScaledQ e = true`（すべての `cheb`/`poly` ノードで $\|c\|_1\ne0$．計算可能）のとき

```lean
compress (toExpr e) (denoteQ E₀ e).encoded
  = ((scaleQ e : ℝ) : ℂ)⁻¹ • (Polynomial.aeval E₀.encoded (spec (toExpr e)) * E₀.P)
```

ここで `denoteQ E₀ e` はプログラムの実体（`space ℋ (toExpr e)` 上の Hermitian 符号化．空間は補助レジスタの直和で `ancillaDimQ e · dim ℋ` 次元），`compress` は補助レジスタをすべて $|0\rangle$ に射影して基底空間へ戻す写像です．
つまり「プログラム $e$ は $A_0$ に多項式 $\mathrm{spec}(e)/\mathrm{scale}(e)$ を施した作用素をブロック符号化する」が，書いたプログラムごとに Lean の定理になります．

固有ベクトル単位の言い換え（例: `QSVT/Examples/Sign21RouteB.lean` の `signB_apply_pos`）: $A_0$ の固有ベクトル $\psi$（固有値 $\lambda$）に対し，基底ブロックは $\psi$ を $\tfrac{1}{\text{scale}}\,\mathrm{spec}(\lambda)\,\psi$ に写します．

**実現可能性**: `qsvt` が施せる多項式のクラスは「次数 $d$ の parity を持ち $[-1,1]$ で $|p|\le1$ の実多項式」です．このクラスの多項式には必ず位相列が存在します（GSLW Thm. 3–5, Cor. 10 を形式化した `exists_phases_real`/`exists_phases_R_real`，`QSVT/QSP/Existence.lean`，`Complementary.lean`）．位相列の**値**は数値ソルバーで求め，§5 の証明書で裏付けます．`cheb`/`poly` は任意の係数で exact に動きますが，正規化 $\|c\|_1$ がかかります．

---

## 5. コストと回路

計算可能なコスト関数（`QSVT/Lang/ExprQ.lean`）と一致定理:

| 関数 | 値 | 一致定理 |
|---|---|---|
| `queriesQ` | `U₀`: 1，`qsvt[Φ]`: $|\Phi|\times$，`cheb[c]`/`poly`: $\tfrac{m(m-1)}2\times$（$m$ = Chebyshev 係数の個数） | `queriesQ_eq` |
| `ancillaDimQ` | `qsvt`: $2\times$，`cheb`/`poly`: $\max(m,1)\times$ | `ancillaDimQ_eq`，`finrank_space_toExpr` |
| `degreeBoundQ` | `spec` の次数の上界 | `natDegree_spec_toExpr_le` |
| `scaleQ` | 正規化定数 | `scaleQ_eq` |
| `wellScaledQ` | 正しさ定理の前提 | `wellScaled_toExpr_iff` |

`qsvt[Φ]` は $|\Phi|$ 回のオラクル呼び出し（$U$ と $U^\dagger$ の合計）で次数 $|\Phi|$ を達成します（最適）．`cheb`/`poly` は次数 $m-1$ に対して $O(m^2)$ 回で，証明書が不要な代わりにコストが大きい経路です（§6 Route A）．

ゲート数（単一ステップ `qsvt[Φ] U₀`，GSLW Lemma 19，`QSVT/Circuit/Primitive.lean`）: 全 $4|\Phi|+2$ ゲート，オラクル $|\Phi|$，$C_\Pi\mathrm{NOT}$ $2|\Phi|$，位相 $|\Phi|$，Hadamard 2．
qubit 回路へのコンパイル `compileQ` の意味が `liftAnc`（補助 qubit を 1 本追加する等長同型）を通して一致することが `compileQ_qsvtReal` で証明されています．多段のプログラム（LCU を含む）の qubit 回路化は `liftReg_lcu`/`liftReg_chebLCU`（`QSVT/Qubit/RegBridge.lean`）までで，ゲート列への展開はまだ `qsvt` 単段のみです．

---

## 6. 証明書: Route A と Route B

| | Route A（`cheb`/`poly`） | Route B（`qsvt[Φ]`） |
|---|---|---|
| 入力 | 多項式の係数（有理数） | 位相列（有理数，ソルバー出力） |
| 実装される多項式 | 入力そのもの（exact，正規化 $\|c\|_1$） | $\Re P_\Phi$（exact）．目標多項式との差は証明書で評価 |
| クエリ数 | $O(d^2)$ | $d$ |
| 必要な証明書 | なし（目標関数との近さを言う場合のみ多項式側の証明書） | `checkRe` 証明書 + 多項式側の証明書 |

**位相証明書**（`QSVT/Certificate/PhaseCheck.lean`）: `checkRe Φ t ε n : Bool` は位相列 `Φ`，目標の Chebyshev 係数 `t`，許容誤差 `ε`，Taylor 深さ `n` を受け取り，区間演算で $\|\Re P_\Phi-\sum_k t_kT_k\|_\infty\le\varepsilon$ を検査します．健全性 `checkRe_sound` により，`decide +kernel` で `true` が証明されれば sup ノルムの不等式が定理になります．

**多項式側の証明書**（`QSVT/Certificate/Bound.lean`）: 目標関数（符号関数や $1/(\kappa x)$ など）への近さは，明示的な有理係数多項式に対する LeanCert の Bernstein 証明書（kernel 信頼）で証明します（`leancert (trust := kernel)`．実例: `Sign21.lean`，`InvExample.lean`，`RectExample.lean`，`CosExample.lean`）．

**自前の位相証明書を作る手順**

1. 目標多項式 $p$（実係数，parity，$[-1,1]$ で $|p|\le1$）を用意し，その近さの証明書を `QSVT/Certificate/` の例にならって書く．
2. 位相をソルバーで求め，反射規約に変換して JSON に保存する（`tools/phases/solver_examples.py` 参照．`phases_R_dyadic` と `target_chebyshev_coeffs` を持つ）．
3. プレビュー: `tools/qsvt check --phases foo.json --eps 1e-12 --depth 30`（インタプリタ評価．証明ではない）．
4. 生成: `tools/qsvt emit-cert --phases foo.json --eps 1e-12 --depth 30 --name foo > QSVT/Certificate/Foo.lean`．
   このモジュールは `fooPhases`，`fooTarget`，`theorem foo_checkRe : checkRe … = true := by decide +kernel`，`foo_phase_bound`（sup ノルムの不等式）を含みます．kernel 検査は次数 21 で約 45 秒，次数 35 で約 4–5 分（重いものは `QSVTHeavy/` に置く）．
5. プログラム `qsvt[fooPhases] U₀` を書く．`baseQ_eq` と `foo_phase_bound`，多項式側の証明書を合わせると，固有ベクトル単位の誤差評価が得られます（`QSVT/Examples/Sign21RouteB.lean` が雛形）．

---

## 7. 典型的な使い方

### 7.1 多項式を exact に実装する（Route A）

```lean
open QSVT.Lang

-- 4x³ − 3x（= T₃）を A₀ に施す
#qsvt_info poly[[0, -3, 0, 4]] U₀
```

出力:

```
program      : poly[[0, -3, 0, 4]] U₀
  poly       : monomial [0, -3, 0, 4] = Chebyshev [0, 0, 0, 1], ℓ¹ = 1, register of dimension 4
queries      : 6
ancilla      : dimension 4 (2 qubits)
degree bound : 3
scale (ℓ¹)   : 1 ≈ 1.000000
well scaled  : true
```

正しさ: `baseQ_eq E₀ (by decide : wellScaledQ (poly[[0, -3, 0, 4]] U₀) = true)` が「基底ブロック $=(4A_0^3-3A_0)\Pi_0$」を与えます（`spec` は `simp`/`norm_num` で具体形に落ちます．`test/QSVTTest/Lang.lean` 参照）．

### 7.2 証明済みの位相列で符号関数を施す（Route B）

```lean
open QSVT.Lang QSVT.Certificate

#qsvt_info qsvt[sign21Phases] U₀      -- 21 クエリ，補助 1 qubit，86 ゲート，OpenQASM 付き
```

`sign21Phases` は符号関数の次数 21 近似（$[0.15,1]$ で $0.8924\pm0.0236$）の位相列で，`sign21_checkRe`（kernel 検査済）と `sign21_rePoly_sub_scale_le` が付属します．
固有値 $\lambda\ge0.15$ の固有ベクトルは $0.8924$ 倍に $10^{-12}+0.0236$ 以内で写されます（`signB_apply_pos`，`QSVT/Examples/Sign21RouteB.lean`）．これは GSLW Thm. 26（特異ベクトル変換）の具体例です．

### 7.3 回路を出す

```lean
#qsvt_info (n := 2) (cP := [(1, true)]) qsvt[[1 / 4]] U₀
```

`(n := k)` はシステム qubit 数（補助ビットは `q[0]`，システムは `q[1..k]`），`(cP := [(i, b), …])` は射影 $\Pi$ の制御パターン（$i<n$ は 0 始まりの qubit 番号，`b` は制御値．省略時は全ビット 0 制御 $\Pi=|0\cdots0\rangle\langle0\cdots0|$）．
出力の OpenQASM では，オラクルは空の `gate U_oracle` として宣言され（本体はユーザーが与える），$C_\Pi\mathrm{NOT}$ は `ctrl`/`negctrl @ x`，位相は `rz`（規約差 $\theta=-2\varphi$ を注記）で表されます．
Lean を介さずに使うには CLI: `tools/qsvt qasm "qsvt[0.25] U0" --qubits 2 --pattern 1=1`．

### 7.4 ネストと反復

```lean
#qsvt_info qsvt[[1 / 2, -1 / 3]] poly[[0, -3, 0, 4]] U₀   -- 合成 Re P_Φ ∘ T₃，queries 2·6 = 12
#qsvt_info qsvtIter [1 / 2, -1 / 3] 2                      -- 同じ段を 2 回，queries 2² = 4
```

反復の定理（`QSVT/Lang/Loop.lean`）: `queriesQ (qsvtIter Φ k) = Φ.length ^ k`，`ancillaDimQ = 2 ^ k`，`spec = compIter (Re P_Φ) k`（$k$ 回の多項式合成），`base_qsvtIter`．

### 7.5 古典ループで QSVT を何度も呼ぶ（閾値の掃引）

`QSVT/Examples/Loop.lean` の `windowProg t := qsvt[sign21Phases] cheb[[-t, 1]] U₀` は「スペクトルを $t$ だけずらしてから符号関数を施す」窓プログラムの族で，`queriesQ (windowProg t) = 21` が $t$ によらず成り立ちます．
二分探索の骨格 `bisect steps lo hi decide` と訪問点 `visited` に対し，`length_visited = steps`，`groundEnergyQueries_le`（総クエリ $\le$ `steps` × 1 段のクエリ）が証明されています．`decide t` の実体は `windowProg t` を走らせて補助ビットを観測する古典的な判定で，量子部分は各段ごとに `baseQ_eq` を持ちます．

### 7.6 応用アルゴリズムの例（ライブラリ側）

| 例 | 内容 | 主定理 |
|---|---|---|
| `QSVT/Examples/FixedPointAA.lean` | 固定点振幅増幅（GSLW Thm. 27）．初期重なり $\ge0.15$ から成功振幅 $\ge0.869$，21 クエリ | `fixedPointAA_amplitude` |
| `QSVT/Examples/Threshold.lean` | 固有値の窓フィルタ（Thm. 31），次数 32，528 クエリ | `rectCircuit_apply_inner/outer` |
| `QSVT/Examples/Inverse.lean`，`QSVTHeavy/InverseAA.lean` | 線形方程式: $c/(\kappa x)$ の近似（$\kappa=4$）+ 振幅増幅．成功振幅 $\ge0.975$，誤差 $\le0.02$ | `inverseAA_amplitude`, `inverseAA_output` |
| `QSVT/Examples/Evolution.lean`，`EvolutionAA.lean` | $e^{-2iA}b$ の準備（Thm. 58 相当）．複素係数の Route A，成功振幅 $\ge0.869$ | `evolutionAA_amplitude`, `evolutionAA_output` |

いずれも「証明書（多項式の近さ）+ 定理（回路の意味）」の組で，数値は証明書の plateau 定数（$0.8924$ や $79/80$）に依存します．

---

## 8. 制限と注意

- `ExprQ` の係数・位相は実数（有理数）です．複素係数の Chebyshev-LCU は IR の下の層（`QSVT.Pipeline.chebLCU`）では使えます（`Examples/Evolution.lean`）．
- 2 つのプログラムの**積**（$A\cdot B$ の符号化，GSLW Lemma 53）は `QSVT/Encoding/Product.lean` にありますが，`ExprQ` の構成子にはまだ入っていません．
- 近似次数の漸近保証（$O(\log(1/\varepsilon)/\delta)$ など）は形式化していません．各例は具体的な $(\varepsilon,\delta,\kappa)$ の証明書です．
- `qsvt[Φ]` は exact ですが，目標関数に対する $\Re P_\Phi$ の近さは証明書に依存します．証明書なしでプログラムを書いた場合，得られるのは「ある多項式 $\Re P_\Phi$ を施した」という事実だけです．
- `#qsvt_info`・CLI・OpenQASM は検証対象外の便宜機能です．信頼される主張は Lean の定理のみです．

---

## 9. 参照（主要なファイルと定理）

| 層 | ファイル | 主な名前 |
|---|---|---|
| 構文・意味・コスト | `QSVT/Lang/ExprQ.lean` | `ExprQ`, `toExpr`, `queriesQ`, `ancillaDimQ`, `degreeBoundQ`, `scaleQ`, `wellScaledQ`, `denoteQ`, `baseQ_eq` |
| 記法 | `QSVT/Lang/Notation.lean` | `U₀`, `qsvt[..]`, `cheb[..]`, `poly[..]` |
| 報告コマンド | `QSVT/Lang/Info.lean` | `#qsvt_info`, `info`, `qasmOf` |
| ループ | `QSVT/Lang/Loop.lean` | `iterate`, `qsvtIter`, `totalQueries`, `expectedQueries` |
| IR | `QSVT/IR/{Expr,Denote,Sound,Cost}.lean` | `spec`, `scale`, `denote`, `compress`, `compress_aeval_mul_P`, `queries` |
| 定理の核 | `QSVT/SVT/{QET,QSVT,RealPoly}.lean` | `qet`, `qsvt_odd`, `qsvt_even`, `qet_real` |
| 回路 | `QSVT/Circuit/`, `QSVT/Qubit/` | `compileQsvtReal`, `compileQ_qsvtReal`, `toQasm`, `liftReg_lcu` |
| 証明書 | `QSVT/Certificate/` | `checkRe`, `checkRe_sound`, LeanCert 証明書の例 |
| CLI | `tools/qsvt`, `tools/README.md` | `info`, `qasm`, `check`, `emit-cert` |
