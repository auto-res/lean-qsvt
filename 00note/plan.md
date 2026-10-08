# lean-qsvt 開発計画

- 作成日: 2026-10-08
- 対象: [prompt.md](prompt.md) に書かれた目標（高級量子言語の開発，当座は QSVT の Lean 実装）
- 付録: [formal-spec.md](formal-spec.md)（Lean で形式化する定義・定理の精密な一覧と依存関係）

---

## 0. 要約

- **当座ゴール（QSVT）を 4 つの完了条件 G1–G4 に分解**し，7 つのフェーズ（Phase 0–7）で達成する．
- **最初のデモ（複素多項式 f ↦ 回路 + Lean 証明）は Phase 3 終了時点（目安 4–5 か月）**．ただし位相角は数値計算（untrusted）で求め，Lean は「構造定理（exact）」と「近似誤差の証明書検査」の二段構えで正しさを保証する．
- 設計上の最重要判断は 3 つ:
  1. **SVD を使わない定式化**．Mathlib に SVD は無い（PR #6042 は 2026-04 に close）．特異値変換 $P^{(SV)}(A)$ を $A^\dagger A$ の多項式で定義し，証明は「固有ベクトル単位の帰納法」で行う．
  2. **Hermitian ブロック符号化（QET）を先に**，一般 QSVT を後に．前者は Mathlib のスペクトル定理だけで閉じる．
  3. **位相角の計算は信頼境界の外**．Lean は証明書（Chebyshev 係数の区間評価）を検査する．数値計算を一切使わない代替経路（Chebyshev 多項式の LCU）も用意し，デモを数値検証ライブラリの成熟に依存させない．
- 既存資産: [lean-quantum](../../lean-quantum)（基底非依存の作用素論，CFC，channel，POVM；arXiv:2607.05492），Mathlib，inQWIRE/LeanQuantum（ゲート層），LeanCert / girving/interval（検証付き数値）．

---

## 1. ゴールと完了条件

### 1.1 長期ゴール（prompt.md の「目標」）

| 要素 | 内容 | 本計画での扱い |
|---|---|---|
| 高級言語 | 回路を意識せずアルゴリズムを書く | Phase 7（Lean 埋め込み DSL として開始） |
| コンパイラ | 機種ごとの回路を自動生成 | Phase 5 で IR→ゲート列，機種依存は将来課題 |
| Lean 証明 | 生成回路がアルゴリズムの実装であることの証明 | Phase 1–5 の中心 |
| 計算量保証 | クエリ数・ゲート数・補助量子ビット数の定理 | Phase 4–5（構造的計算量），Phase 6（近似次数の漸近評価） |

### 1.2 当座ゴール（QSVT）の完了条件

- **G1（定理）**: QSP 構造定理（GSLW Thm 3 / Cor 8）と QSVT 定理（GSLW Thm 17）が Lean で sorry-free．
- **G2（パイプライン）**: 入力 $f\in\mathbb{C}[x]$ に対し `(位相列 Φ, 回路, 証明)` を自動生成する．証明は二本立て:
  - exact: `回路の意味 = P_Φ^{(SV)}(A)`（Φ を記号として扱う構造定理のインスタンス）
  - 近似: $\|P_\Phi - f\|_{[-1,1]} \le \varepsilon$（証明書検査，または Chebyshev-LCU 経路なら exact）
- **G3（計算量）**: 生成物に「$U,U^\dagger$ の使用回数 $=\deg f$，補助量子ビット 1（実多項式なら 2）」等の定理が自動で付く（GSLW Lemma 19）．
- **G4（例）**: GSLW の 固定点振幅増幅（Thm 27），閾値射影（Thm 31），擬似逆（Thm 41），Hamiltonian simulation（Thm 58）を DSL で各 10–30 行で記述し，正しさ定理が通る．加えて QSVT を多数回・ループで使う例を 1 つ（§4 Phase 6 参照）．

---

## 2. アーキテクチャ

### 2.1 レイヤー

```
 L4  言語層     : 埋め込み DSL（コンビネータ + マクロ），OpenQASM 出力
 L3  回路層     : ゲート列 IR `Circuit`，意味関数 `denote`，コスト関数，コンパイラ + 正当性
 L2  符号化層   : `BlockEncoding α a ε A`，LCU・積・制御化，資源カウント
 L1  QSVT 層    : 位相列 Φ ↦ 交代列 U_Φ，QET/QSVT 定理，ロバスト性
 L0  数学層     : Polynomial ℂ（parity, Chebyshev, sup ノルム），作用素論（lean-quantum），QSP (2×2)
 ----------------------------------------------------------------------
 ツール（untrusted）: 位相角ソルバー（QSPPACK / 自作 FFT 法），Chebyshev 展開器
 証明書検査（trusted, Lean）: 区間演算で ‖P_Φ − f‖ ≤ ε を検査
```

### 2.2 信頼境界

- **trusted**: Lean の定義・定理，`denote`，証明書検査器（`check_sound` 定理付き）．
- **untrusted**: 位相角ソルバー，近似多項式の構成器，OpenQASM エミッタ（意味は `denote` が決める；エミッタの検証は将来課題）．
- 位相列は **有理数（二進小数）** で受け取り，Lean 内では `Real.cos`/`Real.sin` を記号的に扱う．浮動小数は Lean の定理に現れない．

### 2.3 データの流れ（G2）

```
 f ∈ ℂ[x]
  │ (1) 前処理 [Lean, 計算可能]: 偶奇分解，スケーリング α_f，許容性チェック
  ▼
 (f_even/α, f_odd/α)
  │ (2a) Route B: ソルバー [untrusted] → Φ̃ ∈ ℚ^d,  Lean: check(Φ̃, f, ε) = true
  │ (2b) Route A: Chebyshev 展開 f = Σ c_k T_k [exact] → 各 T_k は閉形式の位相 (Lemma 9)
  ▼
 IR 項:  lcu [...] (qsvt Φ̃ enc) ...
  │ (3) 定理の自動インスタンス化: denote = P^{(SV)}(A), 誤差 ≤ ε, cost = ...
  │ (4) compile → Circuit → OpenQASM
  ▼
 (回路, 証明, 計算量定理)
```

---

## 3. 主要な設計判断

| ID | 判断 | 理由 / 代替案 |
|---|---|---|
| D1 | **コア定理は基底非依存（`L ℋ`，`Qudit ℋ`）**，回路層は qubit 添字付き行列 `Matrix (Fin n → Bool) (Fin n → Bool) ℂ`．両者を `toOperator` で橋渡し | lean-quantum と整合し，CFC・スペクトル定理をそのまま使える．回路層は Kronecker 積と制御ゲートが具体的に書ける方が楽．**Phase 0 の結論**: lean-quantum 公開版を v4.34.1 に上げると `QuantumChannel` が 31 エラーでビルド不能（[survey.md](survey.md) §B）→ `QuantumState.lean` の約 70 行（`Qudit`, `L`, `†`, `Tr`, `IsProjective` 等）を Apache-2.0 表示付きで `QSVT/Operator/Basic.lean` に複製し，名前は同一に保つ |
| D2 | **QSP の規約は GSLW の反射規約 $R(x)$（Cor 8，位相 $d$ 個）**を主，回転規約 $W(x)$（Thm 3，位相 $d+1$ 個）は変換補題で接続 | QSVT 定理（Def 15, Thm 17）が $R$ 規約で書かれている．QSPPACK 等は $W$ 規約なので変換補題が必要 |
| D3 | **$P^{(SV)}(A)$ は SVD を使わず定義**: $P$ 偶 $=R(x^2)$ なら $\Pi\,R(A^\dagger A)\,\Pi$，$P$ 奇 $=xR(x^2)$ なら $A\,R(A^\dagger A)$ | Mathlib に SVD が無い．代数的定義なら `Polynomial.aeval` で書け，計算可能性・拡張性が高い．SVD との一致は補題として証明 |
| D4 | **Hermitian 符号化（$\tilde\Pi=\Pi$, $A=A^\dagger$）の QET を先行**，一般 QSVT は後続 | スペクトル定理（Mathlib）だけで閉じ，Hamiltonian simulation・逆行列・基底状態など主要応用を先にカバー |
| D5 | **位相角は untrusted，Lean は証明書を検査**．並行して **数値を使わない Route A（Chebyshev-LCU）** を持つ | 証明付き数値計算（LeanCert / girving/interval）の成熟度・バージョン整合に依存しない退路を確保．Route A はクエリ数が $O(d^2)$ で劣るが完全に exact |
| D6 | **誤差 ε と正規化 α は型に載せる**: `BlockEncoding (α ε : ℝ) (a : ℕ) (A : L ℋ)` | GSLW Def 43 そのもの．合成則（LCU，積，QSVT）が誤差伝播の定理になる |
| D7 | **コア IR は純ユニタリ**．量子データ上の分岐は制御ユニタリ（$C_\Pi\mathrm{NOT}$，多重制御位相）に，古典ループはメタ言語（Lean）の再帰に，観測は最上位の `run`／channel に限定 | 「観測で状態が壊れる」問題への構造的回答．補助量子ビットが $\ket{0}$ に戻ることは ブロック符号化述語そのものが保証する |
| D8 | **補助量子ビットは直和で表す**: `Anc ℋ := WithLp 2 (ℋ × ℋ)`，作用素は `L ℋ` 成分の 2×2 ブロック．$m$ 項 LCU は `PiLp 2 (fun _ : Fin m => ℋ)` に拡張 | テンソル積 `ℂ² ⊗ ℋ` の基底非依存な取り回し（lean-quantum の `basisPiTensor*`）を持ち込まずに Cor 18・Lemma 19 が書ける．qubit テンソル積との対応は回路層（Phase 5）で付ける |

---

## 4. フェーズ計画

各フェーズは「目的 / 成果物 / 主要タスク / 完了条件 / リスク / 目安」で記述．定理 ID（例 `QSP-3`）は [formal-spec.md](formal-spec.md) を参照．

### Phase 0: 環境整備とサーベイ（目安 1–2 週）

- 目的: ビルドが通る骨組みと，依存ライブラリの採否決定．
- 成果物:
  - `lakefile.toml`（Mathlib 最新安定版），`QSVT.lean` ルート，CI（`lake build` + `#print axioms` チェック），blueprint 雛形（lean-quantum と同じ LeanArchitect 方式）．
  - `00note/survey.md`: lean-quantum（依存可否・必要モジュール），inQWIRE/LeanQuantum（Kronecker・制御ゲートの流用可否），LeanCert / girving/interval（Lean 版，`cos`/`sin` の区間評価，kernel 検証可否），Mathlib の `Polynomial.Chebyshev`・`Matrix.unitaryGroup`・`LinearMap.IsSymmetric.eigenvectorBasis`・`cfc` の API 確認．
- 主要タスク:
  - [x] lean-quantum の公開版（v4.29.0-rc6）を最新 Mathlib に上げて `require` できるか試す．→ 不可（survey.md §B）．`QSVT/Operator/Basic.lean` に最小複製する（Phase 2a 着手時）．
  - [x] GSLW の定理番号を [formal-spec.md](formal-spec.md) に固定，他の規約（pyqsp, qsppack の $W$ 規約）との変換表を作成（[qsp-convention-check.md](qsp-convention-check.md)；GSLW 式 (16) の符号誤りも発見）．
  - [x] ソルバー候補の動作確認（pyqsp 0.2.0, qsppack 0.4.0 を導入．$T_5$ と次数 21 の符号関数近似で検証）．JSON 出力ラッパ `tools/phases/solver_examples.py`．
- 完了条件: 空の定理ファイルを含むプロジェクトが CI で通る．D1・D5 の採否が決まる．
- リスク: ツールチェーン不整合（lean-quantum, LeanCert がそれぞれ別の Lean 版）．→ 最小複製で逃げる．

### Phase 1: QSP（1 qubit）理論（目安 4–6 週）

- 目的: 位相列 Φ ↦ 多項式 $(P_\Phi, Q_\Phi)$ を記号的に定義し，構造定理を証明．
- 成果物: `QSVT/QSP/*.lean`
- 主要タスク:
  - [ ] `POLY-*`: parity，偶奇分解 `evenPart/oddPart`，偶多項式 $=R(x^2)$ の表現，$[-1,1]$ 上 sup ノルム，Chebyshev $T_n$ の性質（Mathlib 流用）．
  - [ ] `QSP-1`: $R(x)$, $e^{i\phi\sigma_z}$，列 `seqR Φ x` の再帰定義．$W(x)$ 規約も定義し変換補題 `QSP-2`（$W = i e^{-i\pi/4\sigma_z} R e^{-i\pi/4\sigma_z}$．GSLW 式 (16) の印刷は右側の符号が誤り．数値検証済）．
  - [ ] `QSP-3`: $(P_\Phi, Q_\Phi)$ を **多項式の再帰**で定義（formal-spec.md の検証済再帰．$Q$ は左下成分）し，評価定理「$x\in[-1,1]$ で `seqR Φ x` の成分 $= P_\Phi(x),\ iQ_\Phi(x)\sqrt{1-x^2},\dots$」を帰納法で証明．次数・parity・$|P|^2+(1-x^2)|Q|^2=1$ を系として導出．
  - [ ] `QSP-4`: Chebyshev の閉形式位相（Lemma 9）: $\phi_1=(1-d)\pi/2,\ \phi_{i\ge2}=\pi/2$ で $P_\Phi=T_d$．最初の「exact な実例」．
  - [ ] `QSP-5`: 端点公式 $P_\Phi(\pm1)=(\pm1)^d\prod e^{i\phi_j}$，偶数 $d$ の $P_\Phi(0)$（Cor 8 の moreover）．QSVT 定理の端点ケースで必要．
  - [ ] `QSP-6`: 摂動補題 $\|P_\Phi - P_{\Phi'}\|_\infty \le 2\sum_j|\phi_j-\phi'_j|$（ユニタリ積の telescoping）．
  - [ ] `QSP-7`（存在定理，後回し可）: Thm 4（相補多項式 $Q$ の存在，Lemma 6 の根の分解），Thm 5 / Cor 10（実多項式）．言語の「意味論」として必要だが G2 のパイプラインには不要．
- 完了条件: `QSP-3`, `QSP-4`, `QSP-5` が sorry-free．
- リスク: $\sqrt{1-x^2}$ の扱い．→ 評価定理は $x=\cos\theta$ で述べる版も用意．`QSP-7` の根の多重度の扱いは Mathlib の `Polynomial.roots` で可能だが重い（★★★）．

### Phase 2a: Hermitian ブロック符号化と QET（目安 5–7 週）

- 目的: $\tilde\Pi=\Pi$，$A=\Pi U\Pi$ が Hermitian のとき $\Pi\,U_\Phi\,\Pi = P_\Phi(A)\,\Pi$ を証明（Low–Chuang の qubitization，GSLW Thm 56 相当）．
- 成果物: `QSVT/Encoding/Projected.lean`, `QSVT/SVT/AltSeq.lean`, `QSVT/SVT/QET.lean`
- 主要タスク:
  - [ ] `ENC-1`: `ProjUnitaryEncoding ℋ`（$U$ ユニタリ，$\Pi,\tilde\Pi$ 直交射影）と `encoded := Π̃ U Π`．
  - [ ] `SVT-1`: 交代列 `altSeq Φ`（Def 15）の再帰定義（先頭から剥がす形．偶奇で $U$/$U^\dagger$ と $\tilde\Pi$/$\Pi$ を切替）．
  - [ ] `SVT-2`: 位相作用素 $e^{i\phi(2\Pi-I)} = e^{i\phi}\Pi + e^{-i\phi}(I-\Pi)$ の性質（ユニタリ，$\Pi$ と可換）．
  - [ ] `SVT-3`（**QET**）: 証明は「固有ベクトル単位の帰納法」:
    1. $A$ のスペクトル定理（`LinearMap.IsSymmetric.eigenvectorBasis` を $\operatorname{ran}\Pi$ 上で）で ONB $\{\psi_i\}$，固有値 $\varsigma_i\in[-1,1]$．
    2. $|\varsigma_i|<1$ なら $\psi_i^\perp := (I-\Pi)U\psi_i/\sqrt{1-\varsigma_i^2}$ を定義し，4 つの関係式 $U\psi=\varsigma\psi+s\psi^\perp$，$U\psi^\perp=s\psi-\varsigma\psi^\perp$，$U^\dagger$ 版，$(2\Pi-I)$ 版 を証明．
    3. 帰納法: `altSeq Φ ψ = a ψ + b ψ^⊥`，$(a,b)^T = \texttt{seqR Φ ς}\cdot e_1$．
    4. $\Pi$ を掛けて `QSP-3` から $P_\Phi(\varsigma)\psi$．端点 $|\varsigma|=1$ は `QSP-5`．
    5. ONB 上で一致 ⇒ 作用素として一致．
  - [ ] `SVT-4`: ノルム補題 $\|g(A)\Pi\|\le\sup_{[-1,1]}|g|$（CFC または固有分解）．
- 完了条件: `SVT-3` が sorry-free．Chebyshev 位相（`QSP-4`）と組み合わせ「$T_d(A)$ のブロック符号化」の具体例が通る．
- リスク: 部分空間 $\operatorname{ran}\Pi$ 上での固有基底の取り回し（`Submodule` の内積空間構造，`LinearMap.restrict`）．→ Phase 0 で API を確認．

### Phase 2b: 一般 QSVT（目安 5–7 週，Phase 3 と並行可）

- 目的: GSLW Thm 17 を SVD 無しの定式化で証明．
- 主要タスク:
  - [ ] `SVT-5`: `svTransform P A`（D3）の定義と，SVD 形との一致補題（ベクトル形: $P^{(SV)}(A)\psi_i = P(\varsigma_i)\tilde\psi_i$）．
  - [ ] `SVT-6`: $A^\dagger A$ の固有基底から $\tilde\psi_i := A\psi_i/\varsigma_i$ を作る「射影ユニタリの SVD」（Def 11 相当，必要最小限）．
  - [ ] `SVT-7`（**QSVT, Thm 17**）: `SVT-3` と同じ帰納法を 2 組の 2 次元空間 $\{\psi_i,\psi_i^\perp\}$，$\{\tilde\psi_i,\tilde\psi_i^\perp\}$ で交互に行う．端点 $\varsigma\in\{0,1\}$ を個別処理（$\varsigma=0$: $P$ 奇なら $P(0)=0$，偶なら `QSP-5`）．
  - [ ] `SVT-8`: 実多項式版（Cor 18）: $U_\Phi$ と $U_{-\Phi}$ の LCU（補助 1 qubit）で $\Re P$．`ENC-3`（LCU）に依存．
  - [ ] `SVT-9`（任意）: ロバスト性 Lemma 22/23．近似ブロック符号化の誤差伝播に使う．
- 完了条件: `SVT-7` sorry-free．副産物として一般の行列 SVD を Mathlib に PR できる形にまとめられれば望ましい（必須ではない）．

### Phase 3: 位相角パイプラインと証明書（目安 6–8 週，Phase 1 完了後に並行開始）

- 目的: 任意の（許容な）$f$ に対し位相列と誤差保証を得る．
- 成果物: `tools/phases/`（Python），`QSVT/Certificate/*.lean`，`QSVT/Frontend/Normalize.lean`
- 主要タスク:
  - [ ] `FE-1` 前処理（Lean, 計算可能）: $f\mapsto$ 偶奇分解，$\alpha_f$ によるスケーリング（$\|f/\alpha_f\|_{[-1,1]}\le 1$ の十分条件は係数の $\ell^1$ ノルムで保守的に），実部・虚部の分離（Cor 18 経由なら実多項式 2 本）．出力は「許容多項式の列と LCU 係数」．
  - [ ] **Route A（exact）** `CERT-A`: $f=\sum_k c_k T_k$ の Chebyshev 展開（有理係数なら exact）．各 $T_k$ は `QSP-4` の閉形式位相で実装し，`ENC-3`（LCU）で合成．数値計算ゼロ，誤差ゼロ．クエリ数 $\sum_k k = O(d^2)$，補助 qubit $O(\log d)$．**G2 の最初の達成経路**．
  - [ ] **Route B（最適コスト）** `CERT-B`:
    - ソルバー: QSPPACK（最適化法）または Berntson–Sünderhauf の FFT 相補多項式法 + 位相抽出．出力は二進小数の $\tilde\Phi$．規約変換（$W\to R$）はラッパ側で行い Lean 側 `QSP-2` と整合させる．
    - 検査器 `check (Φ̃ : Fin d → ℚ) (f : Polynomial ℂ) (ε : ℚ) : Bool`: $P_{\tilde\Phi}$ の Chebyshev 係数を区間演算で囲い込み，$\|P_{\tilde\Phi}-f\|_\infty\le\sum_k|c_k(P_{\tilde\Phi})-c_k(f)|$ で評価．必要な補題: $|T_k|\le1$，$xT_k=(T_{k+1}+T_{k-1})/2$，再帰 `QSP-3` の Chebyshev 基底版．
    - 健全性 `check_sound`: `check … = true → ∀ x ∈ [-1,1], ‖P_Φ̃(x) − f(x)‖ ≤ ε`．
    - 区間演算は LeanCert（Lean v4.30–4.34 対応，`sin`/`cos` あり，kernel 検証モードあり）を第一候補，girving/interval を第二候補．
  - [ ] `CERT-C`: 誤差の作用素への持ち上げ $\|P_{\tilde\Phi}^{(SV)}(A)-f^{(SV)}(A)\|\le\|P_{\tilde\Phi}-f\|_\infty$（`SVT-4`）．
  - [ ] オプション: ソルバーを Lean の `Float` で書き直し `lake exe qsvt` 一本にする（untrusted のまま．言語統一の観点）．
- 完了条件: Route A で G2 達成（Hermitian ケース）．Route B で次数 $d\le 200$ 程度の実多項式（例: 符号関数近似）の証明書が kernel で検査できる．
- リスク: 証明書検査の kernel 実行時間（$d\sim10^3$ で係数 $10^3$ 個 × 区間演算）．→ `native_decide` 併用の是非を Phase 3 で判断し，trusted base を明記．

### Phase 4: 符号化の代数と抽象 IR，計算量（目安 6–8 週）

- 目的: ブロック符号化のコンビネータと資源カウントを定理付きで揃える．
- 成果物: `QSVT/Encoding/{Block,LCU,Product,Control}.lean`，`QSVT/IR/*.lean`
- 主要タスク:
  - [ ] `ENC-2`: `BlockEncoding α a ε A`（Def 43）．`ProjUnitaryEncoding` の特殊化（$\Pi=\ket0\!\bra0^{\otimes a}\otimes I$）．
  - [ ] `ENC-3`: LCU（GSLW Lemma 52）: 状態準備ユニタリ + select で $\sum_j y_j A_j$．誤差・正規化の合成則．
  - [ ] `ENC-4`: 積（Lemma 53）: $(\alpha\beta, a+b, \alpha\delta+\beta\varepsilon)$．
  - [ ] `ENC-5`: 制御化（Lemma 19 後半）: `controlled (altSeq Φ)` は位相ゲートの制御化だけで作れる．
  - [ ] `ENC-6`: 自明符号化（Def 44），ユニタリの符号化，対角・疎行列・密度作用素（Lemma 45）は例として．
  - [ ] `IR-1`: 抽象 IR `Expr`（`oracle`, `qsvt Φ`, `lcu`, `prod`, `control`, `adjoint`）と `denote : Expr → L ℋ`，`cost : Expr → Resources`（queries, ancilla, phaseGates, cpiNot）．
  - [ ] `IR-2`: 計算量定理の自動化: `cost (qsvt Φ e) = ⟨d, 1, d, d⟩ + …` を `simp` で閉じる形にする（G3）．
- 完了条件: `qsvt`・`lcu`・`prod` の合成で「$\Re P(A)$ の $(1,2,\varepsilon)$-符号化」が定理として得られ，コストが `simp` で数値に落ちる．

### Phase 5: 具体回路コンパイラ（目安 6–10 週）

- 目的: IR をゲート列に落とし，意味保存を証明．OpenQASM に出力．
- 成果物: `QSVT/Circuit/{Gate,Denote,Cost,Compile,Correct}.lean`，`tools/export/`
- 主要タスク:
  - [ ] `CIRC-1`: ゲート集合 {H, X, Z, Rz(φ), CNOT, 多重制御 X, `oracle U`, `oracle U†`, `cΠNOT`}．添字は `Fin n → Bool`．Kronecker 積と reindex（inQWIRE/LeanQuantum の `solve_matrix` 等を流用検討）．
  - [ ] `CIRC-2`: `denote : Circuit n → Matrix …`，ユニタリ性の保存定理．
  - [ ] `CIRC-3`: Lemma 19 の実装: $e^{i\phi(2\Pi-I)} = C_\Pi\mathrm{NOT}\,(I\otimes e^{-i\phi\sigma_z})\,C_\Pi\mathrm{NOT}$（Fig. 1b）と，その制御版（Fig. 1c）．
  - [ ] `CIRC-4`: `compile : Expr → Circuit`，`compile_correct : toOperator (denote (compile e)) = Expr.denote e`，`compile_cost`（ゲート数 = IR コストの線形関数）．
  - [ ] `CIRC-5`: $\Pi=\ket0\!\bra0^{\otimes a}\otimes I$ のとき $C_\Pi\mathrm{NOT}$ は多重制御 X（Toffoli 列）．ゲート数 $O(a)$ の定理．
  - [ ] `CIRC-6`: OpenQASM 3 エミッタ（oracle は opaque gate）．簡単な回路で Qiskit の状態ベクトルと `denote` を数値照合するテスト（untrusted，回帰テスト用）．
- 完了条件: Phase 3 の生成物が `.qasm` として出力され，`compile_correct` がインスタンス化される．
- リスク: 具体行列計算の `simp`/`decide` の重さ．→ 定理は「構造的」に（ゲートの意味を代数的に）証明し，数値展開は避ける．

### Phase 6: 応用例とループ（目安 8–12 週）

- 目的: G4．QSVT を「使う側」の記述が短く，証明が合成で得られることを示す．
- 主要タスク（GSLW の定理番号）:
  - [ ] `APP-1` 固定点振幅増幅（Thm 26/27）: 符号関数近似多項式（Lemma 25）を Route B で用意．正しさは `SVT-7` + `CERT-C` の合成．
  - [ ] `APP-2` 特異値閾値射影・判別（Thm 31/32）: 矩形関数近似（Lemma 29）．
  - [ ] `APP-3` 擬似逆・線形方程式（Lemma 40, Thm 41）: $1/x$ 近似．Lemma 40 は構成が明示的（二項和 + Chebyshev）なので **近似次数の定理を Lean で証明する最初の候補**．
  - [ ] `APP-4` Hamiltonian simulation（Thm 58）: Jacobi–Anger 展開．$\cos(tx),\sin(tx)$ の Chebyshev 展開係数は Bessel 関数なので証明書経路で．
  - [ ] `APP-5` **ループ例**: (a) Lin–Tong 型の基底エネルギー推定: 閾値 $t$ の二分探索の各ステップで `APP-2` の QSVT を呼ぶ（古典ループ × 量子サブルーチン）．(b) 「QSVT の出力を再びブロック符号化して QSVT」（多項式の合成 $P\circ Q$ による次数の積，Lemma 53 と `SVT-7` の反復）．いずれも Lean の再帰で記述し，証明はパラメトリック．
  - [ ] `APP-6` 後選択・観測の扱い: 成功確率の定理（`POVM` を lean-quantum から流用），固定点振幅増幅で後選択を除去する定型パターンを補題化．
- 完了条件: 4 例 + ループ例が `Examples/` にあり，各ファイル 100 行以内（うち DSL 記述 10–30 行），sorry-free．

### Phase 7: 言語化（継続）

- 埋め込み DSL の表面構文（`do` 記法風マクロ），型による $(\alpha, a, \varepsilon)$ とコストの追跡，エラーメッセージ（許容条件違反の報告），`#eval` で回路図/コスト表示．
- 機種依存コンパイル: `GateSet`/`Backend` 抽象，意味保存書換え（VOQC 流）．接続制約・ルーティングは対象外から始める．
- 拡張: GQSP（Motlagh–Wiebe 2024，parity 制約なし），多変数 QSVT，近似理論の漸近定理（Lemma 25, 29 の $O(\log(1/\varepsilon)/\delta)$ 等）．

---

## 5. スケジュール目安

**達成状況（2026-10-09 時点）**: M1–M5 を達成，M6 は 4 例中 4 例（固定点振幅増幅・閾値射影・擬似逆・Hamiltonian simulation の多項式ステップ）とループ例が揃い，残りは振幅増幅との結合と近似次数の漸近定理．
計画時の目安（約 1 年）に対し，subagent 並列開発により 2 日で到達した．詳細は [PROGRESS.md](../PROGRESS.md) と [formal-spec.md](formal-spec.md) の進捗表．

| マイルストーン | 状態 | 実体 |
|---|---|---|
| M1 Chebyshev の exact 位相 | 済 | `QSP/Chebyshev.lean` |
| M2 QET 定理 | 済 | `SVT/QET.lean`；一般 QSVT（Thm 17）も `SVT/QSVT.lean` で済 |
| M3 $f\mapsto$ 回路 + 証明（Hermitian, exact） | 済 | Route A `Pipeline/ChebLCU.lean`，`routeA` |
| M4 QSVT 定理 + 証明書検査 | 済 | `Certificate/PhaseCheck.lean`（`checkRe_sound`），Route B `Examples/Sign21RouteB.lean`（21 クエリ） |
| M5 OpenQASM 出力 + compile_correct | 済 | `Circuit/`，`Qubit/Compile.lean`（`compileQ_qsvtReal`），`Qubit/Qasm.lean`，`Qubit/RegBridge.lean` |
| M6 GSLW 4 例 + ループ例 | ほぼ済 | `Examples/{FixedPointAA,Threshold,Inverse,Evolution,Loop}.lean`；振幅増幅との結合（Thm 41/58 の残り）と Lemma 25/29/40 の漸近次数定理は未 |


前提: 1–2 名 + AI 支援，週 20–30 時間．並行可能なものは並行．数字は目安であり，Phase 1–2a の実績で再見積もりする．

| 期間（週） | 主担当フェーズ | 並行 | マイルストーン |
|---|---|---|---|
| 1–2 | Phase 0 | — | CI 通過，依存決定 |
| 3–8 | Phase 1 | ソルバー動作確認 | `QSP-3/4/5` 完了（**M1: Chebyshev の exact 位相**） |
| 9–15 | Phase 2a | Phase 3 Route A | `SVT-3` 完了（**M2: QET 定理**） |
| 16–20 | Phase 3 Route A 仕上げ | Phase 2b 開始 | **M3: f ↦ 回路+証明（Hermitian, exact）** ＝ 最初のデモ |
| 21–28 | Phase 2b, Phase 3 Route B | Phase 4 開始 | **M4: QSVT 定理**，証明書検査が動く |
| 29–36 | Phase 4 | Phase 5 開始 | コンビネータ + コスト定理 |
| 37–46 | Phase 5 | Phase 6 開始 | **M5: OpenQASM 出力 + compile_correct** |
| 47–58 | Phase 6 | Phase 7 | **M6: GSLW 4 例 + ループ例** |

---

## 6. リスクと対応

| リスク | 影響 | 対応 |
|---|---|---|
| Mathlib に SVD が無い | QSVT 定理の証明が重い | D3（SVD 無し定式化）+ D4（Hermitian 先行）+ `SVT-6` は必要最小限の SVD |
| 検証付き数値ライブラリのバージョン不整合・性能 | Route B が遅れる | Route A（exact）で G2 を先に達成．検査器は自前の最小区間演算（有理数区間，`cos`/`sin` は Taylor 剰余で囲い込み）に退避可能 |
| 近似理論（符号関数・$1/x$・Jacobi–Anger）の形式化が重い | 漸近的計算量保証が遅れる | 当面は「具体的な $(\varepsilon,\delta,\kappa)$ に対する証明書」で代替．Lemma 40 から着手 |
| 具体行列の計算が Lean で重い | Phase 5 の証明が詰まる | 代数的（構造的）証明に徹し，`decide` は小さい例だけ |
| lean-quantum 依存によるビルド時間・バージョン追従 | 開発速度低下 | 必要部分のみ複製し，インターフェースを固定 |
| QSP 規約の取り違え（符号・添字） | ソルバー出力と定理の不一致 | `QSP-2` の変換補題を機械的に適用．小さい $d$ で `#eval` による数値照合テスト |
| 「複素係数多項式 f」が Cor 8 の許容条件を満たさない | 入力クラスの縮小 | 前処理（偶奇分解・スケーリング・実虚分離 + LCU）で任意の $f$ を $\alpha_f$ 付きで扱う．$\alpha_f$ は型に残す |

---

## 7. リポジトリ構成案

```
lean-qsvt/
├── lakefile.toml, lean-toolchain, QSVT.lean
├── QSVT/
│   ├── Operator/      -- Qudit, L, †, 射影（lean-quantum 依存 or 最小複製）
│   ├── Polynomial/    -- parity, even/odd, Chebyshev, supNorm
│   ├── QSP/           -- Conventions, Seq, Poly, Structure, Chebyshev, Existence, Perturb
│   ├── Encoding/      -- Projected, Block, LCU, Product, Control, Examples
│   ├── SVT/           -- AltSeq, PhaseOp, SVTransform, QET, QSVT, RealPoly, Robust
│   ├── IR/            -- Expr, Denote, Cost
│   ├── Circuit/       -- Gate, Denote, Cost, Compile, Correct, Qasm
│   ├── Certificate/   -- ChebCoeff, Interval, Check, Sound
│   ├── Frontend/      -- Normalize, Admissible
│   ├── Lang/          -- Macros, Notation
│   └── Examples/      -- FixedPointAA, Threshold, Inverse, HamSim, Loop
├── tools/
│   ├── phases/        -- Python: solver → JSON（untrusted）
│   └── export/        -- QASM 出力・Qiskit 照合テスト
├── blueprint/         -- LeanArchitect
├── test/              -- #eval 回帰テスト，小 d の数値照合
└── 00note/            -- 本計画，仕様，調査メモ
```

---

## 8. 直近 2 週間の具体アクション

1. `lake new` + Mathlib 最新安定版．`QSVT/QSP/Conventions.lean` に $R(x)$, $e^{i\phi\sigma_z}$, `seqR` を定義し，`#eval` で $d=2,3$ の数値を Python と照合．
2. lean-quantum 公開版のツールチェーン更新を試す（半日で判断）．
3. LeanCert を最新 Mathlib でビルドし，`cos (1/3)` の区間評価が kernel で通るか確認．
4. [formal-spec.md](formal-spec.md) の `QSP-3` を Lean の statement として書き（`sorry`），blueprint に登録．
5. QSPPACK で $T_5$ と符号関数近似（$d=21$）の位相を出し，規約変換後に `seqR` の数値と一致することを確認（`QSP-2` の検算）．

---

## 9. 参考文献・既存資産

- Gilyén, Su, Low, Wiebe, *Quantum singular value transformation and beyond*, arXiv:1806.01838（定理番号は本計画の参照元）．
- Martyn, Rossi, Tan, Chuang, *Grand Unification of Quantum Algorithms*, PRX Quantum 2 (2021)（$W_x$ 規約，教育的導入）．
- Low, Chuang, *Hamiltonian simulation by qubitization*, Quantum 3 (2019)．
- Berntson, Sünderhauf, *Complementary polynomials in quantum signal processing*, arXiv:2406.04246（FFT 法）．Alexis, Lin, Mnatsakanyan, Thiele, Wang, Riemann–Hilbert–Weiss 法（証明付き安定性）．Dong, Meng, Whaley, Lin, QSPPACK（最適化法）．
- Motlagh, Wiebe, *Generalized quantum signal processing*, PRX Quantum 5 (2024)．
- Kasaura et al., *Lean-Quantum*, arXiv:2607.05492 と [lean-quantum](../../lean-quantum)．
- inQWIRE/LeanQuantum（Lean 4，MIT）: ゲート・Pauli・Kronecker．
- LeanCert（Reservoir: alerad/LeanCert），girving/interval: 検証付き区間演算．
- Hietala et al., VOQC / SQIR（Coq）; CoqQ; Isabelle の量子 Hoare 論理: 回路コンパイラ検証の先行例．
