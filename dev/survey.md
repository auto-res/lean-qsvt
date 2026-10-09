# Phase 0 サーベイ: 依存ライブラリと Mathlib API（Lean v4.34.1 / Mathlib v4.34.1）

- 作成日: 2026-10-08．対象: [plan.md](plan.md) Phase 0 の成果物 `dev/survey.md`（D1・D5 の採否判断の根拠）．
- 検証環境: macOS (Darwin 25.2), elan 4.2.4, Lean `v4.34.1`，Mathlib tag `v4.34.1`（commit `d13f23b7`, 2026-09-24）．
- スクラッチ: `/private/tmp/claude-501/-Users-shosonoda-work-quantum-lean-qsvt/32fd056f-3e39-40c7-9f82-2a840d613258/scratchpad/`
  （`lcproj/` = LeanCert 検証プロジェクト（`LcTest/*.lean` がテスト），`lq/lean-quantum/` = lean-quantum の v4.34.1 化クローン（`build.log`），`src/` = 各リポジトリの読み取り用クローン）．
- 判定の凡例: **採用** / **条件付き採用** / **不採用**．

---

## A. LeanCert（検証付き数値計算）

### 事実
- リポジトリ: GitHub `alerad/LeanCert`（Reservoir 同名）．タグ **`v4.34.1`**（commit `7f91b6eb`, 2026-09-29）が存在し，`lean-toolchain` = `leanprover/lean4:v4.34.1`，`lakefile.toml` は Mathlib を `git = "https://github.com/leanprover-community/mathlib4.git", rev = "v4.34.1"` で固定．Lean のパッチごとにタグを打つ運用（`v4.30.0.1`…`v4.33.1`, `v4.34.0`, `v4.34.1`）．ライセンス Apache-2.0．488 ファイル．
- 依存の書き方（README「Install」，TOML）:
  ```toml
  [[require]]
  name = "leancert"
  git = "https://github.com/alerad/leancert"
  rev = "v4.34.1"
  ```
  我々の `lakefile.toml` では Mathlib 側も `rev = "v4.34.1"` にそろえる（同一 rev なので manifest 衝突なし；実際に衝突なしで `lake update` が通った）．
- ビルド時間（スクラッチ `lcproj`）: `lake update` **4 分 30 秒**（Mathlib clone + post-update hook の `cache get` を含む），`lake exe cache get` 9 秒．**LeanCert 本体の olean はキャッシュ配布されない**ので `lake build LeanCert.Tactic LeanCert` でソースビルド: **4 分 46 秒**（4,223 ジョブ中 325 モジュールをコンパイル，CPU 938%，エラー 0）．導入合計 ≈ 10 分．CI では `.lake` のキャッシュ保存が必須．
- 公開 API（`LeanCert/Core`, `LeanCert/API`）:
  - 式言語 `LeanCert.Core.Expr`（`LeanCert/Core/Expr.lean:264`）: `const (q : ℚ) | var | add | mul | neg | inv | exp | sin | cos | log | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst (π, γ…)`，意味 `Expr.eval (ρ : ℕ → ℝ) : Expr → ℝ`．
  - 区間型 `LeanCert.Core.IntervalRat`（`structure lo hi : ℚ, le : lo ≤ hi`; `LeanCert/Core/IntervalRat/Basic.lean:39`），`Membership ℝ IntervalRat`（`mem_def : x ∈ I ↔ (I.lo:ℝ) ≤ x ∧ x ≤ I.hi`），演算 `add/neg/sub/mul/scale/intersect/bisect/singleton`，健全性 `mem_add (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ add I J`，`mem_mul`，`mem_neg`，`mem_sub`，`mem_scale`，`mem_singleton`．
  - 三角関数: `IntervalRat.cosComputable (I) (n := 10) : IntervalRat`（Taylor n 次 + 剰余，`[-1,1]` と交差; `Core/IntervalRat/Taylor.lean:350`），定理 `mem_cosComputable {x I} (hx : x ∈ I) (n) : Real.cos x ∈ cosComputable I n`（同 :1174），`sinComputable`/`mem_sinComputable`（:297/:1140），範囲縮約版 `cosComputableReduced`/`mem_cosComputableReduced`（`Core/IntervalRat/TrigReduced.lean:81/:111`）．平方根: `sqrtInterval`, `sqrtIntervalTight(Prec)`, `mem_sqrtInterval'`（`Core/IntervalRat/Transcendental.lean:374–691`）．
  - 統合評価器: `LeanCert.evalInterval (e : Expr) (box : List IntervalRat) (opts) : EvalResult IntervalOutcome` と `evalInterval_correct`, `evalInterval1_correct`（`LeanCert/API/Eval.lean`）．バックエンドは Rational / Dyadic（`Core/IntervalDyadic.lean`）/ Affine．
- タクティク（`docs/reference/tactics.md`）: `leancert`, `leancert?`（ルータ＋診断），`certify_bound [depth] (trust := …)`（量化された区間上の bound 専用），`interval_decide`（点比較），`enclosure_bound`, `bernstein_bound`, `interval_roots`, `interval_minimize` 等．信頼モード: `native`（既定，`native_decide`），**`kernel`（`decide +kernel` のみ，フォールバックなし）**，`auto`．`set_option leancert.trust "kernel"` でファイル単位指定，`#assert_trust kernel thm` で CI 固定可．
- 実験結果（`lcproj/LcTest/Cos2.lean`, `Cos3.lean`, `Api2.lean`；各ファイル 9 秒前後で処理）:
  - `(0.944:ℝ) ≤ Real.cos (1/3) ∧ Real.cos (1/3) ≤ 0.945`: `leancert` ✓（native），`leancert (trust := kernel)` ✓（`#print axioms` = `[propext, Classical.choice, Quot.sound]`）．
  - 幅 2e-9: `0.9449569453 < cos(1/3) ∧ cos(1/3) < 0.9449569473` は `leancert (taylorDepth := 20) (trust := kernel)` ✓．幅 1e-12（`0.944956946314 < … < 0.944956946315`）も `(taylorDepth := 25) (trust := kernel)` ✓．
  - `0.327 < Real.sin (1/3) ∧ Real.sin (1/3) < 0.3272`，`1.41421 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41422`: kernel ✓．
  - 量化: `∀ x ∈ Set.Icc (0:ℝ) 1, Real.cos x ≤ 1.0001`，`∀ x ∈ Set.Icc (-1:ℝ) 1, 4*x^3 - 3*x ≤ 1.001`（$T_3$）: kernel ✓．
  - 不可・要注意: 点の `Set.Icc` 所属 `Real.cos (1/3) ∈ Set.Icc 0.944 0.945` は "unsupported theorem shape"（連言で書く）．`|cos(1/3) − 0.9449569463| < 1e-9` は深さ 20 でも失敗（`abs` が `sqrt(x²)` に展開され Rational backend の sqrt が粗い; 両側不等式で書く）．`1e-9` 形の指数リテラルは `certify_bound` の構文解析で不支持（`0.000000001` 形は可），`certify_bound` は点比較を受け付けない（`interval_decide`/`leancert` を使う）．`∀ x, cos²x + sin²x ≤ 1.001` は区間依存性問題で失敗（想定内）．
  - プログラマブル API: `third := IntervalRat.singleton (1/3)` に対し `#eval cosComputable third 10` → `[835240519447/883892671200, 477280296827/505081526400]`（≈[0.9449569463, 0.9449569464]）．`mem_cosComputable (mem_singleton (1/3)) 20` で `Real.cos ((1/3:ℚ):ℝ) ∈ cosComputable third 20`，`push_cast` で実リテラル形に，`decide +kernel` で `(cosComputable third 20).hi < 945/1000` を閉じ，合成して `Real.cos (1/3) < 945/1000`（公理 `[propext, Classical.choice, Quot.sound]`）．`IntervalRat.add/mul` + `mem_add/mem_mul` で Horner ループ `horner (c : List ℚ) (I : IntervalRat)` と健全性 `horner_sound : (c.foldr (fun ck acc => (ck:ℝ) + x*acc) 0) ∈ horner c I` を 10 行で証明でき，`decide +kernel` で評価結果の上界を判定できた．→ Route B の検査器（Chebyshev 係数の区間評価ループ＋`check_sound`）を `IntervalRat` 上に自前実装することは十分可能．

### 判定
**採用**（Route B の第一候補）: v4.34.1 タグが Mathlib v4.34.1 と完全一致し約 10 分で導入でき，`sin/cos/sqrt` の kernel 検証（`decide +kernel`）が点・区間の両方で通り，`IntervalRat` と `mem_*` 健全性定理が公開 API として使えるため自前の証明書検査器を構築できる．注意: (i) LeanCert の olean は毎回ソースビルド，(ii) ゴールは連言・両側不等式で書き `abs`・`Set.Icc` 所属・`1e-9` 記法を避ける，(iii) Lean 更新への追随はタグ待ち（過去実績は良好）．

### 代替: girving/interval
- `lean-toolchain` = **`v4.27.0-rc1`**（HEAD 5683bf0, 2026-08-09; Mathlib は `master` 追随で rev `725c803e`），タグなし．`Interval`（64+64bit ソフト浮動小数 `Floating` の区間），`Box`（複素），型クラス `Approx`，`Interval.approx_sin/approx_cos`（`Interval/Interval/Sincos.lean:439/446`），`Interval/Interval/Sqrt.lean`．`interval` タクティクは **`native_decide` 前提**（`Interval/Tactic/Interval.lean` の警告文）．v4.34.1 への更新は自前作業になるためビルド未実施．
- 判定: **不採用**（Lean 版が 7 マイナー遅れ，kernel 検証モードなし；LeanCert が破綻した場合の第 2 候補として記録のみ）．

---

## B. lean-quantum（基底非依存の作用素論）

### 事実
- 公開版（`/Users/shosonoda/work/quantum/lean-quantum`, commit e8603bc）は `leanprover/lean4:v4.29.0-rc6`，Mathlib は `scope = "leanprover-community"`・rev 指定なし（manifest は `f156f7ab`）．
- スクラッチで `lean-toolchain → v4.34.1`，`[[require]] mathlib` に `rev = "v4.34.1"` を追加，`checkdecls` 依存を削除．`lake update` 4 分 29 秒（Mathlib clone + cache），`lake exe cache get` 9 秒．
- `lake build Quantum.QuantumMechanics.QuantumState Quantum.QuantumMechanics.QuantumChannel`: **1 分 15 秒で終了．`QuantumState` は成功（30 秒，style 警告 1 件のみ），`QuantumChannel` は失敗（error 31 件，warning 約 40 件）**．
- 失敗の内訳（`lq/build.log`）: `Function expected` 14 件（例 l.210: `LinearMap.nonneg_iff_isPositive` の引数が explicit→implicit に変わり `(… Y).mp` が壊れる），`Type mismatch` 11 件（例 l.636: `LinearMap.adjoint_inner_left` の結論が `adjoint f` だが期待は `star f`，star/adjoint の正規形変更；l.261: 非推奨 `TensorProduct.induction_on` の motive 推論失敗），`instance` の返り型が class でない hard error 2 件（l.46 `linear_isometry_equiv : L ℋ ≃ᵢ (ℋ →L[ℂ] ℋ)`, l.136 `l_tensor_equiv`），`ℋ₁ ⊗[ℂ] ℋ₂` の `ext` 定理不在 1 件（l.377），`rfl` 失敗 1 件（l.954, `CStarMatrix`/`PiLp` 周り），unsolved goals 2 件．非推奨: `TensorProduct.induction_on`→`inductionOn`（7 件），`LinearEquiv.ofLinear`→`ofLinearMap`，import `Mathlib.Topology.Algebra.Module.LinearMapPiProd`．いずれも機械的修正で直る種類だが 2,534 行・約 30 箇所，さらに `Quantum.lean` 配下の TraceInequality/QuantumEntropy 群は未検証．
- `QuantumState.lean`（71 行，Apache-2.0）で流用したい宣言（namespace `QuantumState`）: `class Qudit (a) extends NormedAddCommGroup a, InnerProductSpace ℂ a, CompleteSpace a, FiniteDimensional ℂ a`；`abbrev L ℋ := ℋ →ₗ[ℂ] ℋ`；`abbrev I ℋ := LinearMap.id`；`notation "⟨" x "∣" y "⟩" => inner ℂ x y`；`notation X"†" => LinearMap.adjoint X`；`noncomputable abbrev Tr := LinearMap.trace ℂ ℋ`；`def IsPositiveDefinite X := X.IsPositive ∧ X.det ≠ 0`；`def IsProjective X := X.IsPositive ∧ IsIdempotentElem X`；`def IsDensity X := X.IsPositive ∧ Tr X = 1`．正規・Hermite・半正定値・ユニタリは Mathlib の `IsStarNormal`, `IsSelfAdjoint`, `LinearMap.IsPositive`, `X ∈ unitary (L ℋ)` をそのまま使う方針（ファイル内コメントで明示されている）．
- `QuantumChannel.lean` で将来欲しいもの: `Norm (L ℋ)`（`toContinuousLinearMap` 経由），`CStarAlgebra`/`StarOrderedRing` の `L ℋ` への転送，超作用素 `T ℋ₁ ℋ₂`，`CPTP`，`IsCompletelyPositive`，Choi/Kraus 表現．QSVT の Phase 1–5 では不要（Phase 6 の後選択・POVM で再検討）．

### 判定
**条件付き採用（最小複製）**: `require` は現時点で不可能（QuantumChannel が v4.34.1 で壊れ，上流は v4.29.0-rc6 のまま）．`QuantumState.lean` の約 70 行を `QSVT/Operator/Basic.lean` に Apache-2.0 表記付きで複製し，名前空間・定義を上流と同一に保って将来 `require` に差し替え可能にする．

---

## C. Mathlib v4.34.1 API 確認

確認方法: スクラッチの `.lake/packages/mathlib`（tag `v4.34.1`, commit `d13f23b7`）を grep．パスは `Mathlib/` 以下，行番号は同 commit．

| 対象 | 宣言名（抜粋） | ファイル |
|---|---|---|
| Chebyshev 定義・再帰 | `Polynomial.Chebyshev.T : ℤ → R[X]`（引数は **ℤ**），`T_zero`, `T_one`, `T_two`, `T_add_two : T (n+2) = 2*X*T (n+1) - T n`, `T_add_one`, `T_sub_one`, `T_eq`, `T_neg`, `T_natAbs`, `degree_T`, `natDegree_T`, `leadingCoeff_T` | `RingTheory/Polynomial/Chebyshev.lean` :70–225 |
| Chebyshev 積・合成・parity | `T_mul_T (m k) : 2 * T R m * T R k = T R (m+k) + T R (m-k)`（:1084; m=1 で $xT_k=(T_{k+1}+T_{k-1})/2$），`T_mul : T (m*n) = (T m).comp (T n)`（:1117），`T_eval_neg : (T n).eval (-x) = n.negOnePow * (T n).eval x`（:243），`T_eval_one`, `T_eval_neg_one`, `T_eval_zero_of_even/odd` | 同上 |
| Chebyshev と cos | `Polynomial.Chebyshev.T_complex_cos (n : ℤ) : (T ℂ n).eval (cos θ) = cos (n*θ)`（:54），`T_real_cos : (T ℝ n).eval (cos θ) = cos (n*θ)`（:148），`complex_ofReal_eval_T`（:28），`U_complex_cos`, `U_real_cos` | `Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean` |
| $\lvert T_n\rvert\le1$ | `abs_eval_T_real_le_one (n : ℤ) (hx : \|x\| ≤ 1) : \|(T ℝ n).eval x\| ≤ 1`（:46），`eval_T_real_mem_Icc`（:41），`roots_T_real`（:163） | `…/Chebyshev/RootsExtrema.lean`（他に `Orthogonality.lean`, `Extremal.lean`, `ChebyshevGauss.lean`） |
| ユニタリ群 | `Matrix.unitaryGroup n α : Submonoid (Matrix n n α)`（`abbrev`, `= unitary (Matrix n n α)`; :60），`Matrix.mem_unitaryGroup_iff : A ∈ unitaryGroup n α ↔ A * star A = 1`（:72），`mem_unitaryGroup_iff'`（`star A * A = 1`; :76），`det_of_mem_unitary`（:80），`UnitaryGroup.toLin'`, `toGL` | `LinearAlgebra/UnitaryGroup.lean` |
| 作用素のユニタリ・star | `instance : StarRing (E →ₗ[𝕜] E)`（:720），`LinearMap.star_eq_adjoint`（:726），`LinearMap.isSelfAdjoint_iff'`（:730），`LinearMap.isSymmetric_iff_isSelfAdjoint`（:733），`LinearMap.id_mem_unitary`．したがって `X ∈ unitary (L ℋ)` が使える | `Analysis/InnerProductSpace/Adjoint.lean` |
| スペクトル定理（線形写像） | `LinearMap.IsSymmetric.eigenvalues (hT) (hn : finrank 𝕜 E = n) : Fin n → ℝ`（**値域が ℝ**; :279），`eigenvectorBasis : OrthonormalBasis (Fin n) 𝕜 E`（:300），`hasEigenvector_eigenvectorBasis`（:306），`apply_eigenvectorBasis : T (b i) = (eigenvalues i : 𝕜) • b i`（:325），`eigenvectorBasis_apply_self_apply`（:332），`eigenvalues_antitone`, `exists_eigenvalues_eq`（:283），`conj_eigenvalue_eq_self`（:94） | `Analysis/InnerProductSpace/Spectrum.lean` |
| 対称性・不変部分空間 | `LinearMap.IsSymmetric`（:59），`IsSymmetric.restrict_invariant (hT) {V} (hV : ∀ v ∈ V, T v ∈ V) : IsSymmetric (T.restrict hV)`（:137） | `Analysis/InnerProductSpace/Symmetric.lean` |
| Hermite 行列 | `Matrix.IsHermitian.eigenvalues : n → ℝ`（:67），`eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)`（:71），`mulVec_eigenvectorBasis`（:75），`eigenvectorUnitary`（:89），`spectral_theorem : A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))`（:143），`spectrum_real_eq_range_eigenvalues`（:213）；`Matrix.isHermitian_iff_isSelfAdjoint`（`LinearAlgebra/Matrix/Hermitian.lean:51`） | `Analysis/Matrix/Spectrum.lean` |
| CFC | `cfc (f : R → R) (a : A) : A`（`irreducible_def`; :307），`cfc_apply`（:317），`cfc_id`（:383），`cfc_const`（:395），`cfc_congr`（:416），`cfc_mul`（:468），`cfc_pow`, `cfc_add`, **`cfc_polynomial (q : R[X]) (a) : cfc q.eval a = aeval a q`**（:597），`cfc_map_polynomial`（:585），`cfc_comp_polynomial`（:651），`cfc_eval_X`, `cfc_eval_C` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean` |
| CFC ノルム | `norm_cfc_le {f a c} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum 𝕜 a, ‖f x‖ ≤ c) : ‖cfc f a‖ ≤ c`（:103），`norm_cfc_le_iff`（:112），`norm_cfc_lt`（:117），`nnnorm_cfc_le`（:133），`IsGreatest.norm_cfc`（:70），`norm_apply_le_norm_cfc`（:91）．`IsSelfAdjoint.norm_cfc_le` という名前は無い（一般形で十分） | `…/ContinuousFunctionalCalculus/Isometric.lean` |
| CFC インスタンス | `IsSelfAdjoint.instContinuousFunctionalCalculus`（`…/Instances.lean:234`; 任意の `CStarAlgebra`），`CStarAlgebra (E →L[ℂ] E)`（`Analysis/CStarAlgebra/ContinuousLinearMap.lean:21`），行列は `Matrix.IsHermitian.instContinuousFunctionalCalculus`（`Analysis/Matrix/HermitianFunctionalCalculus.lean:97`）と `IsHermitian.cfc_eq`（:143）．**注意: CFC は `ℋ →L[ℂ] ℋ` 上．`L ℋ = ℋ →ₗ[ℂ] ℋ` には `toContinuousLinearMap` で橋渡しが必要（lean-quantum の `QuantumChannel.lean` がやっていること）** | |
| aeval と固有ベクトル | **`Module.End.aeval_apply_of_hasEigenvector (h : f.HasEigenvector μ x) : aeval f p x = p.eval μ • x`**（`LinearAlgebra/Eigenspace/Minpoly.lean:51`）— D3 の「固有ベクトル単位の帰納法」はこれと `eigenvectorBasis` だけで CFC 不要．`Module.End.hasEigenvalue_iff_mem_spectrum [FiniteDimensional]`（`LinearAlgebra/Eigenspace/Basic.lean:526`）で `norm_cfc_le` の `spectrum` 条件を固有値条件に落とせる | |
| 多項式の共役 | 専用の `Polynomial.conj` は**無い**．`Polynomial.map (starRingEnd ℂ)` と汎用補題 `Polynomial.coeff_map`（`Algebra/Polynomial/Eval/Coeff.lean:78`），`Polynomial.eval_map : (p.map f).eval x = p.eval₂ f x`（`Eval/Defs.lean:577`），`Polynomial.degree_map`/`natDegree_map`（`FieldDivision.lean:277/281`），`Polynomial.map_map`，`starRingEnd_apply`, `starRingEnd_self_apply`（`Algebra/Star/Basic.lean:353/356`）．`eval (conj z) (P.map conj) = conj (eval z P)` は自前補題（`Polynomial.hom_eval₂` から数行） | |
| 偶・奇多項式 | **Mathlib に無い**．`Function.Even/Odd`（`Algebra/Group/EvenFunction.lean`）は関数用．Chebyshev の parity は `T_eval_neg` 経由．POLY-1 は自前定義（例 `IsEven P := ∀ k, Odd k → P.coeff k = 0`，または `P.comp (-X) = P`） | |
| Kronecker 積 | `Matrix.kroneckerMap (f) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ`（:55），`Matrix.kronecker := kroneckerMap (*)`（:274），記法 `A ⊗ₖ B`（`open Kronecker`），`kronecker_apply`, `mul_kronecker_mul`, `one_kronecker_one`（:368），`kroneckerMap_reindex`（:164），`kroneckerMap_assoc`（:183），`det_kroneckerMapBilinear`, `trace_kroneckerMapBilinear`．添字は**積型** `l × n`；qubit 添字 `Fin n → Bool` へは `Matrix.reindex` + `Equiv`（`Fin.consEquiv`/`Equiv.piFinSucc` 系）で写す | `LinearAlgebra/Matrix/Kronecker.lean` |
| 部分空間への制限 | `LinearMap.restrict (f) {p q} (hf : ∀ x ∈ p, f x ∈ q) : p →ₗ q`（:209），`restrict_apply`（:223），`restrict_coe_apply`（:219），`restrict_comp`, `restrict_commute`, `restrict_eq_codRestrict_domRestrict` | `Algebra/Module/Submodule/LinearMap.lean` |
| 部分空間の内積構造 | `instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W`（`.induced W.subtype`; :36），`ClosedSubmodule.innerProductSpace`（:61）；`NormedAddCommGroup W`，`FiniteDimensional 𝕜 W` は既存インスタンスで自動 | `Analysis/InnerProductSpace/Subspace.lean` |
| 随伴（有限次元） | `LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E`（:552; `[FiniteDimensional]`），`adjoint_inner_left`（:587），`adjoint_inner_right`（:594），`adjoint_adjoint`（:602），`adjoint_comp`（:610），`eq_adjoint_iff`（:618），`adjoint_toContinuousLinearMap`（:568）；CLM 版 `ContinuousLinearMap.adjoint`（:114） | `Analysis/InnerProductSpace/Adjoint.lean` |
| SVD / 極分解 | **無い**（`Matrix.svd`, `polarDecomposition`, "singular value decomposition" とも 0 件）．新規に `LinearMap.singularValues : ℕ →₀ ℝ`（$T^\dagger T$ の固有値の平方根; `Analysis/InnerProductSpace/SingularValues.lean:94`, 2026, `sq_singularValues_fin`, `hasEigenvalue_adjoint_comp_self_sq_singularValues`）があるが**特異ベクトル・分解定理は無い**．D3（SVD を使わない定式化）は妥当 | |

### 判定
**採用**: 必要 API はすべて存在．自前で用意するのは偶奇多項式（POLY-1）・多項式共役補題・`L ℋ`↔`ℋ →L[ℂ] ℋ` の橋渡し・qubit 添字の Kronecker のみ．

---

## D. inQWIRE/LeanQuantum（qubit ゲート層）

### 事実
- GitHub `inQWIRE/LeanQuantum`，HEAD 44fc4eb（2026-05-15），**`lean-toolchain` = `v4.30.0-rc2`**（2026-04-25 に v4.26 から更新済み），Mathlib は rev `c1e30e17`（タグなし），タグ・リリースなし．**MIT License（Copyright (c) 2025 INQWIRE）**→ 著作権表示と許諾文を残せばコピー可．28 ファイル，`Data/Gate` 周りで約 1.7k 行．ビルドは未実施（読むだけ）．
- 型: `CMatrix m n := Matrix (Fin m) (Fin n) ℂ`，`CVector n := CMatrix n 1`，`CSquare n`（`Quantumlib/ForMathlib/Data/Matrix/Basic.lean`）．**添字は `Fin (2^n)`**（bit-vector 添字ではない）．
- Kronecker（`ForMathlib/Data/Matrix/Kron.lean`, 187 行）: `Matrix.kron (m₁ : CMatrix a b) (m₂ : CMatrix c d) : CMatrix (a*c) (b*d)` を `Fin.divNat/modNat` で直接定義，`kron_def` で Mathlib の `⊗ₖ` を `reindex finProdFinEquiv` したものと一致．scoped 記法 `⊗`（`open Kron`）．補題: `kron_apply`, `zero_kron`, `add_kron`, `smul_kron`, `one_kron_one`, `kron_one`, `one_kron`, `mul_kron_mul`, `kron_assoc`（**`reindex (finCongr (Nat.mul_assoc ..))` を伴う**），`trace_kron`, `det_kron`, `inv_kron`, `transpose_kron`, `conjTranspose_kron`．
- テンソル冪（`ForMathlib/Data/Matrix/PowBitVec.lean`）: `CMatrix.powBitVec (M : CMatrix m m) (x : BitVec n) : CMatrix (m^n) (m^n)`（記法 `^ᵥ`；ビット i が 1 なら M，0 なら 1 を並べる），`powBitVec_zero`, `one_powBitVec`, `powBitVec_mul_powBitVec`, `powBitVec_cons`．`hadamardK k := hadamard ^ᵥ BitVec.allOnes k`．
- ゲート（`Data/Gate/Basic.lean`, `Rotate.lean`, `PhaseShift.lean`, `Pauli/Defs.lean`）: `hadamard`, `sqrtx`, `controlM (M : CSquare n) : CSquare (2*n)`（`Fin.subNat` によるブロック対角定義），`cnot`, `notc`, `swap`（`!![…]` の具体行列），`σx σy σz`，`rotate θ φ δ`（U3），`xRotate`, `yRotate`，`phaseShift φ = diag(1, e^{iφ})`，`sGate`, `tGate`．**`Rz`/`e^{iφσ_z}` は無い**（`e^{iφσ_z} = e^{iφ} • phaseShift (-2φ)` で作る）．
- ユニタリ性（`ForMathlib/Data/Matrix/Unitary.lean`, `Data/Gate/Unitary.lean`）: `Matrix.IsUnitary (M : CSquare n) := M ∈ Matrix.unitaryGroup (Fin n) ℂ`，閉包補題 `kron_of_isUnitary`, `mul_of_isUnitary`, `conjTranspose_of_isUnitary`, `smul_of_isUnitary`，個別 `rotate_isUnitary`, `hadamard_isUnitary`, `σx/σy/σz_isUnitary`, `phaseShift_isUnitary`, `controlM_isUnitary`, `cnot_isUnitary`, `swap_isUnitary`．`ConjTranspose.lean`: `controlM_conjTranspose`, `rotate_conjTranspose`, `phaseShift_conjTranspose`．`Equivs.lean`: `hadamard_mul_hadamard`, `controlM_def`, `controlM_mul_controlM`, `controlM_σx : controlM σx = cnot`, `cnot_decompose : ∣1⟩⟨1∣ ⊗ σx + ∣0⟩⟨0∣ ⊗ 1 = cnot`, `phaseShift_mul_phaseShift`, `phaseShift_pow`．
- 基底: `ket0 ket1 : CVector 2`, `bra0 bra1`，マクロ記法 `∣01⟩`, `⟨01∣`（`Data/Basis/Notation.lean`）．
- タクティク `solve_matrix [lemmas]`（`Tactic/SolveMatrix.lean`, 24 行）: `ext i j; simp [mul_apply, kron_apply, blockDiagonal, finProdFinEquiv, Fin.divNat, Fin.modNat, …]; fin_cases i <;> fin_cases j <;> simp! <;> ring_nf`．**固定小次元の具体行列専用**（記号 `n` には使えない）．
- Pauli 群 `Pauli n`（位相 `ZMod 4`, `z x : BitVec n`），`toCMatrix`，stabilizer code（`Data/Error/Operator.lean`）: QSVT には不要．

### 流用できるもの / 注意
- 流用候補（MIT 表記付きコピー，合計 ~400 行）: `kron` の補題セット，`powBitVec`，`IsUnitary` 閉包補題，`controlM` と `controlM_*` 補題，`solve_matrix`，1 qubit ゲート定義．
- 注意: D1 の `Fin n → Bool` 添字を採るなら `kron` は `Matrix.kroneckerMap` + `Matrix.reindex (Fin.consEquiv …)` で定義し直す（`Nat.mul_assoc` キャストが消える）．LeanQuantum の `Fin (2^n)` 流儀を採る場合は `kron_assoc` 型のキャスト補題が至る所で必要になる．

### 判定
**条件付き採用（部分コピー）**: `require` はしない（v4.30.0-rc2，タグなし，Mathlib 追随が不定期）．ゲート定義・ユニタリ性補題・`controlM`・`solve_matrix` を MIT 表記付きで `QSVT/Circuit/` に取り込み，添字体系は我々の D1 に合わせて書き直す．

---

## まとめ（Phase 0 の判断 D1・D5 への入力）

| 項目 | 判定 | 根拠 |
|---|---|---|
| A. LeanCert | 採用 | v4.34.1 タグが Mathlib v4.34.1 と一致，導入約 10 分；cos/sin/sqrt の kernel 検証（点 1e-12 幅・区間 bound）と `IntervalRat` + `mem_*` API による自前 Horner ループの健全性証明を確認 |
| A'. girving/interval | 不採用 | v4.27.0-rc1 止まり，`native_decide` 前提 |
| B. lean-quantum | 条件付き採用（最小複製） | QuantumState は通るが QuantumChannel が 31 エラー；上流 v4.29.0-rc6 |
| C. Mathlib v4.34.1 | 採用 | Chebyshev・スペクトル定理・CFC・Kronecker・adjoint すべて存在．SVD は無い（D3 を維持） |
| D. LeanQuantum | 条件付き採用（部分コピー, MIT） | ゲート・Kronecker・ユニタリ補題は流用価値あり；toolchain v4.30.0-rc2 で依存は不可 |

D1 への示唆: コア定理は `L ℋ` + `Module.End.aeval_apply_of_hasEigenvector` + `LinearMap.IsSymmetric.eigenvectorBasis` で閉じ，ノルム評価のみ `toContinuousLinearMap` 経由で `norm_cfc_le` を使う．D5 への示唆: Route B は LeanCert の `IntervalRat` 上に検査器を書き，`decide +kernel` で閉じる（trusted base は Lean kernel のみ）．
