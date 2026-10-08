# tools/ — コマンドラインフロントエンド `qsvt` と位相ソルバ補助

## `tools/qsvt`(Phase 7 / CIRC-6)

「プログラムを書く → コスト報告と OpenQASM 回路が出る」ための CLI。`tools/qsvt_cli.lean` を
`lake env lean --run` でスクリプトとして実行する薄いラッパです(`lakefile.toml` に `lean_exe` は
追加していない)。毎回スクリプトを再エラボレートするため 1 回の起動に約 8 秒かかります
(うち約 6 秒は `import QSVT` の olean 読み込み。事前に `lake build` が済んでいること)。

```
tools/qsvt help
tools/qsvt info      <program> [--qubits n] [--pattern i=b,...]
tools/qsvt qasm      <program> [--qubits n] [--pattern i=b,...]
tools/qsvt check     --phases <file.json|list> [--target <file.json|list>] [--eps 1e-12] [--depth 30]
tools/qsvt emit-cert --phases ... [--target ...] [--eps ...] [--depth ...] --name <Name>
```

プログラムの文法は `QSVT.Lang.Notation` の表記をそのまま文字列にしたもの:
`U0`(または `U₀`)、`qsvt[φ1,φ2,...] <p>`、`cheb[c0,c1,...] <p>`、`poly[a0,a1,...] <p>`、
`iter[k] <step> <p>`(`QSVT.Lang.iterate`)。数は整数・小数(`-0.25`, `1e-3`)・分数(`3/4`)で、
すべて厳密な `ℚ` として読まれます。終了コードは 0(成功 / `check` が true)、1(`check` が
false)、2(文法・入力エラー。メッセージは stderr)。

### `info` — `#qsvt_info` と同じ報告

```
$ tools/qsvt info "qsvt[0.5,-0.3333] U0"
program      : qsvt[[1/2, -3333/10000]] U₀
  qsvt       : |Φ| = 2, Re[P_Φ] (GSLW Cor 18), one ancilla qubit, exact
queries      : 2
ancilla      : dimension 2 (1 qubit)
degree bound : 2
scale (ℓ¹)   : 1 ≈ 1.000000
well scaled  : true
gates        : 10 = 4·|Φ| + 2  [oracle U/U†: 2, C_Π NOT: 4, phase: 2, H: 2]  (GSLW Lemma 19)
OpenQASM 3   : 1 qubit + ancilla q[0], Π: q[1]=0  (untrusted output)
OPENQASM 3.0;
...
```

`poly[0,-3,0,4] U0`(`4x³ − 3x = T₃`)では Chebyshev 係数 `[0, 0, 0, 1]`、queries 6、
ancilla 次元 4、degree bound 3 が報告されます。数値は `QSVT.Lang.queriesQ` などの計算可能定義で、
IR のコストと一致することは `queriesQ_eq`、`ancillaDimQ_eq`、`scaleQ_eq`、
`natDegree_spec_toExpr_le` が保証します。

### `qasm` — OpenQASM 3 だけを出力

```
$ tools/qsvt qasm "qsvt[0.5,-0.3333] U0" --qubits 2 --pattern 1=0
OPENQASM 3.0;
include "stdgates.inc";
// lean-qsvt CIRC-6 (untrusted output): q[0] = QSVT ancilla, q[1..n] = system register.
// U_oracle is a placeholder for the block-encoding unitary U on q[1..n]: supply its body.
// rz(θ) below is OpenQASM's diag(e^{-iθ/2}, e^{iθ/2}); the verified gate is e^{iφZ}, θ = -2φ.
gate U_oracle q1, q2 { }
qubit[3] q;
h q[0];
U_oracle q[1], q[2];
negctrl(1) @ x q[2], q[0];
rz(-0.666600000000000) q[0];
negctrl(1) @ x q[2], q[0];
inv @ U_oracle q[1], q[2];
negctrl(1) @ x q[2], q[0];
rz(1.000000000000000) q[0];
negctrl(1) @ x q[2], q[0];
h q[0];
```

`--qubits n` はシステム量子ビット数(補助ビットは `q[0]`、システムは `q[1..n]`)、
`--pattern` は射影 `Π` の制御パターンを 0 始まりの `i=b` で指定します(省略時は全ビット 0 制御、
`none` で `Π = 1`)。単一ステップ `qsvt[...] U0` 以外のプログラムではエラー(終了コード 2)。

### `check` — 位相証明書のプレビュー(信頼されない)

```
$ tools/qsvt check --phases tools/phases/examples/sign21_qsppack.json \
    --target tools/phases/examples/sign21_qsppack.json --eps 1e-12 --depth 30
true
checkRe Φ t ε depth = true  (|Φ| = 21, |t| = 22, ε = 1 / 1000000000000 ≈ 1.000e-12, depth = 30)
interval bound errBoundRe ≈ 7.919e-14 ≤ ε
elapsed (checkRe, IO evaluation): 0.434 s
note: untrusted preview; the trusted certificate is `decide +kernel` in a Lean module (`qsvt emit-cert`).
```

`QSVT.Certificate.checkRe`(CERT-B)をインタプリタで評価します。d = 21 で約 0.4 秒
(`--depth 20` では区間幅 `8.2e-7` で false、0.27 秒)。JSON は `tools/phases/examples/*.json` の
配置を前提に、キー `phases_R_dyadic`(厳密な 2 進有理数。優先)/ `phases_R_decimal` と
`target_chebyshev_coeffs` を探します(`file.json#key` で明示指定、`1/2,-0.25` のようなインライン
リストも可)。`--target` を省くと `--phases` のファイルから読みます。

### `emit-cert` — カーネル証明書の Lean モジュールを生成

```
$ tools/qsvt emit-cert --phases tools/phases/examples/sign21_qsppack.json --eps 1e-12 --depth 30 \
    --name demo > QSVT/Certificate/Demo.lean
```

`demoPhases`、`demoTarget`、`demoEps`、`theorem demo_checkRe : checkRe … = true := by decide +kernel`
と、`sign21_phase_bound` と同じ形の `demo_phase_bound`(`checkRe_sound` + `eval_rePoly_ofReal`)を
含むモジュールが出力されます。有理数は分数リテラルで厳密に書き出されます。生成物を
`lake env lean` でコンパイルすると、sign21(d = 21、depth 30)の `decide +kernel` は約 47 秒、
`T5_qsppack.json`(d = 5)は 1 秒未満でした。

### 信頼境界

CLI は構文解析と印字だけを行う信頼されない便宜層です。`check` が返す true は
インタプリタによる評価結果であり証明ではありません。信頼できる主張は、`emit-cert` の出力を
ライブラリに置いて Lean カーネルが `decide +kernel` で検証した `<Name>_checkRe` と、そこから
`checkRe_sound` で導かれる `<Name>_phase_bound` だけです。同様に `info`/`qasm` の数値・回路は
`QSVT.Lang`・`QSVT.Qubit.Qasm` の計算可能定義の出力で、意味は `baseQ_eq`、`queriesQ_eq`、
`denote_compileQsvtRealQ` が与えます(OpenQASM 文字列自体は CIRC-6 どおり untrusted)。

構文解析器(`parseRat`、`parseProgram`、`parsePattern`、`parseArgs`)の回帰テストは
`tools/qsvt_cli.lean` 末尾の `#guard` で、スクリプトの起動ごとに実行されます。

## `tools/phases/` — 位相ソルバの出力と変換

QSPPACK / pyqsp の位相を R 規約(`seqR`)に変換し JSON に保存するスクリプト群
(`qsp_conventions.py`、`solver_examples.py`)と、Chebyshev 係数の変換(`cheb_to_monomial.py`、
`cos_cheb.py`、`inv_cheb.py`、`rect_cheb.py`)。`examples/*.json` が `check`/`emit-cert` の入力です。
