# QSP 規約の数値検証メモ（Python）

- 作成日: 2026-10-08．対象: [formal-spec.md](formal-spec.md) §0, §2（QSP-2, QSP-3, QSP-4, QSP-5）．
- コード: `tools/phases/qsp_conventions.py`（`verify` で全検査），`tools/phases/solver_examples.py`（ソルバー連携），`tools/phases/examples/*.json`（位相データ）．
- 環境: `tools/phases/.venv`（numpy 2.5.3, scipy 1.18.1, sympy 1.14.0, pyqsp 0.2.0, qsppack 0.4.0）．
- 記法: $s=\sqrt{1-x^2}$，$Z=\sigma_z$，$e^{i\phi Z}=\mathrm{diag}(e^{i\phi},e^{-i\phi})$ = `phaseZ φ`．$P^*$ は係数の複素共役．
  `seqR (φ::Φ) = phaseZ φ * R x * seqR Φ`（$\phi_1$ が最左），`seqW (φ'_0..φ'_k) = phaseZ φ'_0 ∏ (W x * phaseZ φ'_j)`．
  以下の「誤差」はすべて $d\le 8$，乱数位相 25 組 × 乱数 $x$ 5 点での最大絶対誤差（倍精度）．

## 1. 規約変換（QSP-2, GSLW Cor 8 式 (16)）

**式 (16) は右側の符号が誤り**（spec と GSLW の転記）．正しくは
$$W(x) = i\,e^{-i\frac{\pi}{4}Z}\,R(x)\,e^{-i\frac{\pi}{4}Z}\qquad(\text{両側とも } -\pi/4).$$
- 数値: 右が $-\pi/4$ で誤差 $2\times10^{-16}$，右が $+\pi/4$ だと $i e^{-i\pi Z/4}Re^{+i\pi Z/4}=\begin{pmatrix} ix & s\\ -s & -ix\end{pmatrix}\ne W$（誤差 1.41）．sympy でも確認．

**位相の対応式は spec 通りで正しい**（上の正しい式 (16) から導かれる）．$d\ge1$，$\Phi'=(\phi'_0,\dots,\phi'_d)$ に対し
$$\phi_1=\phi'_0+\phi'_d+(d-1)\tfrac{\pi}{2},\qquad \phi_j=\phi'_{j-1}-\tfrac{\pi}{2}\ (2\le j\le d)$$
で $\mathrm{seqW}(\Phi';x)_{00}=\mathrm{seqR}(\Phi;x)_{00}$（誤差 $\le1.5\times10^{-15}$）．試した誤り変種（$\pm\pi/2$ の符号反転，$(d-1)\pi/2$ の符号反転，添字ずらし $\phi_j=\phi'_j-\pi/2$，オフセット無し）は $d$ 偶で $O(1)$ 誤差（$d$ 奇では $\pi$ シフトが偶数個で打ち消して一致することがある．後述の落とし穴）．

**行列全体の正確な関係**（$\theta:=\phi'_d-\pi/4$）:
$$\mathrm{seqW}(\Phi';x)=i^d\,\mathrm{seqR}(\tilde\Phi;x)\,e^{i\theta Z},\quad \tilde\Phi=(\phi'_0-\tfrac\pi4,\ \phi'_1-\tfrac\pi2,\dots,\phi'_{d-1}-\tfrac\pi2)$$
$$\mathrm{seqW}(\Phi';x)=Z^{d}\,e^{-i\theta Z}\,\mathrm{seqR}(\Phi;x)\,e^{i\theta Z}\qquad(\Phi\text{ は上の対応式})$$
（どちらも誤差 $\le1.7\times10^{-15}$）．spec QSP-2 の「全体は位相 $i^d$ と右側の $e^{i(\phi'_d-\pi/4)Z}$ の分だけ異なる」は $\tilde\Phi$ に対する記述で，$\Phi$（$\phi_1$ に $\phi'_d$ を吸収した版）に対しては第 2 式のように $Z^d e^{-i\theta Z}$ が左にも付く．左上成分だけ見れば両者とも一致．

**逆変換 R→W**: $P$ は $\phi'_0+\phi'_d$ にしか依らない（$Q$ は差に依る）ので 1 自由度．`R_to_W(Φ, split)`: $\phi'_{j-1}=\phi_j+\pi/2$ $(2\le j\le d)$，$\phi'_0=\mathrm{split}\cdot c$，$\phi'_d=(1-\mathrm{split})\,c$，$c=\phi_1-(d-1)\pi/2$．往復誤差 $\le 9\times10^{-16}$．

## 2. R 規約の多項式再帰（QSP-3）— Lean 転記用

**行列の形**（$d=|\Phi|$，$x\in[-1,1]$ で成立，誤差 $\le3.6\times10^{-15}$）:
$$\mathrm{seqR}(\Phi;x)=\begin{pmatrix} P(x) & Q^*(-x)\,s\\ Q(x)\,s & P^*(-x)\end{pmatrix}
=\begin{pmatrix} P(x) & (-1)^{d+1}Q^*(x)\,s\\ Q(x)\,s & (-1)^d P^*(x)\end{pmatrix}.$$
$Q$ は**左下**（第 1 列）の多項式に取る．spec の `qspPoly` コメントは $Q$ を右上に書いているが，書かれている再帰は左下の $Q$ に対するもの（再帰自体は正しい）．第 1 列 $(P, Qs)^{\mathsf T}$ は SVT-3 の帰納補題でそのまま使う形．

**2 項再帰**（第 1 列は閉じている．共役・反転を含まない）:
```lean
def qspPoly : List ℝ → ℂ[X] × ℂ[X]
| []       => (1, 0)
| (φ :: Φ) => let (P, Q) := qspPoly Φ
              ( C (exp (I * φ)) * (X * P + (1 - X ^ 2) * Q),
                C (exp (-I * φ)) * (P - X * Q) )
```
すなわち $P_{\phi::\Phi}=e^{i\phi}\,(xP_\Phi+(1-x^2)Q_\Phi)$，$Q_{\phi::\Phi}=e^{-i\phi}\,(P_\Phi-xQ_\Phi)$．

**4 項再帰**（全成分を直接追う版．$\mathrm{seqR}=\begin{pmatrix}P & Q_t s\\ Q_b s & P_b\end{pmatrix}$，sympy で $s^2=1-x^2$ として導出）:
- 基底 $(P,Q_t,Q_b,P_b)_{[]}=(1,0,0,1)$
- $P' = e^{i\phi}\,(xP+(1-x^2)Q_b)$
- $Q_t' = e^{i\phi}\,(xQ_t+P_b)$
- $Q_b' = e^{-i\phi}\,(P-xQ_b)$
- $P_b' = e^{-i\phi}\,((1-x^2)Q_t-xP_b)$

$(P,Q_b)$ は 2 項再帰の $(P,Q)$ と一致（誤差 0）．成分間の関係 $Q_t=Q_b^*\circ(-X)=(-1)^{d+1}Q_b^*$，$P_b=P^*\circ(-X)=(-1)^dP^*$（誤差 0；帰納法で閉じる: $P_b$ の更新式に IH を入れると $(e^{i\phi}(xP+(1-x^2)Q_b))^*(-x)$ に一致）．Lean では 2 項再帰を定義にし，`seqR_eval` は右上・右下を `(Q.map conj).comp (-X)`，`(P.map conj).comp (-X)` で書くのが最短．parity を先に示せば $(-1)^d$ 版に書き換え可能．

**系**（すべて数値確認済，$d\le8$）:
- 次数: $\deg P\le d$，$\deg Q\le d-1$．parity: $P\equiv d$，$Q\equiv d-1 \pmod 2$（違反係数 0）．
- $|P(x)|^2+(1-x^2)|Q(x)|^2=1$（第 1 列のノルム，誤差 $\le6\times10^{-15}$）．
- $\mathrm{qspPoly}(-\Phi)=(P^*,Q^*)$（SVT-8 用，誤差 0）．
- 端点（QSP-5）: $P(\pm1)=(\pm1)^d\prod_j e^{i\phi_j}$；$d$ 偶で $P(0)=e^{-i\sum_{j=1}^d(-1)^j\phi_j}$（誤差 $\le10^{-14}$）．
- 参考: W 規約（GSLW Thm 3 形 $\begin{pmatrix}P & iQs\\ iQ^*s & P^*\end{pmatrix}$）の再帰は $(P,Q)_{[\phi'_k]}=(e^{i\phi'_k},0)$，$(P,Q)_{\phi'::\Phi'}=(e^{i\phi'}(xP-(1-x^2)Q^*),\ e^{i\phi'}(xQ+P^*))$．変換後 $P_W=P_R$（誤差 $\le5\times10^{-14}$，$d=8$ の単項式基底評価）．

## 3. Chebyshev 位相（QSP-4, GSLW Lemma 9）

$\Phi=((1-d)\pi/2,\ \pi/2,\dots,\pi/2)$ で $\max_{x\in[-1,1]}|\mathrm{seqR}(\Phi;x)_{00}-\cos(d\arccos x)|\le3.9\times10^{-15}$（$d\le8$，2001 点）．行列全体は
$$\mathrm{seqR}(\Phi;x)=\begin{pmatrix} T_d(x) & U_{d-1}(x)\,s\\ (-1)^{d+1}U_{d-1}(x)\,s & (-1)^dT_d(x)\end{pmatrix}$$
（$U_{d-1}=T_d'/d$．多項式係数比較で誤差 $\le1.2\times10^{-13}$）．$d=5$ の位相は `examples/T5_lemma9_exact.json`（$\pi$ の有理数倍で記録）．

## 4. ソルバー（pyqsp, QSPPACK）の規約と変換結果

両方とも pip で問題なく導入できた（`pip install pyqsp`，`pip install qsppack`）．どちらも GSLW Thm 3 の W 列 $U=e^{i\phi_0Z}\prod_{j=1}^d W(x)e^{i\phi_jZ}$，$W=\begin{pmatrix}x& is\\ is& x\end{pmatrix}$，位相は $[\phi_0,\dots,\phi_d]$ の順（$\phi_0$ 最左）で，**`seqW` と完全に同じ**．違いは「どの成分を目標 $f$ にするか」:

| ツール / 方法 | 位相の対称性 | 目標の読み方 | R 規約への写し方 |
|---|---|---|---|
| pyqsp `laurent`（`Wx`, measurement `x`） | 非対称（$\phi_d-\phi_0=\pi/2$） | $\langle+|U|+\rangle=\mathrm{Re}P+is\,\mathrm{Re}Q=f$，つまり $\mathrm{Re}P=f,\ \mathrm{Re}Q=0$ | そのまま `W_to_R` |
| pyqsp `sym_qsp`（Chebyshev 係数入力，返値 `(full, reduced, parity)`） | 対称 | $\mathrm{Im}\,U_{00}=\mathrm{Im}P=f$ | 両端から $\pi/4$ を**引いて**（$U_{00}\mapsto -iU_{00}$）$\mathrm{Re}P=f$ にしてから `W_to_R` |
| QSPPACK `qsppack.solve(reduced_cheb, parity, {targetPre: True, typePhi: 'full'})` | 対称（両端に $+\pi/4$ 込み） | $\mathrm{Re}\,U_{00}=\mathrm{Re}P=f$ | そのまま `W_to_R` |

- 入力は全ツール Chebyshev 係数（QSPPACK と pyqsp `sym_qsp` は parity に応じた「reduced」係数 `coef[parity::2]`）．pyqsp `laurent` は `suc`（既定 $1-10^{-4}$）で目標を縮め，`eps` で最高次に加算するため，既定では $P$ が目標と $10^{-4}$ 程度ずれる（T_5 は `suc=1, eps=0` で厳密解が得られた）．
- QSPPACK: $\|f\|_\infty=1$ の T_5 では既定の FPI が劣線形収束（3000 反復で $2\times10^{-7}$）．`method: 'Newton'` なら 22 反復で $3\times10^{-14}$．$\|f\|_\infty<1$ の目標なら FPI/Newton/LBFGS いずれも収束．`NLFT` は T_5 で NaN．
- 同じ目標に対し QSPPACK の full 位相 = $-$(pyqsp `sym_qsp` の full 位相) $+\pi/4$（両端）．位相の全符号反転は $P\mapsto P^*$（§2 の系）なので整合的．

**検証結果**（`seqR` で 2001 点グリッド評価；`examples/*.json` の `errors`）:

| 例 | $d$ | $\max|\mathrm{seqW}_{00}-\mathrm{seqR}_{00}|$ | $\max|\mathrm{Re}\,\mathrm{seqR}_{00}-f|$ | $\max|\mathrm{Im}\,\mathrm{seqR}_{00}|$ |
|---|---|---|---|---|
| T5_pyqsp_laurent（suc=1, eps=0） | 5 | $7\times10^{-16}$ | $1.3\times10^{-15}$ | $3\times10^{-8}$ |
| T5_pyqsp_symqsp | 5 | $8\times10^{-16}$ | $1.4\times10^{-13}$ | $5\times10^{-7}$ |
| T5_qsppack（Newton） | 5 | $6\times10^{-16}$ | $3.5\times10^{-14}$ | $3\times10^{-7}$ |
| sign21_pyqsp_laurent（既定 suc, eps） | 21 | $1.8\times10^{-15}$ | $1.4\times10^{-4}$ | 0.72 |
| sign21_pyqsp_symqsp | 21 | $1.7\times10^{-15}$ | $2.1\times10^{-15}$ | 0.72 |
| sign21_qsppack（FPI, 65 反復） | 21 | $3.5\times10^{-15}$ | $6.2\times10^{-14}$ | 0.72 |

- T_5: W 位相は laurent が $(-\pi/4,0,0,0,0,+\pi/4)$，`sym_qsp` 生値が $(\pi/4,0,0,0,0,\pi/4)$（Im 規約；$-\pi/4$ 補正後は全零），QSPPACK Newton が $(0,\dots,0)$ に収束し，R 規約ではいずれも $(0,-\pi/2,-\pi/2,-\pi/2,-\pi/2)$（mod $2\pi$）．Lemma 9 の $(-2\pi,\pi/2,\pi/2,\pi/2,\pi/2)$ とは $\phi_2..\phi_5$ が各 $\pi$ ずれるが $e^{i\pi Z}=-I$ が 4 個で打ち消し，行列として一致（$P=T_5$ が厳密に実）．
- sign21 の目標は pyqsp `PolySign`（$\mathrm{erf}(10x)$ の次数 21 Chebyshev 近似，$\max|f|=0.8924$ に正規化）で，Chebyshev 係数を JSON に同梱．$\mathrm{Im}P\ne0$ は本質的（$\mathrm{Re}P=f$ を LCU で取る GSLW Cor 18 / SVT-8 の前提）．
- JSON の位相は倍精度値の**厳密な**10 進展開（≥30 桁）と二進有理数 `{num, den_log2}` の両方．R 規約の $\phi_1$ は mod $2\pi$ で $(-\pi,\pi]$ に戻してある（`seqR` は各位相について $2\pi$ 周期）．

## 5. 落とし穴

1. 式 (16) の右側は $e^{-i\pi Z/4}$（spec の $+$ は誤植）．位相対応式は正しいので，Lean で QSP-2 を証明するときは式 (16) を直す．
2. $\det R=-1$ のため右下は $P^*$ ではなく $P^*(-x)=(-1)^dP^*(x)$，右上は $Q^*(-x)\,s=(-1)^{d+1}Q^*(x)\,s$（$Q$ は左下）．spec の `seqR Φ x = [[P, Q√], [Q^♯√, P^♯]]` コメントは $Q$ の位置が逆．
3. $e^{i(\phi+\pi)Z}=-e^{i\phi Z}$ なので，位相を $\pi$ ずらす箇所が偶数個なら `seqR` は不変，奇数個なら全体が $-1$ 倍．ソルバー出力の比較・位相の一意性の議論はこの同値を除いて行う（Lemma 9 との比較で実際に現れた）．
4. 単項式基底の係数は次数 21 で $2^{20}$ 規模になり，多項式評価で $10^{-8}$ の誤差が出る．証明書（CERT-B）側でも Chebyshev 基底で再帰を回す方針が妥当．検証は `seqR` の直接評価で行った．
5. pyqsp `laurent` の `suc`/`eps` は目標を変形する．厳密に $P=f$ が欲しい場合は `suc=1, eps=0`（完備化が存在する場合のみ成功）か `sym_qsp`/QSPPACK を使う．
6. pyqsp は `pyqsp.__version__` を持たない（pip 表示 0.2.0）．QSPPACK Python 版は PyPI `qsppack`（0.4.0）で，GitHub の MATLAB 版と `targetPre`/`typePhi` の意味は同じ．
