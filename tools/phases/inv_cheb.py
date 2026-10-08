#!/usr/bin/env python
"""
inv_cheb.py -- an odd polynomial approximation of `c / (kappa x)` on `[-1, -1/kappa] u [1/kappa, 1]`,
bounded by 1 on `[-1, 1]`, as an exact rational monomial coefficient list for
`QSVT.Certificate.PolyQ` (APP-3, matrix inversion / GSLW Lemma 40, Thm 41, Cor 69).

Why a constant `c < 1`.  The natural target `1/(kappa x)` equals `1` at `x = 1/kappa`, so an
odd polynomial that is `eps`-close to it on the gapped region and bounded by `1` on `[-1, 1]`
must have a maximum of height `1 - O(eps)` at `x ~ 1/kappa` while its slope just to the right is
`-kappa`: the clipped function `min(1, 1/(kappa|x|)) sign x` has a kink, and the best uniform
error of degree `d` is only `O(1/d)` (numerically `eps ~ 1e-2` for `kappa = 4` at every degree
`19..39`).  GSLW's bounded-by-one version (Cor. 69) therefore approximates a constant multiple
`c/(kappa x)`; with `c = 3/4` and `kappa = 4` the unconstrained Chebyshev minimax fit stays below
`1` up to degree `29`, and `c = 1/2` is the Thm 41 convention.  `--scale` sets `c`.

Construction (default): a *constrained Chebyshev minimax fit* by linear programming (scipy /
HiGHS, untrusted): the coefficients `a_j` of `p = sum_j a_j T_{2j+1}` minimise `eps` subject to
    |kappa x p(x) / c - 1| <= eps     on a Chebyshev grid of [1/kappa, 1]   (relative error),
    |p(x)| <= 1 - margin              on a Chebyshev grid of [0, 1]         (admissibility).
The admissibility constraint is inactive for the default parameters (`max |p| = 0.974`).

Reference (`--gslw`): GSLW Lemma 40's explicit construction `f(x) = (1 - (1 - x^2)^b) / x`,
`b = ceil(kappa^2 log(kappa/eps))`, truncated in the Chebyshev basis to degree `2J + 1`,
`J = ceil(sqrt(b log(4b/eps)))`, with the exact dyadic coefficients
    g = 4 sum_{j=0}^{J} (-1)^j [ sum_{i=j+1}^{b} C(2b, b+i) / 2^{2b} ] T_{2j+1}.
For `kappa = 4, eps = 1e-3` this has `b = 133`, degree `85`, and `max f = 1.84 kappa` on the
interior, so `f/kappa` is *not* bounded by `1`; it is printed for comparison only.

Only the Lean literal is consumed downstream; the rounding to `--digits` significant digits is
exact (`Fraction(Decimal(s))`), and the Chebyshev -> monomial conversion uses the integer
recursion `T_{k+1} = 2 x T_k - T_{k-1}` over exact rationals (as `cheb_to_monomial.py`).  The
numerical report (mpmath, untrusted) prints the quantities the Lean certificates state:
  * max |kappa x p(x) - c| on [1/kappa, 1] (the absolute `eps` of `invPoly_gap_bound`) and the
    relative error max |kappa x p(x)/c - 1|,
  * max |p(x)| on [-1, 1] and where it is attained (admissibility `|p| <= 1`),
  * the Chebyshev coefficients and the exact l1 norm `sum |c_k|` (the Route A subnormalisation,
    recomputed in Lean by `ChebQC.l1Bound (ChebQC.ofMonomials _)`).

Usage:
  .venv/bin/python inv_cheb.py                              # kappa 4, c = 3/4, degree 29
  .venv/bin/python inv_cheb.py --kappa 4 --scale 1/2 --degree 31
  .venv/bin/python inv_cheb.py --gslw --eps 1e-3           # the Lemma 40 reference numbers
"""
from __future__ import annotations

import argparse
import math
from decimal import Decimal
from fractions import Fraction

import mpmath as mp
import numpy as np
from numpy.polynomial import chebyshev as npcheb
from scipy.optimize import linprog


def cheb_to_monomial(c: list[Fraction]) -> list[Fraction]:
    """Exact monomial coefficients of sum_k c_k T_k (index = degree)."""
    n = len(c)
    if n == 0:
        return []
    out = [Fraction(0)] * n
    t_prev = [0] * n
    t_cur = [0] * n
    t_prev[0] = 1
    if n > 1:
        t_cur[1] = 1
    for k in range(n):
        tk = t_prev if k == 0 else t_cur
        if c[k] != 0:
            for i in range(n):
                if tk[i]:
                    out[i] += c[k] * tk[i]
        if k >= 1 and k + 1 < n:
            t_next = [0] * n
            for i in range(n - 1):
                t_next[i + 1] += 2 * t_cur[i]
            for i in range(n):
                t_next[i] -= t_prev[i]
            t_prev, t_cur = t_cur, t_next
    return out


def frac_lean(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    if q.numerator < 0:
        return f"-{-q.numerator} / {q.denominator}"
    return f"{q.numerator} / {q.denominator}"


def round_sig(x: float | mp.mpf, digits: int) -> Fraction:
    """`x` rounded to `digits` significant decimal digits, as an exact rational."""
    if x == 0:
        return Fraction(0)
    return Fraction(Decimal(mp.nstr(mp.mpf(x), digits, strip_zeros=False)))


def horner_mp(a: list[Fraction], x: mp.mpf) -> mp.mpf:
    acc = mp.mpf(0)
    for q in reversed(a):
        acc = mp.mpf(q.numerator) / q.denominator + x * acc
    return acc


def lp_fit(kappa: int, scale: Fraction, degree: int, margin: float,
           n_gap: int = 1200, n_adm: int = 1600) -> list[float]:
    """Constrained Chebyshev minimax fit (LP): coefficients a_j of T_{2j+1}, j = 0..(degree-1)/2."""
    J = (degree - 1) // 2
    c = float(scale)
    t = np.cos(np.pi * (np.arange(n_gap) + 0.5) / n_gap)
    xg = (1 / kappa + 1) / 2 + (1 - 1 / kappa) / 2 * t
    t2 = np.cos(np.pi * (np.arange(n_adm) + 0.5) / n_adm)
    xa = 0.5 + 0.5 * t2

    def basis(x: np.ndarray) -> np.ndarray:
        V = np.zeros((len(x), J + 1))
        for j in range(J + 1):
            e = np.zeros(2 * j + 2)
            e[2 * j + 1] = 1
            V[:, j] = npcheb.chebval(x, e)
        return V

    Vg, Va = basis(xg), basis(xa)
    w = (kappa * xg / c)[:, None]
    # variables (a_0, ..., a_J, eps); minimise eps
    A_ub = np.vstack([
        np.hstack([w * Vg, -np.ones((n_gap, 1))]),      #  (kappa x / c) p - eps <= 1
        np.hstack([-w * Vg, -np.ones((n_gap, 1))]),     # -(kappa x / c) p - eps <= -1
        np.hstack([Va, np.zeros((n_adm, 1))]),          #  p <= 1 - margin
        np.hstack([-Va, np.zeros((n_adm, 1))]),         # -p <= 1 - margin
    ])
    b_ub = np.concatenate([np.ones(n_gap), -np.ones(n_gap),
                           (1 - margin) * np.ones(n_adm), (1 - margin) * np.ones(n_adm)])
    cost = np.zeros(J + 2)
    cost[-1] = 1
    res = linprog(cost, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)] * (J + 1) + [(0, None)],
                  method="highs")
    if not res.success:
        raise SystemExit(f"LP failed: {res.message}")
    return [float(v) for v in res.x[: J + 1]]


def gslw_lemma40(kappa: int, eps: float) -> tuple[int, int, list[Fraction]]:
    """GSLW Lemma 40: (b, J, exact Chebyshev coefficients c_k of g, index k = degree)."""
    b = math.ceil(kappa ** 2 * math.log(kappa / eps))
    J = math.ceil(math.sqrt(b * math.log(4 * b / eps)))
    two_2b = Fraction(1, 2 ** (2 * b))
    cheb = [Fraction(0)] * (2 * J + 2)
    for j in range(J + 1):
        s = sum(math.comb(2 * b, b + i) for i in range(j + 1, b + 1))
        cheb[2 * j + 1] = 4 * (-1) ** j * s * two_2b
    return b, J, cheb


def report(mono: list[Fraction], cheb: list[Fraction], kappa: int, scale: Fraction,
           grid: int) -> None:
    print("-- Chebyshev coefficients c_k (exact rationals after rounding):")
    for k, c in enumerate(cheb):
        if c != 0:
            print(f"--   c_{k} = {frac_lean(c)}  ≈ {float(c):.12e}")
    l1 = sum(abs(c) for c in cheb)
    print(f"-- l1 norm sum |c_k| = {frac_lean(l1)} ≈ {float(l1):.15f}")

    kap = mp.mpf(kappa)
    c = mp.mpf(scale.numerator) / scale.denominator
    abs_max = mp.mpf(0)
    rel_max = mp.mpf(0)
    for i in range(grid + 1):
        x = 1 / kap + (1 - 1 / kap) * i / grid
        r = kap * x * horner_mp(mono, x) - c
        abs_max = max(abs_max, abs(r))
        rel_max = max(rel_max, abs(r) / c)
    p_max = mp.mpf(0)
    x_max = mp.mpf(0)
    for i in range(grid + 1):
        x = mp.mpf(-1) + mp.mpf(2) * i / grid
        v = abs(horner_mp(mono, x))
        if v > p_max:
            p_max, x_max = v, x
    print(f"-- max |{kappa} x p(x) - {scale}| on [1/{kappa}, 1] (grid {grid + 1}): "
          f"{mp.nstr(abs_max, 6)}  (relative to {scale}/({kappa} x): {mp.nstr(rel_max, 6)})")
    print(f"-- max |p(x)| on [-1,1]: {mp.nstr(p_max, 15)} at x = {mp.nstr(x_max, 6)} "
          f"(1 - max |p| = {mp.nstr(1 - p_max, 6)})")
    print(f"-- p(1/{kappa}) = {mp.nstr(horner_mp(mono, 1 / kap), 15)} (target {mp.nstr(c, 6)}), "
          f"p(1) = {mp.nstr(horner_mp(mono, mp.mpf(1)), 15)} (target {mp.nstr(c / kap, 6)})")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kappa", type=int, default=4, help="condition number bound (gap 1/kappa)")
    ap.add_argument("--scale", default="3/4", help="constant c in the target c/(kappa x)")
    ap.add_argument("--degree", type=int, default=29, help="odd degree of the fit")
    ap.add_argument("--margin", type=float, default=1e-4,
                    help="admissibility constraint |p| <= 1 - margin in the LP")
    ap.add_argument("--digits", type=int, default=30, help="significant digits of the coefficients")
    ap.add_argument("--name", default="invPoly", help="Lean identifier")
    ap.add_argument("--grid", type=int, default=200000)
    ap.add_argument("--gslw", action="store_true",
                    help="emit GSLW Lemma 40's explicit construction instead of the LP fit")
    ap.add_argument("--eps", type=float, default=1e-3, help="eps for the Lemma 40 parameters")
    args = ap.parse_args()

    mp.mp.dps = 50
    kappa = args.kappa
    scale = Fraction(args.scale)

    if args.gslw:
        b, J, cheb = gslw_lemma40(kappa, args.eps)
        cheb = [c * scale / kappa for c in cheb]
        print(f"-- GSLW Lemma 40: kappa = {kappa}, eps = {args.eps}, b = {b}, J = {J}, "
              f"degree {2 * J + 1}; coefficients exact (dyadic), scaled by {scale}/{kappa}")
    else:
        if args.degree % 2 == 0:
            raise SystemExit("degree must be odd")
        a = lp_fit(kappa, scale, args.degree, args.margin)
        cheb = [Fraction(0)] * (args.degree + 1)
        for j, v in enumerate(a):
            cheb[2 * j + 1] = round_sig(v, args.digits)
        print(f"-- {scale}/({kappa} x) on [1/{kappa}, 1], odd, |p| <= 1 - {args.margin} on [-1, 1]: "
              f"constrained Chebyshev minimax fit (LP) of degree {args.degree}")
        print(f"-- coefficients rounded to {args.digits} significant digits")
    mono = cheb_to_monomial(cheb)

    print(f"def {args.name} : PolyQ :=")
    print("  [")
    for i, q in enumerate(mono):
        sep = "," if i + 1 < len(mono) else ""
        print(f"    {frac_lean(q)}{sep}  -- x^{i} ≈ {float(q):.6e}")
    print("  ]")
    report(mono, cheb, kappa, scale, args.grid)


if __name__ == "__main__":
    main()
