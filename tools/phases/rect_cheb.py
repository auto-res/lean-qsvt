#!/usr/bin/env python
"""
rect_cheb.py -- an even polynomial approximation of the rectangle (window) function

    rect(x) = 1  for |x| <= t - delta,      rect(x) = 0  for |x| >= t + delta,

bounded by 1 on [-1, 1], as an exact rational monomial coefficient list for
`QSVT.Certificate.PolyQ` (APP-2: the singular value threshold projector of GSLW Lemma 29 /
Thm 31, in the Hermitian case an eigenvalue window filter).  Defaults: `t = 1/2`,
`delta = 1/10` (transition band [0.4, 0.6]), accuracy `eps = 1e-2` on both plateaus.

GSLW Lemma 29 builds the rectangle from two shifted sign approximations and gets degree
`O(log(1/eps) / delta)`; here the polynomial is a *constrained Chebyshev minimax fit* by linear
programming (scipy / HiGHS, untrusted) in the even Chebyshev basis `r = sum_j a_j T_{2j}`.
Two LP formulations are available:

* `--sweep` (pure minimax, one LP per even degree): minimise `eps` subject to
      1 - eps <= r(x) <= 1 - margin   on a Chebyshev grid of [0, t - delta],
      |r(x)| <= eps                   on a Chebyshev grid of [t + delta, 1],
      |r(x)| <= 1 - margin            on a Chebyshev grid of [0, 1]        (admissibility),
  and print the achieved `eps` for every even degree in the range (to choose the degree).
* default (maximal certificate margin at the *stated* accuracy `--eps`): maximise `mu` subject to
      1 - eps + mu <= r(x) <= 1 - mu  on [0, t - delta],
      |r(x)| <= eps - mu              on [t + delta, 1],
      |r(x)| <= 1 - mu                on [0, 1].
  `mu` is then the uniform slack of all three Lean certificates (`rectPoly_abs_bound`,
  `rectPoly_inner_bound`, `rectPoly_outer_bound`): the LP solution is `mu` away from every
  stated bound, so the Bernstein bisection of LeanCert needs only a moderate depth.  (The upper
  bound `r <= 1` is stated without an `eps`, so an LP that merely minimised `eps` would touch `1`
  at x = 0 and the admissibility certificate would have no margin; this replaces the
  `(1 - 1e-8)` rescaling of `SinExample`.)

Evenness is built into the basis (only `T_{2j}`), so the grids live on [0, 1].

Only the Lean literal is consumed downstream; the rounding to `--digits` significant digits is
exact (`Fraction(Decimal(s))`), and the Chebyshev -> monomial conversion uses the integer
recursion `T_{k+1} = 2 x T_k - T_{k-1}` over exact rationals (as `cheb_to_monomial.py`).  The
numerical report (mpmath, untrusted) prints the quantities the Lean certificates state:
  * min / max of r on [0, t - delta] (inner plateau: `1 - eps <= r <= 1`),
  * max |r| on [t + delta, 1] (outer plateau: `|r| <= eps`),
  * max |r| on [-1, 1] and where it is attained (admissibility `|r| <= 1`),
  * the Chebyshev coefficients and the exact l1 norm `sum |c_k|` (the Route A subnormalisation,
    recomputed in Lean by `ChebQC.l1Bound (ChebQC.ofMonomials _)`).

Usage:
  .venv/bin/python rect_cheb.py --sweep                      # eps(d) for d = 20, 22, ..., 40
  .venv/bin/python rect_cheb.py                              # degree 32, max-margin fit at eps = 1e-2 (rectPoly)
  .venv/bin/python rect_cheb.py --degree 40 --eps 5e-3 --name rectPoly40
"""
from __future__ import annotations

import argparse
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


def cheb_grid(lo: float, hi: float, n: int) -> np.ndarray:
    t = np.cos(np.pi * (np.arange(n) + 0.5) / n)
    return (lo + hi) / 2 + (hi - lo) / 2 * t


def even_basis(x: np.ndarray, J: int) -> np.ndarray:
    """Columns `T_{2j}(x)`, j = 0..J."""
    V = np.zeros((len(x), J + 1))
    for j in range(J + 1):
        e = np.zeros(2 * j + 1)
        e[2 * j] = 1
        V[:, j] = npcheb.chebval(x, e)
    return V


def lp_minimax(t: float, delta: float, degree: int, margin: float,
               n_in: int = 800, n_out: int = 1200, n_adm: int = 2000) -> tuple[list[float], float]:
    """Pure minimax: coefficients a_j of T_{2j} and the achieved eps (see module docstring)."""
    J = degree // 2
    Vi = even_basis(cheb_grid(0.0, t - delta, n_in), J)
    Vo = even_basis(cheb_grid(t + delta, 1.0, n_out), J)
    Va = even_basis(cheb_grid(0.0, 1.0, n_adm), J)
    one = lambda V: np.ones((V.shape[0], 1))  # noqa: E731
    zero = lambda V: np.zeros((V.shape[0], 1))  # noqa: E731
    # variables (a_0, ..., a_J, eps); minimise eps
    A_ub = np.vstack([
        np.hstack([-Vi, -one(Vi)]),     # -r - eps <= -1          (r >= 1 - eps, inner)
        np.hstack([Vo, -one(Vo)]),      #  r - eps <= 0           (outer)
        np.hstack([-Vo, -one(Vo)]),     # -r - eps <= 0
        np.hstack([Va, zero(Va)]),      #  r <= 1 - margin        (admissibility, [0, 1])
        np.hstack([-Va, zero(Va)]),     # -r <= 1 - margin
    ])
    b_ub = np.concatenate([-np.ones(n_in), np.zeros(n_out), np.zeros(n_out),
                           (1 - margin) * np.ones(n_adm), (1 - margin) * np.ones(n_adm)])
    cost = np.zeros(J + 2)
    cost[-1] = 1
    res = linprog(cost, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)] * (J + 1) + [(0, None)],
                  method="highs")
    if not res.success:
        raise SystemExit(f"LP failed: {res.message}")
    return [float(v) for v in res.x[: J + 1]], float(res.x[-1])


def lp_max_margin(t: float, delta: float, degree: int, eps: float,
                  n_in: int = 800, n_out: int = 1200, n_adm: int = 2000) -> tuple[list[float], float]:
    """Maximal uniform certificate margin `mu` at the stated accuracy `eps` (see module docstring)."""
    J = degree // 2
    Vi = even_basis(cheb_grid(0.0, t - delta, n_in), J)
    Vo = even_basis(cheb_grid(t + delta, 1.0, n_out), J)
    Va = even_basis(cheb_grid(0.0, 1.0, n_adm), J)
    one = lambda V: np.ones((V.shape[0], 1))  # noqa: E731
    # variables (a_0, ..., a_J, mu); maximise mu = minimise -mu
    A_ub = np.vstack([
        np.hstack([-Vi, one(Vi)]),      # -r + mu <= -(1 - eps)   (r >= 1 - eps + mu, inner)
        np.hstack([Vi, one(Vi)]),       #  r + mu <= 1            (r <= 1 - mu, inner)
        np.hstack([Vo, one(Vo)]),       #  r + mu <= eps          (outer)
        np.hstack([-Vo, one(Vo)]),      # -r + mu <= eps
        np.hstack([Va, one(Va)]),       #  r + mu <= 1            (admissibility, [0, 1])
        np.hstack([-Va, one(Va)]),      # -r + mu <= 1
    ])
    b_ub = np.concatenate([-(1 - eps) * np.ones(n_in), np.ones(n_in),
                           eps * np.ones(n_out), eps * np.ones(n_out),
                           np.ones(n_adm), np.ones(n_adm)])
    cost = np.zeros(J + 2)
    cost[-1] = -1
    res = linprog(cost, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)] * (J + 1) + [(None, None)],
                  method="highs")
    if not res.success:
        raise SystemExit(f"LP failed: {res.message}")
    return [float(v) for v in res.x[: J + 1]], float(res.x[-1])


def report(mono: list[Fraction], cheb: list[Fraction], t: Fraction, delta: Fraction,
           grid: int) -> None:
    print("-- Chebyshev coefficients c_k (exact rationals after rounding):")
    for k, c in enumerate(cheb):
        if c != 0:
            print(f"--   c_{k} = {frac_lean(c)}  ≈ {float(c):.12e}")
    l1 = sum(abs(c) for c in cheb)
    print(f"-- l1 norm sum |c_k| = {frac_lean(l1)} ≈ {float(l1):.15f}")

    lo_in = mp.mpf(t.numerator) / t.denominator - mp.mpf(delta.numerator) / delta.denominator
    lo_out = mp.mpf(t.numerator) / t.denominator + mp.mpf(delta.numerator) / delta.denominator
    r_min, r_max = mp.mpf(10), mp.mpf(-10)
    for i in range(grid + 1):
        x = lo_in * i / grid
        v = horner_mp(mono, x)
        r_min, r_max = min(r_min, v), max(r_max, v)
    o_max = mp.mpf(0)
    for i in range(grid + 1):
        x = lo_out + (1 - lo_out) * i / grid
        o_max = max(o_max, abs(horner_mp(mono, x)))
    p_max, x_max = mp.mpf(0), mp.mpf(0)
    for i in range(grid + 1):
        x = mp.mpf(-1) + mp.mpf(2) * i / grid
        v = abs(horner_mp(mono, x))
        if v > p_max:
            p_max, x_max = v, x
    print(f"-- inner plateau [0, {mp.nstr(lo_in, 4)}] (grid {grid + 1}): "
          f"min r = {mp.nstr(r_min, 12)}  (1 - min r = {mp.nstr(1 - r_min, 6)}),  "
          f"max r = {mp.nstr(r_max, 12)}  (1 - max r = {mp.nstr(1 - r_max, 6)})")
    print(f"-- outer plateau [{mp.nstr(lo_out, 4)}, 1]: max |r| = {mp.nstr(o_max, 6)}")
    print(f"-- max |r(x)| on [-1,1]: {mp.nstr(p_max, 15)} at x = {mp.nstr(x_max, 6)} "
          f"(1 - max |r| = {mp.nstr(1 - p_max, 6)})")
    print(f"-- r(0) = {mp.nstr(horner_mp(mono, mp.mpf(0)), 15)}, "
          f"r({mp.nstr(lo_in, 4)}) = {mp.nstr(horner_mp(mono, lo_in), 15)}, "
          f"r(1/2) = {mp.nstr(horner_mp(mono, mp.mpf(1) / 2), 15)}, "
          f"r({mp.nstr(lo_out, 4)}) = {mp.nstr(horner_mp(mono, lo_out), 15)}, "
          f"r(1) = {mp.nstr(horner_mp(mono, mp.mpf(1)), 15)}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--t", default="1/2", help="threshold t (centre of the transition band)")
    ap.add_argument("--delta", default="1/10", help="half-width of the transition band")
    ap.add_argument("--eps", type=float, default=1e-2, help="stated plateau accuracy eps")
    ap.add_argument("--degree", type=int, default=32, help="even degree of the fit")
    ap.add_argument("--margin", type=float, default=1e-6,
                    help="admissibility margin |r| <= 1 - margin in the --sweep LPs")
    ap.add_argument("--sweep", action="store_true",
                    help="print the minimax eps for every even degree in [--sweep-from, --degree]")
    ap.add_argument("--sweep-from", type=int, default=20)
    ap.add_argument("--digits", type=int, default=30, help="significant digits of the coefficients")
    ap.add_argument("--name", default="rectPoly", help="Lean identifier")
    ap.add_argument("--grid", type=int, default=200000)
    args = ap.parse_args()

    mp.mp.dps = 50
    t = Fraction(args.t)
    delta = Fraction(args.delta)
    tf, df = float(t), float(delta)
    if args.degree % 2 != 0:
        raise SystemExit("degree must be even")

    if args.sweep:
        print(f"-- minimax eps(d) for rect(t = {t}, delta = {delta}), even degree d, "
              f"|r| <= 1 - {args.margin}:")
        for d in range(args.sweep_from, args.degree + 1, 2):
            _, e = lp_minimax(tf, df, d, args.margin)
            print(f"--   d = {d:2d}: eps = {e:.6e}")
        return

    a_mm, eps_mm = lp_minimax(tf, df, args.degree, args.margin)
    a, mu = lp_max_margin(tf, df, args.degree, args.eps)
    if mu <= 0:
        raise SystemExit(f"eps = {args.eps} is not achievable at degree {args.degree} "
                         f"(minimax eps = {eps_mm:.3e}); raise the degree or eps")
    cheb = [Fraction(0)] * (args.degree + 1)
    for j, v in enumerate(a):
        cheb[2 * j] = round_sig(v, args.digits)
    mono = cheb_to_monomial(cheb)

    print(f"-- rect(t = {t}, delta = {delta}): even constrained Chebyshev fit (LP) of degree "
          f"{args.degree}; plateaus [0, {t - delta}] (value 1) and [{t + delta}, 1] (value 0)")
    print(f"-- minimax eps at this degree: {eps_mm:.6e}; stated eps = {args.eps:g}, "
          f"maximal uniform certificate margin mu = {mu:.6e}")
    print(f"-- coefficients rounded to {args.digits} significant digits")
    print(f"def {args.name} : PolyQ :=")
    print("  [")
    for i, q in enumerate(mono):
        sep = "," if i + 1 < len(mono) else ""
        print(f"    {frac_lean(q)}{sep}  -- x^{i} ≈ {float(q):.6e}")
    print("  ]")
    report(mono, cheb, t, delta, args.grid)


if __name__ == "__main__":
    main()
