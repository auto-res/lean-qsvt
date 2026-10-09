#!/usr/bin/env python
"""
cos_cheb.py -- Chebyshev (Jacobi-Anger) approximation of cos(t x) on [-1, 1] as an exact rational
monomial coefficient list for `QSVT.Certificate.PolyQ` (APP-4 lite, Hamiltonian simulation, real
part of e^{-itx}).

    cos(t x) = J_0(t) + 2 sum_{k>=1} (-1)^k J_{2k}(t) T_{2k}(x)        (Jacobi-Anger)

The series is truncated at an even degree d chosen so that the tail 2 sum_{2k>d} |J_{2k}(t)| is
below `--tail` (default 1e-7); the Bessel values are computed with mpmath at 50 digits and rounded
to `--digits` significant decimal digits (default 30), read back as exact `Fraction`s, and the sum
c_k T_k is expanded in the monomial basis with the integer recursion T_{k+1} = 2 x T_k - T_{k-1}
(exact rationals; the same conversion as `cheb_to_monomial.py`).  Only the Lean literal is
consumed downstream; everything else printed is an untrusted numerical report:

  * max |p(x) - cos(t x)| on a fine grid of [-1, 1] (the quantity `eps` certifies),
  * max |p(x)| on [-1, 1] and the value p(0) = 1 - (truncation tail), for the admissibility bound,
  * the Chebyshev coefficients and the l1 norm sum |c_k| (the Route A subnormalisation).

With `--shift s` the constant coefficient is lowered by s (p(0) = 1 - tail - s): this gives the
`p <= 1` certificate a margin of about s at x = 0 at the price of s in the approximation error.

With `--sin` the odd part is produced instead (APP-4, imaginary part of e^{-itx}):

    sin(t x) = 2 sum_{k>=0} (-1)^k J_{2k+1}(t) T_{2k+1}(x)        (Jacobi-Anger, odd part)

truncated at an odd degree d with tail 2 sum_{2k+1>d} |J_{2k+1}(t)| below `--tail`.  Since
max |sin(t x)| = 1 is attained inside [-1, 1] (for t >= pi/2) the truncation can overshoot 1 by
about the tail, so `--scale s` multiplies every Chebyshev coefficient by (1 - s) before the
rounding: the `|p| <= 1` certificate then has a margin of about s at the price of s in the
approximation error (the odd polynomial has no constant term, so `--shift` does not apply).

Usage:
  .venv/bin/python cos_cheb.py --t 2 --name cos2Poly
  .venv/bin/python cos_cheb.py --t 2 --degree 10 --shift 5e-7
  .venv/bin/python cos_cheb.py --t 2 --sin --name sin2Poly --scale 1e-8
"""
from __future__ import annotations

import argparse
from decimal import Decimal
from fractions import Fraction

import mpmath as mp


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


def round_sig(x: mp.mpf, digits: int) -> Fraction:
    """`x` rounded to `digits` significant decimal digits, as an exact rational."""
    s = mp.nstr(x, digits, strip_zeros=False)
    return Fraction(Decimal(s))


def horner_mp(a: list[Fraction], x: mp.mpf) -> mp.mpf:
    acc = mp.mpf(0)
    for q in reversed(a):
        acc = mp.mpf(q.numerator) / q.denominator + x * acc
    return acc


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--t", type=float, default=2.0, help="evolution time t in cos(t x)")
    ap.add_argument("--degree", type=int, default=None, help="even truncation degree (default: auto)")
    ap.add_argument("--tail", type=float, default=1e-7, help="tail bound for the automatic degree")
    ap.add_argument("--digits", type=int, default=30, help="significant digits of the coefficients")
    ap.add_argument("--shift", type=float, default=0.0, help="lower the constant term by this much")
    ap.add_argument("--sin", action="store_true", help="approximate sin(t x) (odd part) instead")
    ap.add_argument("--scale", type=float, default=0.0,
                    help="multiply every coefficient by (1 - scale) before rounding")
    ap.add_argument("--name", default=None, help="Lean identifier (default cos2Poly / sin2Poly)")
    ap.add_argument("--grid", type=int, default=200000)
    args = ap.parse_args()

    mp.mp.dps = 50
    t = mp.mpf(args.t)
    odd = args.sin
    fname = "sin" if odd else "cos"
    target = mp.sin if odd else mp.cos
    name = args.name or f"{fname}2Poly"
    parity = 1 if odd else 0

    # cos: c_{2k} = (-1)^k 2 J_{2k}(t) (k >= 1), c_0 = J_0(t); odd ones vanish.
    # sin: c_{2k+1} = (-1)^k 2 J_{2k+1}(t); even ones vanish.
    def cheb_coeff(k: int) -> mp.mpf:
        if k % 2 != parity:
            return mp.mpf(0)
        j = k // 2
        if not odd and j == 0:
            return mp.besselj(0, t)
        return 2 * (-1) ** j * mp.besselj(k, t)

    def tail_from(d: int) -> mp.mpf:
        return sum(2 * abs(mp.besselj(k, t)) for k in range(d + 2, d + 60, 2))

    if args.degree is None:
        d = parity
        while tail_from(d) >= args.tail:
            d += 2
    else:
        d = args.degree
        if d % 2 != parity:
            raise SystemExit(f"degree must be {'odd' if odd else 'even'}")
    tail = tail_from(d)

    # The scale factor is applied before the rounding, so that the coefficients keep `--digits`
    # significant digits (an exact rational factor would lengthen every denominator).
    factor = 1 - mp.mpf(repr(args.scale)) if args.scale else mp.mpf(1)
    cheb_exact = [factor * cheb_coeff(k) for k in range(d + 1)]
    cheb = [round_sig(c, args.digits) if c != 0 else Fraction(0) for c in cheb_exact]
    shift = Fraction(Decimal(repr(args.shift))) if args.shift else Fraction(0)
    cheb[0] -= shift
    mono = cheb_to_monomial(cheb)

    print(f"-- {fname}({args.t} x) on [-1, 1]: Jacobi-Anger truncated at degree {d}")
    print(f"-- truncation tail 2 sum_{{k>{d}}} |J_k({args.t})| = {mp.nstr(tail, 6)}; "
          f"coefficients rounded to {args.digits} significant digits; shift of a_0 = {args.shift}; "
          f"scale factor 1 - {args.scale}")
    print(f"def {name} : PolyQ :=")
    print("  [")
    for i, q in enumerate(mono):
        sep = "," if i + 1 < len(mono) else ""
        print(f"    {frac_lean(q)}{sep}  -- x^{i} ≈ {float(q):.6e}")
    print("  ]")

    # Chebyshev view (what `ChebQC.ofMonomials` will recompute inside Lean).
    print("-- Chebyshev coefficients c_k (exact rationals after rounding):")
    for k, c in enumerate(cheb):
        if c != 0:
            print(f"--   c_{k} = {frac_lean(c)}  ≈ {float(c):.12e}")
    l1 = sum(abs(c) for c in cheb)
    print(f"-- l1 norm sum |c_k| = {frac_lean(l1)} ≈ {float(l1):.15f}")

    # Numerical report (untrusted).
    n = args.grid
    err_max = mp.mpf(0)
    p_max = mp.mpf(0)
    x_max = mp.mpf(0)
    for i in range(n + 1):
        x = mp.mpf(-1) + mp.mpf(2) * i / n
        p = horner_mp(mono, x)
        err_max = max(err_max, abs(p - target(t * x)))
        if abs(p) > p_max:
            p_max, x_max = abs(p), x
    p0 = horner_mp(mono, mp.mpf(0))
    print(f"-- max |p(x) - {fname}({args.t} x)| on [-1,1] (grid {n + 1}): {mp.nstr(err_max, 6)}")
    print(f"-- max |p(x)| on [-1,1]: {mp.nstr(p_max, 20)} at x = {mp.nstr(x_max, 8)} "
          f"(1 - max |p| = {mp.nstr(1 - p_max, 6)})")
    print(f"-- p(0) = {mp.nstr(p0, 20)}  (1 - p(0) = {mp.nstr(1 - p0, 6)})")
    print(f"-- p(1) = {mp.nstr(horner_mp(mono, mp.mpf(1)), 20)}, "
          f"{fname}({args.t}) = {mp.nstr(target(t), 20)}")


if __name__ == "__main__":
    main()
