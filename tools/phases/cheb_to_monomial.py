#!/usr/bin/env python
"""
cheb_to_monomial.py -- exact Chebyshev -> monomial conversion of a target polynomial, as a Lean
`List ℚ` literal for `QSVT.Certificate.PolyQ` (Route B, CERT-B part 1).

Input: one of the solver JSON files in tools/phases/examples/ (field `target_chebyshev_coeffs`:
exact decimal expansions of doubles, index k = coefficient of T_k).  The decimals are read as exact
rationals (`Fraction(Decimal(s))`), and `sum_k c_k T_k` is expanded in the monomial basis with the
integer recursion T_{k+1} = 2 x T_k - T_{k-1}, so the output coefficients are exact rationals (dyadic
when the input is).

Output (stdout, or `--lean-out FILE`): the Lean literal `[a_0, a_1, ...]` (index = degree) plus,
with `--analyze`, a numeric report (pure Python floats, untrusted) of
  * max |p| on [-1, 1] (for the global bound), and
  * for a few thresholds delta: min / max of p on [delta, 1] and the deviation from the plateau
    value c (the rescaling constant in the JSON `target` field, if present, else the value p(1)),
to pick the (delta, eps) pair that the Lean certificate states.

Usage:
  python cheb_to_monomial.py examples/sign21_qsppack.json --analyze
  python cheb_to_monomial.py examples/sign21_qsppack.json --lean-out /dev/stdout --name sign21
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from decimal import Decimal
from fractions import Fraction


def cheb_to_monomial(c: list[Fraction]) -> list[Fraction]:
    """Exact monomial coefficients of sum_k c_k T_k (index = degree)."""
    n = len(c)
    if n == 0:
        return []
    out = [Fraction(0)] * n
    # T_{k-1}, T_k as integer monomial coefficient lists of length n
    t_prev = [0] * n
    t_cur = [0] * n
    t_prev[0] = 1  # T_0
    if n > 1:
        t_cur[1] = 1  # T_1
    for k in range(n):
        tk = t_prev if k == 0 else t_cur
        if c[k] != 0:
            for i in range(n):
                if tk[i]:
                    out[i] += c[k] * tk[i]
        if k >= 1 and k + 1 < n:
            # T_{k+1} = 2 x T_k - T_{k-1}
            t_next = [0] * n
            for i in range(n - 1):
                t_next[i + 1] += 2 * t_cur[i]
            for i in range(n):
                t_next[i] -= t_prev[i]
            t_prev, t_cur = t_cur, t_next
    return out


def strip_trailing_zeros(a: list[Fraction]) -> list[Fraction]:
    while a and a[-1] == 0:
        a = a[:-1]
    return a


def frac_lean(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    if q.numerator < 0:
        return f"-{-q.numerator} / {q.denominator}"
    return f"{q.numerator} / {q.denominator}"


def horner(a: list[Fraction], x: float) -> float:
    acc = 0.0
    for q in reversed(a):
        acc = float(q) + x * acc
    return acc


def analyze(a: list[Fraction], plateau: Fraction | None, grid: int) -> None:
    xs = [-1.0 + 2.0 * i / grid for i in range(grid + 1)]
    ps = [horner(a, x) for x in xs]
    pmax = max(abs(p) for p in ps)
    print(f"# degree {len(a) - 1}, max|p| on [-1,1] (grid {grid + 1}): {pmax:.15f}")
    cmax = max(abs(q) for q in a)
    print(f"# max |monomial coefficient|: {float(cmax):.6e}; sum |coeff|: {float(sum(abs(q) for q in a)):.6e}")
    c = float(plateau) if plateau is not None else horner(a, 1.0)
    print(f"# plateau value c = {c:.16f}")
    for delta in [0.05, 0.08, 0.1, 0.12, 0.15, 0.2, 0.25, 0.3]:
        sel = [p for x, p in zip(xs, ps) if x >= delta]
        lo, hi = min(sel), max(sel)
        dev = max(abs(lo - c), abs(hi - c))
        print(f"# delta={delta:<5}: min p={lo:.12f}  max p={hi:.12f}  max|p-c|={dev:.3e}  1-min={1 - lo:.6f}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("json", help="solver JSON with Chebyshev coefficients")
    ap.add_argument("--key", default="target_chebyshev_coeffs")
    ap.add_argument("--name", default="p", help="Lean identifier")
    ap.add_argument("--lean-out", default=None, help="write the Lean literal (def) to this file")
    ap.add_argument("--analyze", action="store_true")
    ap.add_argument("--grid", type=int, default=20000)
    args = ap.parse_args()

    with open(args.json) as fh:
        data = json.load(fh)
    cheb = [Fraction(Decimal(s)) for s in data[args.key]]
    mono = strip_trailing_zeros(cheb_to_monomial(cheb))

    plateau = None
    m = re.search(r"rescaled by ([0-9.]+)", str(data.get("target", "")))
    if m:
        plateau = Fraction(Decimal(m.group(1)))

    lines = [f"def {args.name} : PolyQ :=", "  ["]
    for i, q in enumerate(mono):
        sep = "," if i + 1 < len(mono) else ""
        lines.append(f"    {frac_lean(q)}{sep}  -- x^{i} ≈ {float(q):.6e}")
    lines.append("  ]")
    text = "\n".join(lines) + "\n"
    if args.lean_out:
        with open(args.lean_out, "w") as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)
    if plateau is not None:
        print(f"-- plateau constant (exact rational of the decimal): {frac_lean(plateau)}")
    if args.analyze:
        analyze(mono, plateau, args.grid)


if __name__ == "__main__":
    main()
