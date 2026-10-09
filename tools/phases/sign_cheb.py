#!/usr/bin/env python
"""
sign_cheb.py -- an odd polynomial approximation of the sign function with a prescribed gap,

    p(x) ≈ c · sign(x)   on [-1, -delta] ∪ [delta, 1],     |p(x)| <= 1  on [-1, 1],

as a solver target (Chebyshev coefficients, exact decimal expansions of doubles) plus the
reflection-convention QSP phases for it (QSPPACK / pyqsp), in the same JSON layout as
`solver_examples.py` writes for `sign21`.  Default: `delta = 1/10`, odd degree `d = 35`
(CERT-B, `QSVT.Certificate.SignD01` / `SignD01Phases`; the input of the fixed-point amplitude
amplification example composed with the matrix-inversion example).

The polynomial is a *constrained minimax fit* by linear programming (scipy / HiGHS, untrusted)
in the odd Chebyshev basis `p = sum_j a_j T_{2j+1}` (oddness built into the basis, grids on
[0, 1]):

    maximise  L   subject to   p(x) >= L           on a Chebyshev grid of [delta, 1]   (plateau)
                               |p(x)| <= 1 - mu    on a Chebyshev grid of [0, 1]       (admissibility)

`L` is the best plateau lower bound achievable at this degree once the maximum of `|p|` is
kept `mu` below `1` (the margin `mu`, default `1e-3`, is what the admissibility certificate
`|p| <= 1` is slack by, and keeps the phase solvers away from the `max |f| = 1` boundary).  The
optimum equioscillates: `p` touches `1 - mu` and `L` alternately on `[delta, 1]`, so the plateau
is `[L, 1 - mu]`, the natural plateau value is the centre `c = (L + 1 - mu) / 2` and the ripple
is `eps_p = (1 - mu - L) / 2`.  Unlike pyqsp's `PolySign` (Chebyshev interpolant of `erf(kappa x)`
rescaled into the unit disc, used for `sign21`) this maximises `c - eps_p` directly.

For the default run (degree 35) the plateau is `[0.976107, 0.999001]`; the Lean certificates of
`QSVT.Certificate.SignD01` state the slightly wider `[0.9755, 0.9995]` (`c = 0.9875`,
`eps_p = 0.012`), whose `5e-4` margins LeanCert's Bernstein bisection certifies at depth 8.

The LP coefficients are rounded to doubles, so every coefficient is an exact dyadic rational; the
JSON field `target_chebyshev_coeffs` holds their exact decimal expansions (as for `sign21`), and
`cheb_to_monomial.py` converts them exactly to the monomial `PolyQ` literal.  The numerical report
(mpmath on the exact monomial list, numpy on the Chebyshev form; untrusted) prints the quantities
the Lean certificates state: `max |p|` on [-1, 1], `min p` / `max p` on `[delta, 1]`, `p(delta)`,
`p(1)`, and the suggested `(c, eps_p)`.

The phases are computed with qsppack (`solve`, FPI then Newton, `targetPre`, full symmetric
phases) and pyqsp (`sym_qsp`), converted to the R convention (`qsp_conventions.W_to_R`, reduced
mod 2 pi) and verified with `seqR` on a grid (max error over `--grid` points); the JSON files are
`examples/sign_d01_qsppack.json`, `examples/sign_d01_pyqsp_symqsp.json`.

Usage:
  .venv/bin/python sign_cheb.py --sweep                  # L(d) for d = 21, 23, ..., 41
  .venv/bin/python sign_cheb.py                          # degree 35, mu = 1e-3, write the JSONs
  .venv/bin/python sign_cheb.py --degree 41 --mu 1e-3 --name sign_d01_41 --no-phases
"""
from __future__ import annotations

import argparse
import contextlib
import io
import os
import sys
import warnings
from fractions import Fraction

import mpmath as mp
import numpy as np
from numpy.polynomial import chebyshev as npcheb
from scipy.optimize import linprog

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cheb_to_monomial import cheb_to_monomial, frac_lean, strip_trailing_zeros  # noqa: E402
from qsp_conventions import PI  # noqa: E402
from solver_examples import dump, exact_decimal, verify_and_pack  # noqa: E402

warnings.filterwarnings("ignore")


# ----------------------------------------------------------------------------
# LP
# ----------------------------------------------------------------------------


def cheb_grid(lo: float, hi: float, n: int) -> np.ndarray:
    t = np.cos(np.pi * (np.arange(n) + 0.5) / n)
    return (lo + hi) / 2 + (hi - lo) / 2 * t


def odd_basis(x: np.ndarray, J: int) -> np.ndarray:
    """Columns `T_{2j+1}(x)`, j = 0..J."""
    V = np.zeros((len(x), J + 1))
    for j in range(J + 1):
        e = np.zeros(2 * j + 2)
        e[2 * j + 1] = 1
        V[:, j] = npcheb.chebval(x, e)
    return V


def lp_sign(delta: float, degree: int, mu: float, n_pl: int = 1500, n_adm: int = 3000) -> tuple[list[float], float]:
    """Coefficients a_j of T_{2j+1} and the plateau lower bound L (see module docstring)."""
    if degree % 2 != 1:
        raise SystemExit("degree must be odd")
    J = (degree - 1) // 2
    Vp = odd_basis(cheb_grid(delta, 1.0, n_pl), J)
    Va = odd_basis(cheb_grid(0.0, 1.0, n_adm), J)
    one = np.ones((n_pl, 1))
    zero = np.zeros((n_adm, 1))
    # variables (a_0, ..., a_J, L); maximise L = minimise -L
    A_ub = np.vstack([
        np.hstack([-Vp, one]),       # -p + L <= 0        (p >= L on the plateau)
        np.hstack([Va, zero]),       #  p <= 1 - mu       (admissibility on [0, 1])
        np.hstack([-Va, zero]),      # -p <= 1 - mu
    ])
    b_ub = np.concatenate([np.zeros(n_pl), (1 - mu) * np.ones(n_adm), (1 - mu) * np.ones(n_adm)])
    cost = np.zeros(J + 2)
    cost[-1] = -1
    res = linprog(cost, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)] * (J + 2), method="highs")
    if not res.success:
        raise SystemExit(f"LP failed: {res.message}")
    return [float(v) for v in res.x[: J + 1]], float(res.x[-1])


# ----------------------------------------------------------------------------
# report
# ----------------------------------------------------------------------------


def horner_mp(a: list[Fraction], x: mp.mpf) -> mp.mpf:
    acc = mp.mpf(0)
    for q in reversed(a):
        acc = mp.mpf(q.numerator) / q.denominator + x * acc
    return acc


def report(cheb: list[float], mono: list[Fraction], delta: Fraction, L: float, mu: float,
           grid_np: int, grid_mp: int) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """Print the numbers the Lean certificates state; return (max |p| on [-1,1], min p, max p on [delta, 1])."""
    d = len(cheb) - 1
    df = float(delta)
    print(f"-- odd degree {d}, delta = {delta}, LP plateau lower bound L = {L:.12f}, margin mu = {mu:g}")
    print("-- Chebyshev coefficients (doubles; exact decimal expansions in the JSON):")
    for k, c in enumerate(cheb):
        if c != 0:
            print(f"--   c_{k} = {c!r}")
    l1 = sum(abs(Fraction(c)) for c in cheb)
    print(f"-- l1 norm sum |c_k| = {float(l1):.15f}")
    # numpy on the Chebyshev form (stable), fine grid
    xs = np.linspace(-1.0, 1.0, grid_np + 1)
    ps = npcheb.chebval(xs, cheb)
    i_max = int(np.argmax(np.abs(ps)))
    sel = xs >= df
    print(f"-- numpy (Chebyshev form, grid {grid_np + 1}): max |p| = {abs(ps[i_max]):.15f} at x = {xs[i_max]:.6f}; "
          f"on [{df}, 1]: min p = {ps[sel].min():.15f}, max p = {ps[sel].max():.15f}")
    # mpmath on the exact monomial list (what Lean certifies), coarser grid
    p_max, x_max = mp.mpf(0), mp.mpf(0)
    for i in range(grid_mp + 1):
        x = mp.mpf(-1) + mp.mpf(2) * i / grid_mp
        v = abs(horner_mp(mono, x))
        if v > p_max:
            p_max, x_max = v, x
    lo = mp.mpf(delta.numerator) / delta.denominator
    pl_min, pl_max = mp.mpf(10), mp.mpf(-10)
    for i in range(grid_mp + 1):
        x = lo + (1 - lo) * i / grid_mp
        v = horner_mp(mono, x)
        pl_min, pl_max = min(pl_min, v), max(pl_max, v)
    # refine the extrema found by numpy with mpmath (golden-section on a small bracket)
    h = 2.0 / grid_np
    def refine(x0: float, sign: int) -> mp.mpf:
        f = lambda t: sign * horner_mp(mono, mp.mpf(t))  # noqa: E731
        a, b = mp.mpf(max(-1.0, x0 - 2 * h)), mp.mpf(min(1.0, x0 + 2 * h))
        gr = (mp.sqrt(5) - 1) / 2
        c1, d1 = b - gr * (b - a), a + gr * (b - a)
        for _ in range(60):
            if f(c1) > f(d1):
                b, d1 = d1, c1
                c1 = b - gr * (b - a)
            else:
                a, c1 = c1, d1
                d1 = a + gr * (b - a)
        return sign * f((a + b) / 2)
    pm_ref = abs(refine(float(xs[i_max]), 1 if ps[i_max] > 0 else -1))
    j_min = int(np.argmin(np.where(sel, ps, np.inf)))
    j_max = int(np.argmax(np.where(sel, ps, -np.inf)))
    plmin_ref = refine(float(xs[j_min]), -1)
    plmax_ref = refine(float(xs[j_max]), 1)
    p_max = max(p_max, pm_ref)
    pl_min = min(pl_min, plmin_ref)
    pl_max = max(pl_max, plmax_ref)
    print(f"-- mpmath (exact monomial list, grid {grid_mp + 1} + refined extrema):")
    print(f"--   max |p| on [-1, 1] = {mp.nstr(p_max, 15)} (1 - max |p| = {mp.nstr(1 - p_max, 6)}), near x = {mp.nstr(x_max, 6)}")
    print(f"--   plateau [{delta}, 1]: min p = {mp.nstr(pl_min, 15)}, max p = {mp.nstr(pl_max, 15)}")
    print(f"--   p({delta}) = {mp.nstr(horner_mp(mono, lo), 15)}, p(1) = {mp.nstr(horner_mp(mono, mp.mpf(1)), 15)}, "
          f"p(1/2) = {mp.nstr(horner_mp(mono, mp.mpf(1) / 2), 15)}")
    c = (pl_min + pl_max) / 2
    eps_p = (pl_max - pl_min) / 2
    print(f"-- suggested plateau centre c = {mp.nstr(c, 12)}, ripple eps_p = {mp.nstr(eps_p, 6)} "
          f"(certify c - eps_p' <= p <= c + eps_p' with eps_p' slightly above eps_p)")
    return p_max, pl_min, pl_max


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--delta", default="1/10", help="half-gap: the plateaus are [delta, 1] and [-1, -delta]")
    ap.add_argument("--degree", type=int, default=35, help="odd degree of the fit")
    ap.add_argument("--mu", type=float, default=1e-3, help="admissibility margin |p| <= 1 - mu")
    ap.add_argument("--sweep", action="store_true", help="print L(d) for odd d in [--sweep-from, --degree]")
    ap.add_argument("--sweep-from", type=int, default=21)
    ap.add_argument("--name", default="sign_d01", help="JSON base name (<name>_<tool>.json)")
    ap.add_argument("--lean-name", default="signD01", help="Lean identifier of the PolyQ literal")
    ap.add_argument("--outdir", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "examples"))
    ap.add_argument("--grid", type=int, default=2001, help="verification grid for seqR")
    ap.add_argument("--grid-np", type=int, default=2_000_000)
    ap.add_argument("--grid-mp", type=int, default=20_000)
    ap.add_argument("--no-phases", action="store_true", help="only the polynomial and the report")
    ap.add_argument("--lean-out", default=None, help="write the Lean PolyQ literal to this file")
    args = ap.parse_args(argv)

    mp.mp.dps = 60
    delta = Fraction(args.delta)
    df = float(delta)

    if args.sweep:
        print(f"-- plateau lower bound L(d) for sign on [{delta}, 1], |p| <= 1 - {args.mu:g}, odd degree d:")
        for d in range(args.sweep_from, args.degree + 1, 2):
            _, L = lp_sign(df, d, args.mu)
            c = (L + 1 - args.mu) / 2
            print(f"--   d = {d:2d}: L = {L:.6f}   (c = {c:.6f}, eps_p = {1 - args.mu - c:.6f})")
        return 0

    a, L = lp_sign(df, args.degree, args.mu)
    cheb = [0.0] * (args.degree + 1)
    for j, v in enumerate(a):
        cheb[2 * j + 1] = float(v)  # doubles: exact dyadic rationals
    cheb_fr = [Fraction(c) for c in cheb]
    mono = strip_trailing_zeros(cheb_to_monomial(cheb_fr))

    print(f"def {args.lean_name} : PolyQ :=")
    print("  [")
    for i, q in enumerate(mono):
        sep = "," if i + 1 < len(mono) else ""
        print(f"    {frac_lean(q)}{sep}  -- x^{i} ≈ {float(q):.6e}")
    print("  ]")
    if args.lean_out:
        with open(args.lean_out, "w") as fh:
            fh.write(f"def {args.lean_name} : PolyQ :=\n  [")
            fh.write(",\n   ".join(frac_lean(q) for q in mono))
            fh.write("]\n")
    print(f"-- Chebyshev list (Lean `List ℚ`, exact dyadics):")
    print("  [" + ", ".join(frac_lean(c) for c in cheb_fr) + "]")
    p_max, pl_min, pl_max = report(cheb, mono, delta, L, args.mu, args.grid_np, args.grid_mp)
    if p_max >= 1:
        raise SystemExit("max |p| >= 1: increase mu")

    if args.no_phases:
        return 0

    os.makedirs(args.outdir, exist_ok=True)
    xs = np.linspace(-1, 1, args.grid)
    chebarr = np.asarray(cheb, dtype=float)
    desc = (f"odd degree-{args.degree} Chebyshev approximation of sign(x) with gap delta = {delta}: constrained "
            f"minimax LP (tools/phases/sign_cheb.py) maximising the plateau lower bound on [{delta}, 1] subject to "
            f"|p| <= 1 - {args.mu:g} on [-1, 1]; plateau [{mp.nstr(pl_min, 12)}, {mp.nstr(pl_max, 12)}], "
            f"plateau centre c = {mp.nstr((pl_min + pl_max) / 2, 12)}, ripple {mp.nstr((pl_max - pl_min) / 2, 6)}, "
            f"max |p| = {mp.nstr(p_max, 12)}")
    extra_common = {"delta": str(delta), "lp_margin_mu": args.mu, "lp_plateau_lower_bound_L": L,
                    "plateau_min": mp.nstr(pl_min, 20), "plateau_max": mp.nstr(pl_max, 20),
                    "max_abs_p": mp.nstr(p_max, 20)}
    parity = args.degree % 2

    try:
        import qsppack

        qsppack_ver = getattr(qsppack, "__version__", "0.4.0 (pip)")
        reduced = chebarr[parity::2]
        done = False
        for method in ("FPI", "Newton"):
            if done:
                break
            try:
                opts = {"method": method, "targetPre": True, "typePhi": "full", "criteria": 1e-13, "maxiter": 5000}
                with contextlib.redirect_stdout(io.StringIO()):  # FPI prints every iteration
                    phi, out = qsppack.solve(reduced, parity, opts)
                phi = np.asarray(phi, dtype=float)
                rec = verify_and_pack(
                    f"{args.name}_qsppack", f"qsppack {qsppack_ver}, solve(reduced_cheb, parity, {opts})",
                    "U = e^{i phi_0 Z} prod W(x) e^{i phi_j Z}; symmetric full phases (pi/4 already added at both ends); Re U00 = f",
                    phi, chebarr, desc, xs,
                    extra={**extra_common,
                           "solver_info": {k: (float(v) if isinstance(v, (int, float, np.floating)) else str(v))
                                           for k, v in out.items()}})
                if rec["errors"]["max|Re seqR00 - f|"] > 1e-9:
                    print(f"qsppack {method}: residual too large, trying next method")
                    continue
                dump(rec, args.outdir, f"{args.name}_qsppack.json")
                done = True
            except Exception as e:
                print(f"qsppack {method} failed: {type(e).__name__}: {e}")
    except Exception as e:  # pragma: no cover
        print("qsppack unavailable:", e)

    try:
        import pyqsp
        from pyqsp.angle_sequence import QuantumSignalProcessingPhases as QSPP

        pyqsp_ver = getattr(pyqsp, "__version__", "0.2.0 (pip)")
        try:
            full, reduced_p, par = QSPP(list(chebarr), method="sym_qsp", chebyshev_basis=True)
            full = np.asarray(full, dtype=float)
            shifted = full.copy()
            shifted[0] -= PI / 4
            shifted[-1] -= PI / 4
            rec = verify_and_pack(
                f"{args.name}_pyqsp_symqsp", f"pyqsp {pyqsp_ver}, QuantumSignalProcessingPhases(method='sym_qsp', chebyshev_basis=True)",
                "U = e^{i phi_0 Z} prod W(x) e^{i phi_j Z}; symmetric full phases with Im U00 = f.  "
                "Stored W phases = full phases with pi/4 SUBTRACTED at both ends so that Re U00 = f.",
                shifted, chebarr, desc, xs,
                extra={**extra_common,
                       "solver_raw_full_phases_decimal": [exact_decimal(p) for p in full],
                       "solver_reduced_phases_decimal": [exact_decimal(p) for p in np.asarray(reduced_p, float)],
                       "solver_parity": int(par)})
            dump(rec, args.outdir, f"{args.name}_pyqsp_symqsp.json")
        except Exception as e:
            print(f"pyqsp sym_qsp failed: {type(e).__name__}: {e}")
    except Exception as e:  # pragma: no cover
        print("pyqsp unavailable:", e)
    return 0


if __name__ == "__main__":
    sys.exit(main())
