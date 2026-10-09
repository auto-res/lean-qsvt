#!/usr/bin/env python
"""
solver_examples.py -- compute QSP phases with external solvers (pyqsp, qsppack), convert them to
the lean-qsvt reflection convention (seqR, GSLW Def 7 / Cor 8) and verify with seqR on a grid.

Solver conventions (all use the GSLW Thm 3 "W" sequence U = e^{i phi_0 Z} prod_{j=1}^d W(x) e^{i phi_j Z},
W = [[x, i s],[i s, x]], phases listed as [phi_0, ..., phi_d]):

  pyqsp  method="laurent", signal_operator="Wx", measurement="x":
         <+|U|+> = Re P(x) + i s Re Q(x) = f(x), so Re P = f and Re Q = 0.  Phases are NOT symmetric
         (phi_0 and phi_d differ by pi/2).  Target is scaled by `suc` and "capitalized" by `eps`.
  pyqsp  method="sym_qsp", chebyshev_basis=True (Dong-Meng-Whaley-Lin symmetric phases):
         returns (full, reduced, parity); full phases symmetric, Im P(x) = Im U[0,0] = f(x).
         Subtracting pi/4 from phi_0 and phi_d gives Re P = f (U -> e^{-i pi/4 Z} U e^{-i pi/4 Z}, U00 -> -i U00).
  qsppack solve(reduced_cheb_coefs, parity, {"targetPre": True, "typePhi": "full"}):
         full symmetric phases that already include +pi/4 at both ends; Re P(x) = Re U[0,0] = f(x).

Output: tools/phases/examples/*.json with phases as exact decimal expansions of the doubles (>= 30 digits)
and as dyadic rationals, plus metadata and verification errors.

Usage: python solver_examples.py [--outdir DIR] [--grid N]
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import warnings
from decimal import Decimal
from fractions import Fraction

import numpy as np
from numpy.polynomial import chebyshev as C

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qsp_conventions import PI, W_to_R, cheb_phases_R, seqR, seqW  # noqa: E402

warnings.filterwarnings("ignore")


# ----------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------


def exact_decimal(x: float) -> str:
    """Exact decimal expansion of the double x (a dyadic rational), >= 30 significant digits."""
    d = Decimal(float(x))
    s = format(d, "f")
    digits = len(s.replace("-", "").replace(".", "").lstrip("0"))
    if digits < 30:  # pad with zeros: the value is exact anyway
        if "." not in s:
            s += "."
        s += "0" * (30 - digits)
    return s


def dyadic(x: float) -> dict:
    n, d = float(x).as_integer_ratio()
    return {"num": n, "den_log2": d.bit_length() - 1}


def reduce_angle(phi: float) -> float:
    """Reduce into (-pi, pi]; seqR/seqW are 2pi-periodic in every phase."""
    r = math.remainder(phi, 2 * PI)
    return r if r > -PI else r + 2 * PI


def tl_R(phR, xs):
    return np.array([seqR(phR, float(x))[0, 0] for x in xs])


def tl_W(phW, xs):
    return np.array([seqW(phW, float(x))[0, 0] for x in xs])


def verify_and_pack(name: str, tool: str, convention: str, phW, target_cheb, target_desc: str, xs, extra=None) -> dict:
    phW = [float(p) for p in phW]
    d = len(phW) - 1
    phR_raw = W_to_R(phW)
    phR = [reduce_angle(p) for p in phR_raw]
    f = C.chebval(xs, target_cheb)
    uW = tl_W(phW, xs)
    uR = tl_R(phR, xs)
    uR_raw = tl_R(phR_raw, xs)
    err = {
        "max|seqW00 - seqR00|  (conversion exactness)": float(np.abs(uW - uR).max()),
        "max|seqR00(reduced) - seqR00(raw)|": float(np.abs(uR - uR_raw).max()),
        "max|Re seqR00 - f|": float(np.abs(uR.real - f).max()),
        "max|Im seqR00|": float(np.abs(uR.imag).max()),
        "max|seqR00| (must be <= 1)": float(np.abs(uR).max()),
        "max|phi_j - phi_{d-j}| (W phases symmetric?)": float(np.abs(np.array(phW) - np.array(phW)[::-1]).max()),
    }
    rec = {
        "name": name,
        "tool": tool,
        "solver_convention": convention,
        "degree": d,
        "parity": d % 2,
        "target": target_desc,
        "target_chebyshev_coeffs": [exact_decimal(c) for c in target_cheb],
        "R_convention": "seqR([phi_1..phi_d], x) = prod_j diag(e^{i phi_j}, e^{-i phi_j}) [[x, s],[s, -x]], s = sqrt(1-x^2); "
                        "top-left entry = P(x) with Re P = f.  Lean: seqR (phi::Ph) = phaseZ phi * Rref x * seqR Ph.",
        "W_to_R_map": "phi_1 = phi'_0 + phi'_d + (d-1) pi/2, phi_j = phi'_{j-1} - pi/2 (2<=j<=d); phi_1 then reduced mod 2 pi",
        "phases_W_decimal": [exact_decimal(p) for p in phW],
        "phases_R_decimal": [exact_decimal(p) for p in phR],
        "phases_R_dyadic": [dyadic(p) for p in phR],
        "grid_points": int(len(xs)),
        "errors": err,
    }
    if extra:
        rec.update(extra)
    print(f"[{name}] d={d}")
    for k, v in err.items():
        print(f"   {k}: {v:.3e}")
    return rec


def dump(rec: dict, outdir: str, fname: str):
    path = os.path.join(outdir, fname)
    with open(path, "w") as fh:
        json.dump(rec, fh, indent=1)
    print("   ->", path)


# ----------------------------------------------------------------------------
# targets
# ----------------------------------------------------------------------------


def target_T5():
    return [0.0, 0.0, 0.0, 0.0, 0.0, 1.0], "T_5(x) = cos(5 arccos x)"


def target_sign21():
    """pyqsp's PolySign: Chebyshev fit of erf(10 x), degree 21, rescaled to max 0.8923886753673906 (ensure_bounded)."""
    from pyqsp.poly import PolySign

    pc, scale = PolySign().generate(degree=21, delta=10, ensure_bounded=True, return_scale=True, chebyshev_basis=True)
    pc = np.asarray(pc, dtype=float)
    return pc, f"odd degree-21 Chebyshev approximation of sign(x): pyqsp PolySign (erf(10 x), rescaled by {float(scale)!r})"


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--outdir", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "examples"))
    ap.add_argument("--grid", type=int, default=2001)
    args = ap.parse_args(argv)
    os.makedirs(args.outdir, exist_ok=True)
    xs = np.linspace(-1, 1, args.grid)

    # ---- exact Lemma 9 phases for T_5 (no solver) --------------------------------------------
    d = 5
    phR = cheb_phases_R(d)
    f = C.chebval(xs, target_T5()[0])
    uR = tl_R(phR, xs)
    rec = {
        "name": "T5_lemma9_exact",
        "tool": "GSLW Lemma 9 (closed form)",
        "degree": d,
        "parity": 1,
        "target": target_T5()[1],
        "phases_R_over_pi": [str(Fraction(1 - d, 2))] + [str(Fraction(1, 2))] * (d - 1),
        "phases_R_decimal": [exact_decimal(p) for p in phR],
        "errors": {"max|seqR00 - T5|": float(np.abs(uR - f).max()), "max|Im seqR00|": float(np.abs(uR.imag).max())},
        "note": "seqR = [[T_d, U_{d-1} s],[(-1)^{d+1} U_{d-1} s, (-1)^d T_d]] for these phases.",
    }
    print("[T5_lemma9_exact] max|seqR00 - T5| = %.3e" % rec["errors"]["max|seqR00 - T5|"])
    dump(rec, args.outdir, "T5_lemma9_exact.json")

    # ---- pyqsp -------------------------------------------------------------------------------
    try:
        import pyqsp
        from pyqsp.angle_sequence import QuantumSignalProcessingPhases as QSPP

        pyqsp_ver = getattr(pyqsp, "__version__", "0.2.0 (pip)")
        have_pyqsp = True
    except Exception as e:  # pragma: no cover
        print("pyqsp unavailable:", e)
        have_pyqsp = False

    try:
        import qsppack

        qsppack_ver = getattr(qsppack, "__version__", "0.4.0 (pip)")
        have_qsppack = True
    except Exception as e:  # pragma: no cover
        print("qsppack unavailable:", e)
        have_qsppack = False

    targets = [("T5", *target_T5())]
    if have_pyqsp:
        pc, desc = target_sign21()
        targets.append(("sign21", pc, desc))

    for tname, cheb, desc in targets:
        cheb = np.asarray(cheb, dtype=float)
        deg = len(cheb) - 1
        parity = deg % 2
        if have_pyqsp:
            # (A) laurent / Wx / x-measurement.  For T5 the exact completion exists (suc=1, eps=0).
            kw = {"suc": 1.0, "eps": 0.0} if tname == "T5" else {}
            try:
                phW = QSPP(list(cheb), signal_operator="Wx", measurement="x", method="laurent", **kw)
                rec = verify_and_pack(
                    f"{tname}_pyqsp_laurent", f"pyqsp {pyqsp_ver}, QuantumSignalProcessingPhases(method='laurent', signal_operator='Wx', measurement='x', {kw})",
                    "U = e^{i phi_0 Z} prod W(x) e^{i phi_j Z}; <+|U|+> = Re P + i s Re Q = f  (Re P = f, Re Q = 0); phases not symmetric",
                    phW, cheb, desc, xs)
                dump(rec, args.outdir, f"{tname}_pyqsp_laurent.json")
            except Exception as e:
                print(f"pyqsp laurent failed on {tname}: {type(e).__name__}: {e}")
            # (B) sym_qsp (Im convention) -> shift both ends by -pi/4 to get Re convention
            try:
                full, reduced, par = QSPP(list(cheb), method="sym_qsp", chebyshev_basis=True)
                full = np.asarray(full, dtype=float)
                shifted = full.copy()
                shifted[0] -= PI / 4
                shifted[-1] -= PI / 4
                rec = verify_and_pack(
                    f"{tname}_pyqsp_symqsp", f"pyqsp {pyqsp_ver}, QuantumSignalProcessingPhases(method='sym_qsp', chebyshev_basis=True)",
                    "U = e^{i phi_0 Z} prod W(x) e^{i phi_j Z}; symmetric full phases with Im U00 = f.  "
                    "Stored W phases = full phases with pi/4 SUBTRACTED at both ends so that Re U00 = f.",
                    shifted, cheb, desc, xs,
                    extra={"solver_raw_full_phases_decimal": [exact_decimal(p) for p in full],
                           "solver_reduced_phases_decimal": [exact_decimal(p) for p in np.asarray(reduced, float)],
                           "solver_parity": int(par)})
                dump(rec, args.outdir, f"{tname}_pyqsp_symqsp.json")
            except Exception as e:
                print(f"pyqsp sym_qsp failed on {tname}: {type(e).__name__}: {e}")
        if have_qsppack:
            reduced = cheb[parity::2]
            done = False
            for method in (("Newton", "FPI") if tname == "T5" else ("FPI", "Newton")):
                if done:
                    break
                try:
                    opts = {"method": method, "targetPre": True, "typePhi": "full", "criteria": 1e-13, "maxiter": 5000}
                    phi, out = qsppack.solve(reduced, parity, opts)
                    phi = np.asarray(phi, dtype=float)
                    rec = verify_and_pack(
                        f"{tname}_qsppack", f"qsppack {qsppack_ver}, solve(reduced_cheb, parity, {opts})",
                        "U = e^{i phi_0 Z} prod W(x) e^{i phi_j Z}; symmetric full phases (pi/4 already added at both ends); Re U00 = f",
                        phi, cheb, desc, xs,
                        extra={"solver_info": {k: (float(v) if isinstance(v, (int, float, np.floating)) else str(v)) for k, v in out.items()}})
                    dump(rec, args.outdir, f"{tname}_qsppack.json")
                    done = True
                except Exception as e:
                    print(f"qsppack {method} failed on {tname}: {type(e).__name__}: {e}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
