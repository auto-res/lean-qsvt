#!/usr/bin/env python
"""
qsp_conventions.py -- numerical reference for the QSP conventions used in lean-qsvt.

Conventions (GSLW = Gilyen-Su-Low-Wiebe, arXiv:1806.01838):

  phaseZ(phi) = diag(e^{i phi}, e^{-i phi})                 ( = exp(i phi sigma_z) )
  R(x)        = [[x, s], [s, -x]],        s = sqrt(1 - x^2)   (GSLW Def 7, "reflection")
  W(x)        = [[x, i s], [i s, x]]                          (GSLW Thm 3, "rotation")

  seqR([phi_1, ..., phi_d], x) = phaseZ(phi_1) R(x) phaseZ(phi_2) R(x) ... phaseZ(phi_d) R(x)
      Lean recursion: seqR []        = 1
                      seqR (phi::Ph) = phaseZ phi * R x * seqR Ph         (phi_1 is leftmost)

  seqW([phi'_0, ..., phi'_k], x) = phaseZ(phi'_0) W(x) phaseZ(phi'_1) W(x) ... W(x) phaseZ(phi'_k)

Polynomial structure of seqR (verified here, see `check_recursion`):

  seqR(Ph, x) = [[ P(x),            Q^*(-x) * s ],
                 [ Q(x) * s,        P^*(-x)     ]]          (^* = complex conjugation of coefficients)

  with the closed two-term recursion on the FIRST COLUMN (P, Q):
      (P, Q)_[]       = (1, 0)
      (P, Q)_(phi::Ph) = ( e^{ i phi} * (X * P + (1 - X^2) * Q),
                           e^{-i phi} * (P - X * Q) )

Run `python qsp_conventions.py verify` for all numerical checks, `symbolic` for the sympy derivation.
"""
from __future__ import annotations

import argparse
import math
import sys
from typing import Sequence

import numpy as np
from numpy.polynomial import Polynomial as Poly

PI = math.pi
X = Poly([0.0, 1.0])
ONE_MINUS_X2 = Poly([1.0, 0.0, -1.0])

# ----------------------------------------------------------------------------
# 2x2 building blocks
# ----------------------------------------------------------------------------


def phaseZ(phi: float) -> np.ndarray:
    """exp(i phi sigma_z) = diag(e^{i phi}, e^{-i phi})."""
    return np.array([[np.exp(1j * phi), 0.0], [0.0, np.exp(-1j * phi)]], dtype=complex)


def Rref(x: float) -> np.ndarray:
    """GSLW Def 7 reflection R(x) = [[x, s], [s, -x]]."""
    s = math.sqrt(max(0.0, 1.0 - x * x))
    return np.array([[x, s], [s, -x]], dtype=complex)


def Wrot(x: float) -> np.ndarray:
    """GSLW Thm 3 rotation W(x) = [[x, i s], [i s, x]]."""
    s = math.sqrt(max(0.0, 1.0 - x * x))
    return np.array([[x, 1j * s], [1j * s, x]], dtype=complex)


SIGMA_Z = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=complex)
I2 = np.eye(2, dtype=complex)


def seqR(phis: Sequence[float], x: float) -> np.ndarray:
    """seqR([phi_1..phi_d], x) = prod_{j=1}^d phaseZ(phi_j) R(x), phi_1 leftmost (Lean recursion)."""
    M = I2.copy()
    R = Rref(x)
    for phi in reversed(list(phis)):  # seqR (phi::Ph) = phaseZ phi * R * seqR Ph
        M = phaseZ(phi) @ R @ M
    return M


def seqW(phis: Sequence[float], x: float) -> np.ndarray:
    """seqW([phi'_0..phi'_k], x) = phaseZ(phi'_0) prod_{j=1}^k W(x) phaseZ(phi'_j)."""
    phis = list(phis)
    M = phaseZ(phis[0])
    W = Wrot(x)
    for phi in phis[1:]:
        M = M @ W @ phaseZ(phi)
    return M


# ----------------------------------------------------------------------------
# Polynomial recursions
# ----------------------------------------------------------------------------


def conj_poly(P: Poly) -> Poly:
    """P^*: conjugate the coefficients (Polynomial.map (starRingEnd C) in Lean)."""
    return Poly(np.conj(P.coef))


def flip_poly(P: Poly) -> Poly:
    """P(-X)  (Polynomial.comp P (-X) in Lean)."""
    c = P.coef.copy()
    c[1::2] *= -1
    return Poly(c)


def qsp_poly_R(phis: Sequence[float]) -> tuple[Poly, Poly]:
    """
    Two-term recursion for the R convention (spec ID QSP-3).  Returns (P, Q) with

        seqR(Ph, x) e_0 = ( P(x), Q(x) * sqrt(1-x^2) )^T     (first column).

        qspPoly []        = (1, 0)
        qspPoly (phi::Ph) = ( C(e^{ i phi}) * (X * P + (1 - X^2) * Q),
                              C(e^{-i phi}) * (P - X * Q) )              where (P, Q) = qspPoly Ph
    """
    P, Q = Poly([1.0 + 0j]), Poly([0.0 + 0j])
    for phi in reversed(list(phis)):
        e = np.exp(1j * phi)
        P, Q = e * (X * P + ONE_MINUS_X2 * Q), np.conj(e) * (P - X * Q)
    return P, Q


def qsp_poly_R4(phis: Sequence[float]) -> tuple[Poly, Poly, Poly, Poly]:
    """
    Four-term recursion for the full matrix, seqR(Ph, x) = [[P, Qt * s], [Qb * s, Pb]].

        (P, Qt, Qb, Pb)_[]        = (1, 0, 0, 1)
        (P, Qt, Qb, Pb)_(phi::Ph) = ( e^{ i phi} (X P + (1 - X^2) Qb),
                                      e^{ i phi} (X Qt + Pb),
                                      e^{-i phi} (P - X Qb),
                                      e^{-i phi} ((1 - X^2) Qt - X Pb) )
    """
    P, Qt, Qb, Pb = Poly([1.0 + 0j]), Poly([0j]), Poly([0j]), Poly([1.0 + 0j])
    for phi in reversed(list(phis)):
        e = np.exp(1j * phi)
        P, Qt, Qb, Pb = (
            e * (X * P + ONE_MINUS_X2 * Qb),
            e * (X * Qt + Pb),
            np.conj(e) * (P - X * Qb),
            np.conj(e) * (ONE_MINUS_X2 * Qt - X * Pb),
        )
    return P, Qt, Qb, Pb


def qsp_poly_W(phis: Sequence[float]) -> tuple[Poly, Poly]:
    """
    GSLW Thm 3 form for the W convention: seqW(Ph', x) = [[P, i Q s], [i Q^* s, P^*]].
    Recursion obtained by peeling phaseZ(phi'_0) W(x) off the left:
        (P, Q)_[phi'_k]           = (e^{i phi'_k}, 0)
        (P, Q)_(phi'::Ph')        = ( e^{ i phi'} (X P - (1 - X^2) Q^*),  e^{ i phi'} (X Q + P^*) )
    """
    phis = list(phis)
    P, Q = Poly([np.exp(1j * phis[-1])]), Poly([0j])
    for phi in reversed(phis[:-1]):
        e = np.exp(1j * phi)
        P, Q = e * (X * P - ONE_MINUS_X2 * conj_poly(Q)), e * (X * Q + conj_poly(P))
    return P, Q


# ----------------------------------------------------------------------------
# Convention conversion
# ----------------------------------------------------------------------------


def W_to_R(phisW: Sequence[float]) -> list[float]:
    """
    GSLW Cor 8 mapping (top-left entries agree):
        phi_1 = phi'_0 + phi'_d + (d-1) pi/2,   phi_j = phi'_{j-1} - pi/2  (2 <= j <= d).
    Full-matrix relation (verified in `check_conversion`), theta = phi'_d - pi/4:
        seqW(Ph') = sigma_z^d  phaseZ(-theta)  seqR(Ph)  phaseZ(theta).
    """
    phisW = list(phisW)
    d = len(phisW) - 1
    if d < 1:
        raise ValueError("need at least two W phases")
    out = [phisW[0] + phisW[d] + (d - 1) * PI / 2]
    out += [phisW[j - 1] - PI / 2 for j in range(2, d + 1)]
    return out


def W_to_R_exact(phisW: Sequence[float]) -> tuple[list[float], float]:
    """
    Exact matrix identity, theta = phi'_d - pi/4:
        seqW(Ph') = i^d * seqR(Ph~) * phaseZ(theta),
        Ph~ = (phi'_0 - pi/4, phi'_1 - pi/2, ..., phi'_{d-1} - pi/2).
    """
    phisW = list(phisW)
    d = len(phisW) - 1
    tilde = [phisW[0] - PI / 4] + [phisW[j] - PI / 2 for j in range(1, d)]
    return tilde, phisW[d] - PI / 4


def R_to_W(phisR: Sequence[float], split: float = 0.5) -> list[float]:
    """
    Inverse of W_to_R.  P depends on phi'_0 + phi'_d only, so the split is free:
        phi'_0 = split * (phi_1 - (d-1) pi/2),  phi'_d = (1 - split) * (phi_1 - (d-1) pi/2),
        phi'_{j-1} = phi_j + pi/2  (2 <= j <= d).
    """
    phisR = list(phisR)
    d = len(phisR)
    total = phisR[0] - (d - 1) * PI / 2
    return [split * total] + [phisR[j - 1] + PI / 2 for j in range(2, d + 1)] + [(1 - split) * total]


def cheb_phases_R(d: int) -> list[float]:
    """GSLW Lemma 9: seqR(Ph, x)[0,0] = T_d(x) for Ph = ((1-d) pi/2, pi/2, ..., pi/2)."""
    return [(1 - d) * PI / 2] + [PI / 2] * (d - 1)


# ----------------------------------------------------------------------------
# Checks
# ----------------------------------------------------------------------------


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


def check_eq16() -> dict:
    """W(x) = i phaseZ(-pi/4) R(x) phaseZ(-pi/4)   (NOT ... phaseZ(+pi/4))."""
    xs = np.linspace(-1, 1, 101)
    err_minus = max(np.abs(Wrot(x) - 1j * phaseZ(-PI / 4) @ Rref(x) @ phaseZ(-PI / 4)).max() for x in xs)
    err_plus = max(np.abs(Wrot(x) - 1j * phaseZ(-PI / 4) @ Rref(x) @ phaseZ(+PI / 4)).max() for x in xs)
    return {"W = i e^{-i pi/4 Z} R e^{-i pi/4 Z}": err_minus, "W = i e^{-i pi/4 Z} R e^{+i pi/4 Z}": err_plus}


def check_conversion(dmax: int = 8, trials: int = 25, seed: int = 1) -> dict:
    rng = _rng(seed)
    res = {}
    for d in range(1, dmax + 1):
        e_tl = e_full = e_full2 = e_inv = 0.0
        variants = {
            "phi_j = phi'_{j-1} + pi/2 (sign flipped)": 0.0,
            "phi_1 = phi'_0 + phi'_d - (d-1)pi/2": 0.0,
            "phi_j = phi'_j - pi/2 (index shift)": 0.0,
            "phi_1 = phi'_0 + phi'_d (no offset)": 0.0,
        }
        for _ in range(trials):
            phW = rng.uniform(-PI, PI, d + 1)
            phR = W_to_R(phW)
            tilde, theta = W_to_R_exact(phW)
            for x in rng.uniform(-1, 1, 5):
                A = seqW(phW, x)
                B = seqR(phR, x)
                e_tl = max(e_tl, abs(A[0, 0] - B[0, 0]))
                # exact full-matrix identities
                C = (1j ** d) * seqR(tilde, x) @ phaseZ(theta)
                e_full = max(e_full, np.abs(A - C).max())
                D = np.linalg.matrix_power(SIGMA_Z, d) @ phaseZ(-theta) @ B @ phaseZ(theta)
                e_full2 = max(e_full2, np.abs(A - D).max())
                # inverse map
                for split in (0.0, 0.5, 1.0):
                    E = seqW(R_to_W(phR, split), x)
                    e_inv = max(e_inv, abs(E[0, 0] - B[0, 0]))
                # wrong variants (should fail for generic phases)
                v1 = [phW[0] + phW[d] + (d - 1) * PI / 2] + [phW[j - 1] + PI / 2 for j in range(2, d + 1)]
                v2 = [phW[0] + phW[d] - (d - 1) * PI / 2] + [phW[j - 1] - PI / 2 for j in range(2, d + 1)]
                v3 = [phW[0] + phW[d] + (d - 1) * PI / 2] + [phW[j] - PI / 2 for j in range(2, d + 1)]
                v4 = [phW[0] + phW[d]] + [phW[j - 1] - PI / 2 for j in range(2, d + 1)]
                for key, v in zip(variants, (v1, v2, v3, v4)):
                    variants[key] = max(variants[key], abs(A[0, 0] - seqR(v, x)[0, 0]))
        res[d] = {
            "topleft(seqW) - topleft(seqR(W_to_R))": e_tl,
            "seqW - i^d seqR(Ph~) phaseZ(theta)": e_full,
            "seqW - sigma_z^d phaseZ(-theta) seqR(Ph) phaseZ(theta)": e_full2,
            "R_to_W round trip (top-left)": e_inv,
            "wrong variants (max err, should be O(1))": {k: round(v, 3) for k, v in variants.items()},
        }
    return res


def check_lemma9(dmax: int = 8) -> dict:
    xs = np.linspace(-1, 1, 2001)
    res = {}
    for d in range(1, dmax + 1):
        ph = cheb_phases_R(d)
        err = max(abs(seqR(ph, x)[0, 0] - math.cos(d * math.acos(x))) for x in xs)
        P, Qt, Qb, Pb = qsp_poly_R4(ph)
        # compare with Chebyshev T_d and U_{d-1}
        Td = Poly(np.polynomial.chebyshev.cheb2poly([0] * d + [1]))
        Ud1 = Td.deriv() / d  # U_{d-1} = T_d' / d
        res[d] = {
            "max|seqR[0,0] - cos(d arccos x)|": err,
            "P - T_d": np.abs((P - Td).coef).max(),
            "Qt - U_{d-1}": np.abs((Qt - Ud1).coef).max(),
            "Qb - (-1)^{d+1} U_{d-1}": np.abs((Qb - (-1) ** (d + 1) * Ud1).coef).max(),
            "Pb - (-1)^d T_d": np.abs((Pb - (-1) ** d * Td).coef).max(),
        }
    return res


def _parity_violation(P: Poly, parity: int) -> float:
    c = P.coef
    bad = [abs(c[k]) for k in range(len(c)) if k % 2 != parity % 2]
    return max(bad) if bad else 0.0


def check_recursion(dmax: int = 8, trials: int = 25, seed: int = 2) -> dict:
    rng = _rng(seed)
    res = {}
    for d in range(0, dmax + 1):
        e_mat = e_two = e_rel = e_unit = e_neg = e_par = e_deg = e_end = e_W = 0.0
        for _ in range(trials):
            ph = rng.uniform(-PI, PI, d)
            P, Qt, Qb, Pb = qsp_poly_R4(ph)
            P2, Q2 = qsp_poly_R(ph)
            # (a) full matrix from 4-term recursion
            for x in rng.uniform(-1, 1, 5):
                s = math.sqrt(1 - x * x)
                M = np.array([[P(x), Qt(x) * s], [Qb(x) * s, Pb(x)]])
                e_mat = max(e_mat, np.abs(seqR(ph, x) - M).max())
                e_unit = max(e_unit, abs(abs(P(x)) ** 2 + (1 - x * x) * abs(Qb(x)) ** 2 - 1))
            # (b) two-term recursion = first column of 4-term
            e_two = max(e_two, np.abs((P - P2).coef).max(), np.abs((Qb - Q2).coef).max())
            # (c) relations between entries: Qt = Qb^*(-X), Pb = P^*(-X)
            e_rel = max(e_rel, np.abs((Qt - flip_poly(conj_poly(Qb))).coef).max(),
                        np.abs((Pb - flip_poly(conj_poly(P))).coef).max())
            # equivalently Pb = (-1)^d P^*, Qt = (-1)^{d+1} Qb^*  (via parity)
            e_rel = max(e_rel, np.abs((Pb - (-1) ** d * conj_poly(P)).coef).max(),
                        np.abs((Qt - (-1) ** (d + 1) * conj_poly(Qb)).coef).max())
            # (d) parity and degree
            e_par = max(e_par, _parity_violation(P, d), _parity_violation(Qb, d - 1))
            e_deg = max(e_deg, float(P.degree() > d), float(Qb.degree() > max(d - 1, 0)))
            # (e) qspPoly(-Ph) = (P^*, Q^*)
            Pn, Qn = qsp_poly_R(-ph)
            e_neg = max(e_neg, np.abs((Pn - conj_poly(P)).coef).max(), np.abs((Qn - conj_poly(Qb)).coef).max())
            # (f) endpoint formulas (QSP-5): P(+-1) = (+-1)^d prod e^{i phi_j}; d even: P(0) = e^{-i sum (-1)^j phi_j}
            prod = np.prod(np.exp(1j * ph)) if d else 1.0
            e_end = max(e_end, abs(P(1.0) - prod), abs(P(-1.0) - (-1) ** d * prod))
            if d % 2 == 0:
                sgn_sum = sum(((-1) ** j) * ph[j - 1] for j in range(1, d + 1))  # j = 1..d as in GSLW
                e_end = max(e_end, abs(P(0.0) - np.exp(-1j * sgn_sum)))
            # (g) W convention recursion vs seqW, and P_W = P_R after conversion
            if d >= 1:
                phW = rng.uniform(-PI, PI, d + 1)
                PW, QW = qsp_poly_W(phW)
                PR, _ = qsp_poly_R(W_to_R(phW))
                for x in rng.uniform(-1, 1, 3):
                    s = math.sqrt(1 - x * x)
                    MW = np.array([[PW(x), 1j * QW(x) * s], [1j * conj_poly(QW)(x) * s, conj_poly(PW)(x)]])
                    e_W = max(e_W, np.abs(seqW(phW, x) - MW).max())
                e_W = max(e_W, np.abs((PW - PR).coef).max())
        res[d] = {
            "seqR - [[P,Qt s],[Qb s,Pb]]": e_mat,
            "two-term (P,Q) == (P,Qb) of four-term": e_two,
            "Qt = Qb^*(-X) = (-1)^{d+1} Qb^*,  Pb = P^*(-X) = (-1)^d P^*": e_rel,
            "parity violation (P ~ d, Q ~ d-1)": e_par,
            "degree violation (deg P <= d, deg Q <= d-1)": e_deg,
            "|P|^2 + (1-x^2)|Q|^2 - 1": e_unit,
            "qspPoly(-Ph) - (P^*, Q^*)": e_neg,
            "endpoint formulas P(+-1), P(0)": e_end,
            "W conv: seqW - [[P,iQs],[iQ*s,P*]] and P_W - P_R(W_to_R)": e_W,
        }
    return res


def symbolic_recursion() -> str:
    """sympy derivation of the one-step update, with s^2 = 1 - x^2."""
    import sympy as sp

    x, s, phi = sp.symbols("x s phi", real=True)
    P, Qt, Qb, Pb = sp.symbols("P Q_t Q_b P_b")
    E = sp.exp(sp.I * phi)
    R = sp.Matrix([[x, s], [s, -x]])
    Z = sp.Matrix([[E, 0], [0, 1 / E]])
    M = sp.Matrix([[P, Qt * s], [Qb * s, Pb]])
    N = (Z * R * M).applyfunc(sp.expand).subs(s**2, 1 - x**2).applyfunc(sp.expand)
    lines = ["one step: phaseZ(phi) * R(x) * [[P, Q_t s], [Q_b s, P_b]]  (s^2 = 1 - x^2):"]
    lines.append(f"  P_new      = {sp.factor(N[0, 0])}")
    lines.append(f"  Q_t_new s  = {sp.factor(N[0, 1])}")
    lines.append(f"  Q_b_new s  = {sp.factor(N[1, 0])}")
    lines.append(f"  P_b_new    = {sp.factor(N[1, 1])}")
    # eq (16) check
    W = sp.Matrix([[x, sp.I * s], [sp.I * s, x]])

    def pz(t):
        return sp.Matrix([[sp.exp(sp.I * t), 0], [0, sp.exp(-sp.I * t)]])

    for sgn in (-1, +1):
        cand = (sp.I * pz(-sp.pi / 4) * R * pz(sgn * sp.pi / 4)).applyfunc(sp.simplify)
        ok = (cand - W).applyfunc(sp.simplify) == sp.zeros(2, 2)
        lines.append(f"  i e^(-i pi/4 Z) R e^({'+' if sgn > 0 else '-'}i pi/4 Z) = {cand.tolist()}  == W : {ok}")
    return "\n".join(lines)


def _fmt(d: dict, indent: int = 0) -> str:
    out = []
    for k, v in d.items():
        if isinstance(v, dict):
            out.append(" " * indent + f"{k}:")
            out.append(_fmt(v, indent + 2))
        elif isinstance(v, float):
            out.append(" " * indent + f"{k}: {v:.3e}")
        else:
            out.append(" " * indent + f"{k}: {v}")
    return "\n".join(out)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["verify", "symbolic", "eq16", "conversion", "lemma9", "recursion"], nargs="?",
                    default="verify")
    ap.add_argument("--dmax", type=int, default=8)
    args = ap.parse_args(argv)
    if args.cmd in ("verify", "eq16"):
        print("== eq (16) check (max abs error over x in [-1,1]) ==")
        print(_fmt(check_eq16()))
    if args.cmd in ("verify", "conversion"):
        print("\n== W -> R conversion (GSLW Cor 8), random phases, d = 1..%d ==" % args.dmax)
        print(_fmt(check_conversion(args.dmax)))
    if args.cmd in ("verify", "lemma9"):
        print("\n== Lemma 9 (Chebyshev phases) ==")
        print(_fmt(check_lemma9(args.dmax)))
    if args.cmd in ("verify", "recursion"):
        print("\n== polynomial recursion for seqR, random phases, d = 0..%d ==" % args.dmax)
        print(_fmt(check_recursion(args.dmax)))
    if args.cmd in ("verify", "symbolic"):
        print("\n== sympy ==")
        print(symbolic_recursion())
    return 0


if __name__ == "__main__":
    sys.exit(main())
