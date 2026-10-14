"""Independent numerical cross-check of the two-sphere example (original Theorem 1.2, Table 1).

Source audited: OQ7_quartic_Maxwell_2026-10-10.pdf, SHA-256
576478ba88fd374e724b96e07c5e3e1648485cd163dc4d8ba9cd0b3ef52eac62.

The manuscript's own boundary-matching solver was not recovered, so nothing here
reuses it.  Two independent routes are computed (standard library only):

1. Static single-exchange moments.  Each isolated ball responds exactly to the
   constant drive e_x (polarization beta e_x) and to the affine drive z e_x.
   The affine drive splits into the centre term z_j e_x, a symmetric traceless
   quadrupolar part (exact response 5chi/(5+2chi), from the l = 2 depolarization
   factor 2/5) and an antisymmetric part (no bound charge, response chi).  One
   exchange between the balls is evaluated exactly with the ball mean-value
   property for the harmonic static dyadic kernel.  Neglected multiple exchanges
   are O(c^2) relative, with c < 1/2500 from the manuscript's eq. (36).
   This gives an estimate of the exact coefficient C = 2|Im(p0^* p1)|/(3 pi D0).

2. Dynamic coupled electric dipoles with exact Mie a_1 polarizabilities and the
   full retarded dyadic Green function.  This model omits magnetic dipoles and
   induced quadrupoles, so it checks normalization, magnitude and the t-trend of
   Table 1, not the theorem.

Neither route is a proof.  Run:  python -I two_sphere_crosscheck.py [output.json]
"""

import cmath
import json
import math
import sys

a = 1 / 20
r1, r2 = a, 2 * a
z1, z2 = -0.5, 0.5
chi1, chi2 = 1j, 2j
v1, v2 = 4 * math.pi * r1 ** 3 / 3, 4 * math.pi * r2 ** 3 / 3
w = v1 + v2
g0 = -1 / (4 * math.pi)  # H(e_z) e_x = g0 e_x


def beta(chi):
    return 3 * chi / (3 + chi)


def gamma2(chi):  # exact ball response to a symmetric traceless linear drive
    return 5 * chi / (5 + 2 * chi)


b1, b2 = beta(chi1), beta(chi2)
# ---------------- route 1: static moments
p0b = b1 * v1 + b2 * v2
p1b = b1 * v1 * z1 + b2 * v2 * z2
p0_1 = 2 * g0 * b1 * b2 * v1 * v2  # one exchange, exact for the constant drive
# one exchange for the affine drive: centre terms cancel because z1 + z2 = 0;
# quadrupolar term: p1^(1) = sum_{i!=j} beta_i v_i (-v_j r_j^2/5) (3 s_ij/(4 pi)) gamma_j,
# s_ij = sign((c_i - c_j)_z); the antisymmetric (curl) part of the drive drops out exactly.
s21, s12 = +1, -1
p1_1 = (b2 * v2 * (-v1 * r1 ** 2 / 5) * (3 * s21 / (4 * math.pi)) * gamma2(chi1)
        + b1 * v1 * (-v2 * r2 ** 2 / 5) * (3 * s12 / (4 * math.pi)) * gamma2(chi2))


def coeff(p0, p1):
    return 2 * abs((p0.conjugate() * p1).imag) / (3 * math.pi * p0.imag)


C_block = coeff(p0b, p1b)
C_dip = coeff(p0b + p0_1, p1b)  # dipole-only exchange
C_one = coeff(p0b + p0_1, p1b + p1_1)  # dipole + quadrupole single exchange
c_bound = 4 * math.sqrt(2) / 14739

# ---------------- route 2: dynamic coupled electric dipoles with Mie a1
def psi1(z):
    return cmath.sin(z) / z - cmath.cos(z)


def dpsi1(z):
    return cmath.cos(z) / z - cmath.sin(z) / z ** 2 + cmath.sin(z)


def xi1(z):
    return psi1(z) + 1j * (-cmath.cos(z) / z - cmath.sin(z))


def dxi1(z):
    # derivative of z*y1(z) = -cos z/z - sin z  is  sin z/z + cos z/z^2 - cos z
    return dpsi1(z) + 1j * (cmath.sin(z) / z + cmath.cos(z) / z ** 2 - cmath.cos(z))


def mie_alpha(chi, radius, k):
    m = cmath.sqrt(1 + chi)
    x = k * radius
    num = m * psi1(m * x) * dpsi1(x) - psi1(x) * dpsi1(m * x)
    den = m * psi1(m * x) * dxi1(x) - xi1(x) * dpsi1(m * x)
    a1 = num / den
    return 6j * math.pi * a1 / k ** 3


def Gxx(d, k):  # transverse component of (k^2 + grad grad) e^{ikr}/(4 pi r) at separation d along z
    return cmath.exp(1j * k * d) / (4 * math.pi * d ** 3) * ((k * d) ** 2 + 1j * k * d - 1)


def dipole_gamma(t):
    k = t  # centre separation is 1, so k = t
    A1, A2 = mie_alpha(chi1, r1, k), mie_alpha(chi2, r2, k)
    G = Gxx(1.0, k)
    ImG0 = k ** 3 / (6 * math.pi)
    out = {}
    for sgn in (+1, -1):
        E1, E2 = cmath.exp(1j * sgn * k * z1), cmath.exp(1j * sgn * k * z2)
        # p1 = A1(E1 + G p2), p2 = A2(E2 + G p1)
        det = 1 - A1 * A2 * G * G
        p1 = A1 * (E1 + G * A2 * E2) / det
        p2 = A2 * (E2 + G * A1 * E1) / det
        X = k * (E1.conjugate() * p1 + E2.conjugate() * p2).imag
        S = k * (ImG0 * (abs(p1) ** 2 + abs(p2) ** 2) + 2 * (p1.conjugate() * G.imag * p2).real)
        out[sgn] = (X, S)
    (Xp, Sp), (Xm, Sm) = out[1], out[-1]
    return {"t": t, "Gamma": abs(Sp - Sm) / Xp, "Gamma_over_t4": abs(Sp - Sm) / Xp / t ** 4,
            "extinction_reciprocity_rel": abs(Xp - Xm) / Xp,
            "absorption_plus": Xp - Sp, "absorption_minus": Xm - Sm}


# Mie small-size sanity: alpha -> beta v
k_small = 1e-4
mie_static_rel = abs(mie_alpha(chi2, r2, k_small) - b2 * v2) / abs(b2 * v2)

table = {0.4: 2.89345641e-5, 0.2: 3.03048021e-5, 0.1: 3.06551229e-5, 0.05: 3.07431878e-5, 0.025: 3.07652336e-5}
dyn = [dipole_gamma(t) for t in sorted(table, reverse=True)]
for row in dyn:
    row["manuscript_Gamma_over_t4"] = table[row["t"]]
    row["relative_difference"] = row["Gamma_over_t4"] / table[row["t"]] - 1

report = {
    "source_sha256": "576478ba88fd374e724b96e07c5e3e1648485cd163dc4d8ba9cd0b3ef52eac62",
    "static": {
        "C_isolated_block": C_block,
        "C_dipole_exchange_only": C_dip,
        "C_single_exchange_with_quadrupole": C_one,
        "manuscript_interval": [36 / 1299125, 44 / 1295875],
        "manuscript_numerical_extrapolation": 3.07725625e-5,
        "relative_gap_single_exchange_vs_extrapolation": C_one / 3.07725625e-5 - 1,
        "multiple_exchange_relative_scale_c_squared": c_bound ** 2,
    },
    "mie_small_size_alpha_relative_error": mie_static_rel,
    "dynamic_coupled_dipole": dyn,
}
print(json.dumps(report["static"], indent=1))
for row in dyn:
    print(f"t={row['t']:<6} G/t4={row['Gamma_over_t4']:.8e} paper={row['manuscript_Gamma_over_t4']:.8e} "
          f"rel={row['relative_difference']:+.2e} recip={row['extinction_reciprocity_rel']:.1e}")
print("Mie static limit rel err", mie_static_rel)
# Diagnostic tolerances (agreement levels observed on 14 October 2026, with margin)
gates = {
    "single-exchange C inside proved interval": 36 / 1299125 <= C_one <= 44 / 1295875,
    "single-exchange C within 1e-5 of manuscript extrapolation": abs(C_one / 3.07725625e-5 - 1) < 1e-5,
    "dipole model within 1e-3 of Table 1 at every t": all(abs(r["relative_difference"]) < 1e-3 for r in dyn),
    "extinction reciprocity to rounding": all(r["extinction_reciprocity_rel"] < 1e-12 for r in dyn),
    "Mie static limit": mie_static_rel < 1e-4,
}
report["gates"] = gates
if len(sys.argv) > 1:
    with open(sys.argv[1], "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=1)
print(f"{sum(gates.values())}/{len(gates)} diagnostic gates passed")
sys.exit(0 if all(gates.values()) else 1)
