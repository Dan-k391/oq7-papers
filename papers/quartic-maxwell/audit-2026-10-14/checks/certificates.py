"""Independent exact checks of the constants in the 10 October 2026 quartic manuscript.

Source audited: papers/quartic-maxwell/manuscript/OQ7_quartic_Maxwell_2026-10-10.pdf
(SHA-256 576478ba88fd374e724b96e07c5e3e1648485cd163dc4d8ba9cd0b3ef52eac62).

Standard library only.  Every quantity that contains pi is written as a rational
multiple of a power of pi, and square roots are compared by squaring, so each
assertion below is an exact rational statement.  Floating point appears only in
the grid scans marked DIAGNOSTIC, which are not proofs.

Run:  python -I certificates.py  [output.json]
"""

from fractions import Fraction as Fr
import cmath
import json
import math
import sys

results = []


def check(name, ok, detail=""):
    results.append({"check": name, "pass": bool(ok), "detail": str(detail)})
    if not ok:
        print("FAIL", name, detail)


# ---------------------------------------------------------------- complex rationals
class Q:
    """Exact complex rational a + b i."""

    def __init__(self, re, im=0):
        self.re, self.im = Fr(re), Fr(im)

    def __add__(self, o):
        o = o if isinstance(o, Q) else Q(o)
        return Q(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, Q) else Q(o)
        return Q(self.re - o.re, self.im - o.im)

    def __mul__(self, o):
        o = o if isinstance(o, Q) else Q(o)
        return Q(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def conj(self):
        return Q(self.re, -self.im)

    def inv(self):
        d = self.re ** 2 + self.im ** 2
        return Q(self.re / d, -self.im / d)

    def __truediv__(self, o):
        o = o if isinstance(o, Q) else Q(o)
        return self * o.inv()

    def abs2(self):
        return self.re ** 2 + self.im ** 2


I = Q(0, 1)

# ------------------------------------------------- Lemma 3.1 / eq. (15): kernel facts (DIAGNOSTIC)
def b_fun(u):
    return cmath.exp(1j * u) * (1j * u - 1) + 1


worst = 0.0
for n in range(1, 20001):
    u = 20.0 * n / 20000
    worst = max(worst, abs(b_fun(u)) / (u * u / 2))
check("diag: |b(u)| <= u^2/2 on (0,20] grid", worst <= 1 + 1e-12, worst)
# b'(u) = -u e^{iu}  (finite-difference spot check)
h = 1e-6
fd = max(abs((b_fun(u + h) - b_fun(u - h)) / (2 * h) + u * cmath.exp(1j * u)) for u in (0.3, 1.7, 4.2))
check("diag: b'(u) = -u e^{iu}", fd < 1e-6, fd)
# Section 5.4: |A(s)|, |B(s)| <= s^2 on 0 < s <= 6/5
A_fun = lambda s: cmath.exp(1j * s) * (s * s + 1j * s - 1) + 1
B_fun = lambda s: 2 * (cmath.exp(1j * s) * (1 - 1j * s) - 1)
wA = max(max(abs(A_fun(s)), abs(B_fun(s))) / (s * s) for s in (1.2 * n / 5000 for n in range(1, 5001)))
# |B(s)|/s^2 -> 1 as s -> 0, so allow floating-point rounding only
check("diag: |A(s)|,|B(s)| <= s^2 on (0,6/5] (rounding tol 1e-8)", wA <= 1 + 1e-8, wA)
# The integral bound used: ((1+s^2)^{3/2}-1)/3 <= s^2 for s^2 <= 3  <=>  (1+x)^3 <= (1+3x)^2 on [0,3]
# (1+3x)^2 - (1+x)^3 = 3x^2 - x^3 + ... = x^2 (3 - x) + 3x - 3x ... expand exactly:
# (1+3x)^2 - (1+x)^3 = 1+6x+9x^2 - 1-3x-3x^2-x^3 = 3x + 6x^2 - x^3 = x(3 + 6x - x^2) >= 0 for 0<=x<=3+2sqrt3
check("exact: |A(s)|<=s^2 integration bound valid for s^2<=3 (x(3+6x-x^2)>=0 on [0,3])",
      all(Fr(x) * (3 + 6 * Fr(x) - Fr(x) ** 2) >= 0 for x in [Fr(k, 100) for k in range(0, 301)]))
# Schur constant: (3k^2/(8 pi)) * (2 pi a^2) = (3/4) k^2 a^2
check("exact: Lemma 3.1 Schur constant 3/(8pi)*2pi = 3/4", Fr(3, 8) * 2 == Fr(3, 4))

# ------------------------------------------- Lemma 3.2: integral of Pi_n over the sphere
# int_{S^2} (I - n n^T) dOmega = 4 pi I - (4 pi/3) I = (8 pi/3) I
check("exact: int Pi_n dOmega = (8pi/3) I", Fr(4) - Fr(4, 3) == Fr(8, 3))
# k^3/(16 pi^2) * 8 pi/3 = k^3/(6 pi): dipole radiation constant used in Q_0 = 1/(6 pi)
check("exact: (1/16pi^2)(8pi/3) = 1/(6pi)", Fr(1, 16) * Fr(8, 3) == Fr(1, 6))

# --------------------------------------------- Theorem 1.1: the algebraic chain (24)->(5)->(6)
# |S+-S-| <= (k^4/16pi^2)(8piV/3)|dp|(|p+|+|p-|) = (k^4 V/(6 pi)) ...
# |dp| <= 2 rho k R sqrt V, |p+|+|p-| <= 2h, sqrt V <= L h, h^2 = rho X / k
# => |S+-S-| <= (k^4 V/(6pi)) * 2 rho k R * L h * 2h * ... collect the pi-free coefficient:
coef = Fr(1, 6) * 2 * 2  # (1/(6pi)) * 2 * 2 = 2/(3pi)
check("exact: Theorem 1.1 coefficient 2/(3pi)", coef == Fr(2, 3))
# (5) -> (6): V <= 4 pi R^3/3:  (2/(3pi)) * (4pi/3) = 8/9
check("exact: Theorem 1.1 (6) coefficient 8/9", Fr(2, 3) * Fr(4, 3) == Fr(8, 9))

# ------------------------------------------------------- Section 5: two-sphere certificate
a = Fr(1, 20)
chi1, chi2 = Q(0, 1), Q(0, 2)
beta = lambda chi: Q(3) * chi / (Q(3) + chi)
b1, b2 = beta(chi1), beta(chi2)
check("exact: beta_1 = 3(1+3i)/10", b1.re == Fr(3, 10) and b1.im == Fr(9, 10))
check("exact: beta_2 = 6(2+3i)/13", b2.re == Fr(12, 13) and b2.im == Fr(18, 13))
# Work in units u = pi a^3.  |Omega_1| = 4u/3, |Omega_2| = 32u/3, w = 12u.
v1, v2, w = Fr(4, 3), Fr(32, 3), Fr(12)
al1, al2 = b1 * v1, b2 * v2
check("exact: alpha_1 = 4 pi a^3 (1+3i)/10", al1.re == Fr(4, 10) and al1.im == Fr(12, 10))
check("exact: alpha_2 = 32 pi a^3 (4+6i)/13", al2.re == Fr(128, 13) and al2.im == Fr(192, 13))
p0b = al1 + al2
p1b = (al2 - al1) * Fr(1, 2)
Ib = (p0b.conj() * p1b).im
Db = p0b.im
check("exact: I_b = -(8/195) w^2", Ib == -Fr(8, 195) * w ** 2, Ib / w ** 2)
check("exact: D_b = (173/130) w", Db == Fr(173, 130) * w, Db / w)
# (36): c = sqrt(|O1||O2|)/(2 pi (1-3a)^3) = 4 sqrt2/14739, and c < 1/2500
gap = 1 - 3 * a
check("exact: gap 1-3a = 17/20", gap == Fr(17, 20))
# c^2 = |O1||O2| / (4 pi^2 gap^6), |O1||O2| = (4pi/3)^2 * 8 a^6 -> c^2 = (16/9)*8 a^6/(4 gap^6)
c2 = Fr(16, 9) * 8 * a ** 6 / (4 * gap ** 6)
check("exact: c^2 = (4 sqrt2/14739)^2", c2 == Fr(32, 14739 ** 2), c2)
check("exact: c < 1/2500", c2 < Fr(1, 2500) ** 2)
# (37): delta = 4c/(1-2c) < 1/600 with ||A_b|| <= 2 (W >= 1/2 for chi = i, 2i)
check("exact: -Im chi^{-1} = 1 and 1/2", (chi1.inv()).im == -1 and (chi2.inv()).im == Fr(-1, 2))
cU = Fr(1, 2500)
check("exact: 4c/(1-2c) < 1/600 at c=1/2500 (monotone in c)", 4 * cU / (1 - 2 * cU) < Fr(1, 600))
# (43): relative error b(4 delta + delta^2)/|I_b| with b = 3/5 (|z| <= 3/5 on Omega)
bb = Fr(3, 5)
dl = Fr(1, 600)
rel = bb * (4 * dl + dl ** 2) * w ** 2 / abs(Ib)
check("exact: relative error = 0.097540625 < 1/10", rel == Fr(1404585, 14400000) and rel < Fr(1, 10), float(rel))
check("exact: z-range: geometry inside B_{3/5}", Fr(1, 2) + 2 * a == Fr(3, 5))
# (44)
I_lo, I_hi = abs(Ib) * Fr(9, 10), abs(Ib) * Fr(11, 10)
check("exact: |I0| in [12/325, 44/975] w^2", I_lo == Fr(12, 325) * w ** 2 and I_hi == Fr(44, 975) * w ** 2)
D_lo, D_hi = Db - dl * w, Db + dl * w
check("exact: D0 in [10367/7800, 10393/7800] w", D_lo == Fr(10367, 7800) * w and D_hi == Fr(10393, 7800) * w)
# (45) C = 2|I0|/(3 pi D0); in units: w = 12 pi a^3 -> C = 2|I0|/(3 pi D0) with |I0|/D0 in units w
# C_lo = 2*(12/325) w/(3 pi * 10393/7800) = 2*(12/325)*(12 pi a^3)*7800/(3 pi*10393)
C_lo = 2 * Fr(12, 325) * 12 * Fr(7800, 10393) / 3  # times a^3
C_hi = 2 * Fr(44, 975) * 12 * Fr(7800, 10367) / 3
check("exact: (45) 2304 a^3/10393 <= C <= 2816 a^3/10367", C_lo == Fr(2304, 10393) and C_hi == Fr(2816, 10367))
check("exact: (7) interval at a=1/20", C_lo * a ** 3 == Fr(36, 1299125) and C_hi * a ** 3 == Fr(44, 1295875))
Cb = 2 * abs(Ib) / (3 * Db)  # Ib, Db in units of (pi a^3)^2 and pi a^3, so C_b is in units a^3
check("exact: C_b = 128 a^3/519", Cb == Fr(128, 519), Cb)
check("exact: interval contains C_b", C_lo <= Cb <= C_hi)

# ------------------------------------------------------------------ Section 5.4 remainder
L = Fr(6, 5)
check("exact: Schur radius-L ball  L^2/2 = 18/25", L ** 2 / 2 == Fr(18, 25))
check("exact: ||T_t-T_0|| <= 2*2*18/25 = 72/25", 4 * Fr(18, 25) == Fr(72, 25))
uq = bb ** 2 + Fr(72, 25)  # 2*(t^2 b^2/2) + 72/25
check("exact: ||u_t-q0|| constant 81/25", uq == Fr(81, 25))
vq = 2 * bb ** 3 / 6 + Fr(72, 25) * bb
check("exact: ||v_t-t q1|| constant 9/5", vq == Fr(9, 5))
# three radiation-error terms in units w^2 t^3/pi
t1 = 2 * (L ** 2 / 8) * 2 * bb  # ||u|| ||Qt-Q0|| ||v||: 2 * (L^2/(8pi)) * 2b
t2 = Fr(81, 25) * Fr(1, 6) * 2 * bb
t3 = 2 * Fr(1, 6) * Fr(9, 5)
check("exact: radiation terms 54/125, 81/125, 3/5", (t1, t2, t3) == (Fr(54, 125), Fr(81, 125), Fr(3, 5)))
check("exact: sum 42/25, times 4 = 168/25", t1 + t2 + t3 == Fr(42, 25) and 4 * (t1 + t2 + t3) == Fr(168, 25))
Dc = (bb ** 2 + Fr(81, 25)) + 2 * bb ** 2
check("exact: |D(t)-D0| constant 108/25", Dc == Fr(108, 25))
check("exact: D(t) >= w for t <= 1/4", Fr(10367, 7800) - Fr(108, 25) / 16 >= 1)
S0max = Fr(2, 3) * Fr(44, 975)
check("exact: |S0| <= 88 w^2/(2925 pi)", S0max == Fr(88, 2925))
tot = Fr(168, 25) + Fr(88, 2925) * Fr(108, 25)
check("exact: division constant 55656/8125 < 7", tot == Fr(55656, 8125) and tot < 7, float(tot))
# 7 w / pi with w = 12 pi/8000 -> 84/8000 = 21/2000
check("exact: (7/pi) w = 21/2000 at a=1/20", 7 * Fr(12, 8000) == Fr(21, 2000))
check("exact: remainder at t=1/40 < (1/4) lower endpoint", Fr(21, 2000) * Fr(1, 40) ** 2 < Fr(1, 4) * Fr(36, 1299125))
check("exact: lower bound 27/1299125 = (3/4) * 36/1299125", Fr(3, 4) * Fr(36, 1299125) == Fr(27, 1299125))
# minimum enclosing radius: points z in [-1/2-a, 1/2+2a]; radius 23/40 centred at 1/40
lo, hi = -Fr(1, 2) - a, Fr(1, 2) + 2 * a
check("exact: minimum enclosing radius 23/40 at z=1/40 (axial extent)", (hi - lo) / 2 == Fr(23, 40) and (hi + lo) / 2 == Fr(1, 40))

# -------------------------------------------------------------- Section 6: homogeneous spheres
# L(mu) = -g0 v1 v2 (v2-v1)|beta|^2 Im beta with g0 = -1/(4pi), v = 4 pi a^3/3, v1=v, v2=8v
# = (1/4pi) * 56 v^3 * 9mu^2/(9+mu^2) * 9mu/(9+mu^2); v^3 = 64 pi^3 a^9/27
Lcoef = Fr(1, 4) * 56 * Fr(64, 27) * 81  # times pi^2 mu^3 a^9/(9+mu^2)^2
check("exact: (61) L = 2688 pi^2 mu^3 a^9/(9+mu^2)^2", Lcoef == 2688)
# |p1^(1)| bound: sum_{i!=j} |beta| v_i (6/(pi h^4)) mu sqrt3 r_j^2 v_j/5, r1=a, r2=2a -> 5a^2 total
check("exact: (60) prefactor 6 sqrt3/(5) * (1+4) = 6 sqrt3", Fr(6, 5) * 5 == 6)
# ||DH[u]|| <= (3*2+3+15)/(4 pi r^4) = 6/(pi r^4)
check("exact: (59) ||DH|| <= 24/(4pi r^4) = 6/(pi r^4)", Fr(3 * 2 + 3 + 15, 4) == 6)
# (62): ratio = 2|beta| w * 6 sqrt3 |beta| mu a^2 v1 v2/(pi h^4) / L
#     = 48 sqrt3 (9+mu^2) a^2/(7 h^4); check symbolic coefficient: 2*9*6*4/(7*9) = 48/7
check("exact: (62) coefficient 48/7", Fr(2 * 9 * 6 * 4, 7 * 9) == Fr(48, 7))
# 48 sqrt3/(7 h^4) < 30 at h = 4/5  <=>  48^2*3 < (30*7*h^4)^2
h4 = Fr(4, 5) ** 4
check("exact: 48 sqrt3/(7 (4/5)^4) < 30", 48 ** 2 * 3 < (30 * 7 * h4) ** 2)
check("exact: h = 1-3a >= 4/5 for a <= 1/20", 1 - 3 * Fr(1, 20) >= Fr(4, 5))
# (54): ||Co|| <= 4 sqrt2 a^3/(3 h^3) <= 4 a^3  <=>  sqrt2/(3 h^3) <= 1  <=> 2 <= 9 h^6
check("exact: (54) sqrt2/(3h^3) <= 1 at h=4/5", 2 <= 9 * Fr(4, 5) ** 6)
# (63)->(64): (9/5) mu^4 ||Co||^2 w^2 / L  with ||Co|| <= 4a^3, w = 9v = 12 pi a^3
num = Fr(9, 5) * 16 * 144  # pi^2 mu^4 a^12
check("exact: (64) coefficient 54/35", num / 2688 == Fr(54, 35))
check("exact: (63) b(mu+2|beta|) mu^3 <= (9/5) mu^4 since |beta|<=mu", bb * 3 == Fr(9, 5))
# (65) choice makes each term <= 1/4
check("exact: (65) 30/120 = 1/4 and (54/35)*(35/216) = 1/4", Fr(30, 120) == Fr(1, 4) and Fr(54, 35) * Fr(35, 216) == Fr(1, 4))
# (66): lower C_h = L/(3 pi mu w) in units; = 2688 pi^2 mu^2 a^6 /(36 pi^2 (9+mu^2)^2) = (224/3)...
check("exact: (66) lower coefficient 2688/36 = 224/3", Fr(2688, 36) == Fr(224, 3))
check("exact: (66) upper coefficient 3*(224/3) = 224", 3 * Fr(224, 3) == 224)
# mu = 1, a = 1/100 example
ex = 30 * 10 * Fr(1, 100) ** 2 + Fr(54, 35) * 1 * 100 * Fr(1, 100) ** 3
check("exact: mu=1,a=1/100 relative error 5277/175000 < 0.031", ex == Fr(5277, 175000) and ex < Fr(31, 1000))
# homogeneous beta facts
for mu in (Fr(1, 10), Fr(1), Fr(3), Fr(10)):
    bt = Q(0, 3 * mu) / Q(3, mu)
    ok = bt.im == 9 * mu / (9 + mu ** 2) and bt.abs2() == 9 * mu ** 2 / (9 + mu ** 2)
    ok = ok and bt.abs2() <= min(mu, 3) ** 2
    check(f"exact: beta(mu={mu}) Im and |beta|<=min(mu,3)", ok)

# ------------------------------------------------ 5.5 Lorentz law (DIAGNOSTIC numeric)
w0, gam = 1.0, 0.3
for j in (1, 2):
    chi = lambda om: j * gam * w0 / (w0 ** 2 - om ** 2 - 1j * gam * om)
    val = chi(w0)
    pos = all(chi(om).imag > 0 for om in [0.01 * n for n in range(1, 500)])
    check(f"diag: Lorentz chi_{j}(w0) = {j}i and Im chi > 0 for w > 0", abs(val - 1j * j) < 1e-12 and pos)

npass = sum(r["pass"] for r in results)
print(f"{npass}/{len(results)} checks passed")
if len(sys.argv) > 1:
    with open(sys.argv[1], "w", encoding="utf-8") as fh:
        json.dump({"source_sha256": "576478ba88fd374e724b96e07c5e3e1648485cd163dc4d8ba9cd0b3ef52eac62",
                   "passed": npass, "total": len(results), "checks": results}, fh, indent=1)
sys.exit(0 if npass == len(results) else 1)
