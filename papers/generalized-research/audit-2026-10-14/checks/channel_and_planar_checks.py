"""Independent checks of the 10 October 2026 generalized-research manuscript.

Source audited: papers/generalized-research/manuscript/OQ7_generalized_research_2026-10-10.pdf
(SHA-256 3f01036ff6bc99939b1f2b1a8a205ac4e755188930535db1336d841ca7d377bf).

Standard library only; the manuscript's NumPy/SciPy scripts were not recovered and
are not reused.  Exact statements use fractions or algebraic identities; random and
grid searches are labelled DIAGNOSTIC and are adversarial tests, not proofs.
Theorem 5.1 itself is checked separately by kernel replay of OQ7.theorem51.

Run:  python -I channel_and_planar_checks.py [output.json]
"""

import cmath
import json
import math
import random
import sys
from fractions import Fraction as Fr

random.seed(20261014)
results = []


def check(name, ok, detail=""):
    results.append({"check": name, "pass": bool(ok), "detail": str(detail)})
    if not ok:
        print("FAIL", name, detail)


# ----------------------------------------------------------------- small complex linear algebra
def mat(n, m=None, f=lambda i, j: 0):
    m = n if m is None else m
    return [[f(i, j) for j in range(m)] for i in range(n)]


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def ct(A):
    return [[A[j][i].conjugate() for j in range(len(A))] for i in range(len(A[0]))]


def tr(A):
    return [[A[j][i] for j in range(len(A))] for i in range(len(A[0]))]


def mv(A, x):
    return [sum(A[i][k] * x[k] for k in range(len(x))) for i in range(len(A))]


def inner(x, y):  # conjugate-linear in the first argument
    return sum(a.conjugate() * b for a, b in zip(x, y))


def norm(x):
    return math.sqrt(sum(abs(c) ** 2 for c in x))


def eye(n):
    return mat(n, f=lambda i, j: 1.0 + 0j if i == j else 0j)


def hermitian_eig_max(H, iters=400):
    """Largest eigenvalue of a Hermitian PSD-shifted matrix by power iteration on H + sI."""
    n = len(H)
    s = sum(abs(H[i][j]) for i in range(n) for j in range(n)) + 1.0
    Hs = [[H[i][j] + (s if i == j else 0) for j in range(n)] for i in range(n)]
    x = [complex(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(n)]
    for _ in range(iters):
        y = mv(Hs, x)
        ny = norm(y)
        x = [c / ny for c in y]
    return inner(x, mv(Hs, x)).real - s


def opnorm(A):
    return math.sqrt(max(0.0, hermitian_eig_max(mm(ct(A), A))))


def random_symmetric_contraction(n, scale_to=None):
    M = mat(n, f=lambda i, j: complex(random.gauss(0, 1), random.gauss(0, 1)))
    S = [[(M[i][j] + M[j][i]) / 2 for j in range(n)] for i in range(n)]
    nrm = opnorm(S)
    target = random.uniform(0.2, 1.0) if scale_to is None else scale_to
    return [[c * target / nrm for c in row] for row in S]


def random_unit(n):
    x = [complex(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(n)]
    nx = norm(x)
    return [c / nx for c in x]


# ===================================================== Section 2: scalar two-port envelope
def envelope(T, a):
    b = 1 - T - a
    ac = (1 - T * T) / 2
    if a < ac:
        y0 = math.sqrt(1 - 2 * a) - T
        return 2 * math.sqrt(max(0.0, b * b - y0 * y0))
    return 2 * b


# exact identity (10): F(x) = (y+T)^2 - (1-2a) with y = sqrt(b^2-x^2), F = a^2 - x^2 - 2T(b - y)
for _ in range(200):
    T = random.random()
    a = random.uniform(0, 1 - T)
    b = 1 - T - a
    x = random.uniform(0, b)
    y = math.sqrt(b * b - x * x)
    F1 = a * a - x * x - 2 * T * (b - y)
    F2 = (y + T) ** 2 - (1 - 2 * a)
    if abs(F1 - F2) > 1e-12:
        check("identity (10)", False, (T, a, x))
        break
else:
    check("algebra: identity (10) F(x) = (y+T)^2-(1-2a) on 200 random points", True)

# DIAGNOSTIC: random symmetric 2x2 contractions never exceed the envelope
viol = 0.0
for _ in range(4000):
    S = random_symmetric_contraction(2, scale_to=random.uniform(0.3, 1.0))
    rL, t, rR = S[0][0], S[0][1], S[1][1]
    T = abs(t) ** 2
    AL, AR = 1 - abs(rL) ** 2 - T, 1 - abs(rR) ** 2 - T
    a = (AL + AR) / 2
    if a < -1e-12 or T > 1 + 1e-12:
        continue
    viol = max(viol, abs(AL - AR) - envelope(T, max(a, 0.0)))
check("diag: 4000 random reciprocal two-ports obey Prop. 2.2 envelope", viol < 1e-9, viol)
# the attaining matrix (8) at an active target
T, a = 0.48, 0.32
b = 1 - T - a
y0 = math.sqrt(1 - 2 * a) - T
x0 = math.sqrt(b * b - y0 * y0)
d = x0
S0 = [[math.sqrt(b - d), math.sqrt(T)], [math.sqrt(T), -math.sqrt(b + d)]]
Adef = [[(1 if i == j else 0) - sum(S0[k][i] * S0[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
detA = Adef[0][0] * Adef[1][1] - Adef[0][1] * Adef[1][0]
check("algebra: matrix (8) attains envelope with det(I-S^T S)=0 at T=12/25,a=8/25",
      abs(detA) < 1e-14 and abs((Adef[0][0] - Adef[1][1]) - envelope(T, a)) < 1e-14, (detA, envelope(T, a)))

# ===================================================== Theorem 6.2: X - X^2/4
viol = 0.0
for _ in range(1500):
    n = random.choice((2, 3, 4))
    S = random_symmetric_contraction(n)
    # lossless reciprocal reference: symmetric unitary  S0 = U U^T
    U = random_symmetric_contraction(n, scale_to=1.0)  # replaced below by a genuine symmetric unitary
    # build symmetric unitary via Takagi form: O D O^T with O real orthogonal (Gram-Schmidt) and |D| = 1
    vecs = []
    for _k in range(n):
        v = [random.gauss(0, 1) for _ in range(n)]
        for q in vecs:
            pr = sum(vi * qi for vi, qi in zip(v, q))
            v = [vi - pr * qi for vi, qi in zip(v, q)]
        nv = math.sqrt(sum(vi * vi for vi in v))
        vecs.append([vi / nv for vi in v])
    O = [[vecs[j][i] for j in range(n)] for i in range(n)]
    Dg = [cmath.exp(1j * random.uniform(0, 2 * math.pi)) for _ in range(n)]
    S0 = [[sum(O[i][k] * Dg[k] * O[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
    u = random_unit(n)
    v = [c.conjugate() for c in mv(S0, u)]  # J0 u = conj(S0 u)
    def powers(x):
        Sx, S0x = mv(S, x), mv(S0, x)
        A = 1 - norm(Sx) ** 2
        X = 2 * inner(S0x, [p - q for p, q in zip(S0x, Sx)]).real
        return A, X
    Au, Xu = powers(u)
    Av, Xv = powers(v)
    viol = max(viol, abs(Xu - Xv), abs(Au - Av) - (Xu - Xu * Xu / 4))
check("diag: 1500 random reciprocal contractions, n=2..4, random symmetric-unitary reference: X(u)=X(J0u) and Thm 6.2",
      viol < 1e-9, viol)
# exact witness (48) at X = 1
t = 0.5
s = math.sqrt(1 - t * t)
S = [[0, t, 0], [t, 0, s], [0, s, 0]]
Sref = [[0, 1, 0], [1, 0, 0], [0, 0, 1]]
def col(Mx, j):
    return [Mx[i][j] for i in range(3)]
AU = 1 - sum(x * x for x in col(S, 0))
AV = 1 - sum(x * x for x in col(S, 1))
XU = 2 * sum(p * (p - q) for p, q in zip(col(Sref, 0), col(S, 0)))
check("algebra: witness (48) attains X - X^2/4 at X = 1", abs(abs(AU - AV) - (XU - XU ** 2 / 4)) < 1e-15 and abs(XU - 1) < 1e-15,
      (AU, AV, XU))

# ===================================================== Section 6.3 / Theorem 6.3: golden ratio
q = (math.sqrt(5) - 1) / 2
gam2 = math.sqrt(10 * math.sqrt(5) - 22)
h = 4 * q * q * (1 - q) / (1 + q)
check("algebra: h(q*) = 10 sqrt5 - 22 and gamma_2 = 0.6005662120", abs(h - (10 * math.sqrt(5) - 22)) < 1e-14 and abs(gam2 - 0.6005662120) < 1e-10, gam2)
# equality matrix (52)
wq, dq = 1 - q, q * math.sqrt(1 - q * q)
phi = 0.7
S = [[(wq + dq) * cmath.exp(1j * phi), q * q], [q * q, (wq - dq) * cmath.exp(-1j * phi)]]
rL, tq, rR = S[0][0], S[0][1], S[1][1]
AL, AR = 1 - abs(rL) ** 2 - abs(tq) ** 2, 1 - abs(rR) ** 2 - abs(tq) ** 2
Xq = 2 * (1 - tq.real)
Adef = [[(1 if i == j else 0) - sum(S[k][i].conjugate() * S[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
detq = (Adef[0][0] * Adef[1][1] - Adef[0][1] * Adef[1][0]).real
check("algebra: (52) attains gamma_2 with PSD defect (det = 0)", abs(abs(AL - AR) / Xq - gam2) < 1e-14 and abs(detq) < 1e-14 and min(AL, AR) >= -1e-15,
      (abs(AL - AR) / Xq, detq))
# DIAGNOSTIC: random reciprocal two-ports in vacuum-reference coordinates
best = 0.0
for _ in range(20000):
    S = random_symmetric_contraction(2, scale_to=random.uniform(0.5, 1.0))
    T_ = S[0][1]
    Xr = 2 * (1 - T_.real)
    if Xr <= 1e-9:
        continue
    AL = 1 - abs(S[0][0]) ** 2 - abs(T_) ** 2
    AR = 1 - abs(S[1][1]) ** 2 - abs(T_) ** 2
    best = max(best, abs(AL - AR) / Xr)
check("diag: 20000 random two-ports never exceed gamma_2", best <= gam2 + 1e-12, best)
# phase-adjusted Theorem 5.1 target T = q^4, a = 4q - 2: active, and D0 = gamma_2 * X at real t = q^2
Tg, ag = q ** 4, 4 * q - 2
check("algebra: target (q^4, 4q-2) strictly active; 1 - T^2 - 2a = q^7", ag > 0 and abs((1 - Tg ** 2 - 2 * ag) - q ** 7) < 1e-14)
check("algebra: envelope D0(q^4,4q-2) / (2(1-q^2)) = gamma_2", abs(envelope(Tg, ag) / (2 * (1 - q * q)) - gam2) < 1e-13,
      envelope(Tg, ag) / (2 * (1 - q * q)))
# reflectionless phase slab: normalized transmission phase m pi (1 - 1/n) covers the circle when m(1-1/sqrtP) >= 2
P = 1.21
m_ = math.ceil(2 / (1 - 1 / math.sqrt(P)))
check("algebra: phase slab range m(1-1/sqrtP) >= 2 gives >= 2 pi of phase", m_ * math.pi * (1 - 1 / math.sqrt(P)) >= 2 * math.pi)

# ===================================================== Theorem 6.4: two-layer vector construction
def slab(n, kh):
    r0 = (1 - n) / (1 + n)
    p = cmath.exp(1j * n * kh)
    rA = r0 * (1 - p * p) / (1 - r0 * r0 * p * p)
    tA = (1 - r0 * r0) * p / (1 - r0 * r0 * p * p)
    return rA, tA


def slab_transfer(n, kh):
    # independent route: field-state transfer (E, E'/(ik)) through a homogeneous layer, then boundary formulas
    th = n * kh
    F = [[cmath.cos(th), 1j * cmath.sin(th) / n], [1j * n * cmath.sin(th), cmath.cos(th)]]
    Wb = [[1, 1], [1, -1]]
    Wi = [[0.5, 0.5], [0.5, -0.5]]
    K = mm(mm(Wi, F), Wb)
    rL = -K[1][0] / K[1][1]
    tR = 1 / K[1][1]
    return rL, tR


dev = 0.0
for eta, kh in ((0.3, 1.1), (1.0, 2.5), (0.05, 7.0), (2.0, 0.4)):
    n = cmath.sqrt(1 + 1j * eta)
    rA, tA = slab(n, kh)
    rB, tB = slab_transfer(n, kh)
    dev = max(dev, abs(rA - rB), abs(tA - tB * cmath.exp(-1j * 0)))
check("independent: (54) slab coefficients equal the transfer-matrix route", dev < 1e-12, dev)
# flux identity A_x = k eta int |E_x|^2 dz  (Simpson on the exact interior field)
eta, kh = 0.4, 2.0
n = cmath.sqrt(1 + 1j * eta)
rA, tA = slab(n, kh)
Ax = 1 - abs(rA) ** 2 - abs(tA) ** 2
# interior field: E(z) = C+ e^{i n k z} + C- e^{-i n k z}, with E(0) = 1 + rA, E'(0)/(ik) = 1 - rA
Cp = ((1 + rA) + (1 - rA) / n) / 2
Cm = ((1 + rA) - (1 - rA) / n) / 2
N = 4000
integ = 0.0
for i in range(N + 1):
    zz = kh * i / N
    E = Cp * cmath.exp(1j * n * zz) + Cm * cmath.exp(-1j * n * zz)
    wgt = 1 if i in (0, N) else (4 if i % 2 else 2)
    integ += wgt * abs(E) ** 2
integ *= (kh / N) / 3
check("independent: flux identity A_x = k eta int |E|^2", abs(Ax - eta * integ) < 1e-10, (Ax, eta * integ))
# limit A_x(1/m, m^2) -> 1 and the quoted m = 128 values
def Ax_of(m):
    n = cmath.sqrt(1 + 1j / m)
    rA, tA = slab(n, m * m)
    return 1 - abs(rA) ** 2 - abs(tA) ** 2


Ax128 = Ax_of(128)
check("independent: m=128, t=1/2: A_R = (3/4)A_x = 0.7499971390", abs(0.75 * Ax128 - 0.7499971390) < 5e-10, 0.75 * Ax128)
tm = 1 - 1 / 128
check("independent: m=128, t=1-1/m: contrast (1+t)/2 A_x = 0.9960899503", abs((1 + tm) / 2 * Ax128 - 0.9960899503) < 5e-10,
      (1 + tm) / 2 * Ax128)
check("independent: A_x(1/m, m^2) increasing toward 1 (m = 8..512)",
      all(Ax_of(2 ** j) < Ax_of(2 ** (j + 1)) < 1 for j in range(3, 9)), [Ax_of(2 ** j) for j in range(3, 10)])
# wave plate: eigenvalues 1, 4 of 5/2 I - 3/2 V and H = -V, normalized transmission V
tt = 0.3
ss = math.sqrt(1 - tt * tt)
V = [[-tt, ss], [ss, tt]]
epsW = [[2.5 - 1.5 * V[0][0], -1.5 * V[0][1]], [-1.5 * V[1][0], 2.5 - 1.5 * V[1][1]]]
trW, detW = epsW[0][0] + epsW[1][1], epsW[0][0] * epsW[1][1] - epsW[0][1] * epsW[1][0]
check("algebra: wave-plate permittivity eigenvalues {1,4}", abs(trW - 5) < 1e-14 and abs(detW - 4) < 1e-14)
# full 4-port: right-incident y gives A_R = s^2 A_x; left-incident y gives A_L = 0; extinctions 2(1-t)
eta, kh = 0.5, 3.0
n = cmath.sqrt(1 + 1j * eta)
rA, tA = slab(n, kh)
Axx = 1 - abs(rA) ** 2 - abs(tA) ** 2
kd = math.pi
H = [[-V[i][j] for j in range(2)] for i in range(2)]
R = [[rA, 0], [0, 0]]
Dm = [[tA, 0], [0, cmath.exp(1j * kh)]]
HD = mm(H, Dm)
DH = mm(Dm, H)
HRH = mm(mm(H, R), H)
# (55) as printed (confirmed from PDF glyph layout, p. 19): S = [[R, DH], [HD, HRH]], channels (Lx, Ly, Rx, Ry).
# Plain pdftotext output lists matrix entries column by column; reading it row-wise swaps these blocks.
S4 = [[R[0][0], R[0][1], DH[0][0], DH[0][1]], [R[1][0], R[1][1], DH[1][0], DH[1][1]],
      [HD[0][0], HD[0][1], HRH[0][0], HRH[0][1]], [HD[1][0], HD[1][1], HRH[1][0], HRH[1][1]]]
sym = max(abs(S4[i][j] - S4[j][i]) for i in range(4) for j in range(4))
pas = 1 - opnorm(S4)
ph = cmath.exp(1j * (kh + kd))
S04 = [[0, 0, ph, 0], [0, 0, 0, ph], [ph, 0, 0, 0], [0, ph, 0, 0]]
def powers4(x):
    Sx, S0x = mv(S4, x), mv(S04, x)
    return 1 - norm(Sx) ** 2, 2 * inner(S0x, [p - q for p, q in zip(S0x, Sx)]).real
AL_, XL_ = powers4([0, 1, 0, 0])
AR_, XR_ = powers4([0, 0, 0, 1])
check("algebra: (55) symmetric and passive", sym < 1e-15 and pas > -1e-12, (sym, pas))
check("algebra: (53) A_L = 0, A_R = (1-t^2)A_x, X_L = X_R = 2(1-t)",
      abs(AL_) < 1e-14 and abs(AR_ - ss * ss * Axx) < 1e-14 and abs(XL_ - 2 * (1 - tt)) < 1e-13 and abs(XR_ - 2 * (1 - tt)) < 1e-13,
      (AL_, AR_, XL_, XR_))
# reversed-pair absorption matrix singular (Section 6.6)
Bdef = [[(1 if i == j else 0) - sum(S4[k][i].conjugate() * S4[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
check("algebra: absorption matrix on reversed y inputs is diag(0, (1-t^2)A_x)", abs(Bdef[1][1]) < 1e-14 and abs(Bdef[1][3]) < 1e-14,
      (Bdef[1][1], Bdef[1][3], Bdef[3][3]))

# ===================================================== Theorem 7.1: prescribed overlap
def delta_rho(rho, r):
    d = math.sqrt(1 - rho * rho)
    if r <= rho / 2:
        return d
    if r >= rho:
        return 1 - r * r
    # middle branch: solve r = r0(c) by bisection (r0 increasing on (0, rho))
    lo, hi = 0.0, rho
    for _ in range(200):
        c = (lo + hi) / 2
        r0 = (rho + c - 2 * rho * c * c) / (2 - rho * c - c * c)
        lo, hi = (c, hi) if r0 < r else (lo, c)
    c = (lo + hi) / 2
    lam = c * (rho - c) / (2 - rho * c - c * c)
    return d * (1 - lam * lam) * math.sqrt(1 - c * c)


# exact rational example (Section 7.4)
rho, c = Fr(4, 5), Fr(2, 5)
Dd = 2 - rho * c - c * c
check("exact: rho=4/5, c=2/5 -> r0 = 59/95, lambda = 2/19",
      (rho + c - 2 * rho * c * c) / Dd == Fr(59, 95) and c * (rho - c) / Dd == Fr(2, 19))
val = math.sqrt(1 - 0.64) * (1 - (2 / 19) ** 2) * math.sqrt(1 - 0.16)
check("algebra: Delta_{4/5}(72/95) = 1071 sqrt21/9025 < 3/5", abs(val - 1071 * math.sqrt(21) / 9025) < 1e-15 and val < 0.6, val)
check("algebra: bisection branch value matches closed form", abs(delta_rho(0.8, 59 / 95) - val) < 1e-12)
# continuity at both transitions
cont = max(abs(delta_rho(rr, rr / 2 + 1e-9) - math.sqrt(1 - rr * rr)) + abs(delta_rho(rr, rr - 1e-9) - (1 - rr * rr))
           for rr in (0.1, 0.4, 0.8, 0.95))
check("algebra: Delta_rho continuous at r = rho/2 and r = rho", cont < 1e-6, cont)
# certificate identities (64) for random (rho, c)
cert = 0.0
for _ in range(300):
    rho = random.uniform(0.02, 0.98)
    c = random.uniform(0.01, 0.99) * rho
    s = math.sqrt(1 - c * c)
    Dd = 2 - rho * c - c * c
    lam = c * (rho - c) / Dd
    th = math.acos(c) / 2
    O = [[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]]
    OT = tr(O)
    B0 = mm(mm(O, [[1, 0], [0, lam]]), OT)
    Zp = [[(rho + c) / 4, -s / (2 * (1 + lam))], [-s / (2 * (1 + lam)), (rho - c) / (4 * lam)]]
    Z = mm(mm(O, Zp), OT)
    Wm = [[(1 + rho) / 2, 0], [0, -(1 - rho) / 2]]
    lyap = mm(B0, Z)
    lyap = [[lyap[i][j] + mm(Z, B0)[i][j] - Wm[i][j] for j in range(2)] for i in range(2)]
    nu = -s / ((1 + lam) * c)
    E = [[0, 0.5], [0.5, 0]]
    Hm = [[Z[i][j] - nu * E[i][j] for j in range(2)] for i in range(2)]
    delta = (rho + c) / 4 + s * s / (2 * (1 + lam) * c)
    Htarget = mm(mm(O, [[delta, 0], [0, 0]]), OT)
    detZ = Z[0][0] * Z[1][1] - Z[0][1] ** 2
    r0 = Wm[0][0] * B0[0][0] + Wm[1][1] * B0[1][1]
    Q0 = mm(B0, B0)
    err = max(max(abs(lyap[i][j]) for i in range(2) for j in range(2)),
              max(abs(Hm[i][j] - Htarget[i][j]) for i in range(2) for j in range(2)),
              abs(detZ - Dd * (rho - c) / (16 * c * (1 - c * c))),  # (64): det Z = D(rho-c)/(16c(1-c^2))
              abs(r0 - (rho + c - 2 * rho * c * c) / Dd), abs(Q0[0][1] - (1 - lam * lam) * s / 2))
    cert = max(cert, err)
    if detZ <= 0 or Z[0][0] <= 0 or delta <= 0 or nu >= 0:
        cert = max(cert, 1.0)
check("algebra: (62)-(64) Lyapunov identity, H = delta O diag(1,0) O^T, Z > 0, nu < 0, r0 and h0 formulas (300 random)", cert < 1e-10, cert)

# DIAGNOSTIC adversarial search with reference S0 = I (reverse = complex conjugation)
def eval_pair(S, u):
    v = [z.conjugate() for z in u]
    rho = abs(sum(z * z for z in u))  # |<u, conj u>| = |u^T u|
    Su, Sv = mv(S, u), mv(S, v)
    Au, Av = 1 - norm(Su) ** 2, 1 - norm(Sv) ** 2
    X = 2 * (1 - inner(u, Su).real)
    return rho, X, abs(Au - Av)


worst = -1.0
for trial in range(2500):
    n = random.choice((2, 3, 4))
    S = random_symmetric_contraction(n, scale_to=random.choice((1.0, random.uniform(0.3, 1.0))))
    u = random_unit(n)
    rho, X, D = eval_pair(S, u)
    if rho >= 1 - 1e-9:
        continue
    worst = max(worst, D - delta_rho(rho, abs(1 - X / 2)))
check("diag: 2500 random complex symmetric contractions (n=2..4) obey Theorem 7.1", worst < 1e-9, worst)
# hill-climb from random starts toward violations
worst_hc = -1.0
for start in range(60):
    n = random.choice((2, 3))
    S = random_symmetric_contraction(n, scale_to=1.0)
    u = random_unit(n)
    def gap(S, u):
        rho, X, D = eval_pair(S, u)
        return D - delta_rho(rho, abs(1 - X / 2)) if rho < 1 - 1e-9 else -1
    g = gap(S, u)
    step = 0.2
    for it in range(400):
        Mp = mat(n, f=lambda i, j: complex(random.gauss(0, step), random.gauss(0, step)))
        Sn = [[S[i][j] + (Mp[i][j] + Mp[j][i]) / 2 for j in range(n)] for i in range(n)]
        nr = opnorm(Sn)
        if nr > 1:
            Sn = [[z / nr for z in row] for row in Sn]
        un = [z + complex(random.gauss(0, step), random.gauss(0, step)) for z in u]
        nu_ = norm(un)
        un = [z / nu_ for z in un]
        gn = gap(Sn, un)
        if gn > g:
            S, u, g = Sn, un, gn
        else:
            step *= 0.995
    worst_hc = max(worst_hc, g)
check("diag: 60 hill-climbs (400 steps each) find no violation of Theorem 7.1", worst_hc < 1e-7, worst_hc)
# witnesses attain each branch (in canonical real coordinates, reference J = diag(1,-1))
att = 0.0
for rho in (0.3, 0.6, 0.9):
    p, qq = math.sqrt((1 + rho) / 2), math.sqrt((1 - rho) / 2)
    d = math.sqrt(1 - rho * rho)
    for r in (rho / 4, 0.5 * (rho / 2 + rho), (rho + 1) / 2):
        a2, b2 = [p, qq], [p, -qq]
        if r <= rho / 2:
            cphi = 2 * r / rho
            Sw = [[complex(cphi, math.sqrt(1 - cphi ** 2)) * 0.5] * 2] * 2
            Sw = [[Sw[0][0], Sw[0][1]], [Sw[1][0], Sw[1][1]]]
            av, bv = a2, b2
        elif r < rho:
            lo, hi = 0.0, rho
            for _ in range(200):
                c = (lo + hi) / 2
                r0 = (rho + c - 2 * rho * c * c) / (2 - rho * c - c * c)
                lo, hi = (c, hi) if r0 < r else (lo, c)
            c = (lo + hi) / 2
            lam = c * (rho - c) / (2 - rho * c - c * c)
            th = math.acos(c) / 2
            O = [[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]]
            B0 = mm(mm(O, [[1, 0], [0, lam]]), tr(O))
            Sw = [[complex(B0[i][j]) for j in range(2)] for i in range(2)]
            av, bv = a2, b2
        else:
            wv = [0, 1]  # orthonormal frame for the input plane: a = e1', w = e2'
            # construct in R^3 with basis (a, g, f) as in the manuscript
            al_, be_ = math.sqrt(1 - r * r) / d, math.sqrt(r * r - rho * rho) / d
            # coordinates: a = (1,0,0), w = (0,1,0), e3 = (0,0,1); f = al w + be e3, g = be w - al e3
            A3 = [1, 0, 0]
            f3 = [0, al_, be_]
            g3 = [0, be_, -al_]
            Mloc = [[rho / r, math.sqrt(r * r - rho * rho) / r, 0], [math.sqrt(r * r - rho * rho) / r, -rho / r, 0], [0, 0, 0]]
            Bas = [A3, g3, f3]  # columns
            Sw = [[complex(sum(Bas[k][i] * Mloc[k][l] * Bas[l][j] for k in range(3) for l in range(3))) for j in range(3)] for i in range(3)]
            av = A3
            bv = [rho * 1, d * 1 * 1, 0]
            bv = [rho, d, 0]
        # evaluate with reference J: forward overlap Re<J a, S a> = Re<b, S a>, Delta = |A(a) - A(b)|
        Sa, Sb = mv(Sw, av), mv(Sw, bv)
        Delta = abs((1 - norm(Sa) ** 2) - (1 - norm(Sb) ** 2))
        rr = abs(inner([complex(z) for z in bv], Sa).real)
        att = max(att, abs(rr - r), abs(Delta - delta_rho(rho, r)), max(0.0, opnorm(Sw) - 1))
check("algebra: branch witnesses attain Delta_rho(r) (rho = 0.3, 0.6, 0.9; one r per branch)", att < 1e-9, att)

# ===================================================== Lemma 4.4: convexity and global tangent (DIAGNOSTIC)
f = lambda u: u * u - math.sin(u) ** 2
g = lambda u: math.sqrt(f(u))
Hf = lambda u: 2 * math.sin(u) ** 2 * f(u) - (u - math.sin(u) * math.cos(u)) ** 2
check("diag: H(u) >= 0 on (0, pi/2] (convexity numerator)", min(Hf(math.pi / 2 * i / 20000) for i in range(1, 20001)) >= -1e-15)
gp = lambda u: (u - math.sin(u) * math.cos(u)) / g(u)
tg = 1.0
for x in (0.01, 0.1, 0.2, 1 / 3):
    for i in range(1, 40001):
        v = math.pi * i / 40000
        tg = min(tg, g(v) - (g(x) + gp(x) * (v - x)))
check("diag: tangent at x in {0.01,0.1,0.2,1/3} lies below g on (0, pi]", tg >= -1e-12, tg)
check("diag: f(u) >= 4u^4/(3 pi^2) on (0, pi/2]", min(f(u) - 4 * u ** 4 / (3 * math.pi ** 2) for u in (math.pi / 2 * i / 20000 for i in range(1, 20001))) >= 0)

# ===================================================== Lemma 4.1 to the full distance pi/K (DIAGNOSTIC)
def fundamental(profile, k, h, steps=4000):
    """RK4 for s'' = -k^2 eps(z) s, s(0)=0, s'(0)=1 on [0,h]; profile: list of (z_end, eps)."""
    def eps_at(z):
        for zend, e in profile:
            if z <= zend:
                return e
        return profile[-1][1]
    s, ds = 0j, 1 + 0j
    dz = h / steps
    for i in range(steps):
        z = i * dz
        def F(z, y):
            return (y[1], -k * k * eps_at(z) * y[0])
        y = (s, ds)
        k1 = F(z, y)
        k2 = F(z + dz / 2, (y[0] + dz / 2 * k1[0], y[1] + dz / 2 * k1[1]))
        k3 = F(z + dz / 2, (y[0] + dz / 2 * k2[0], y[1] + dz / 2 * k2[1]))
        k4 = F(z + dz, (y[0] + dz * k3[0], y[1] + dz * k3[1]))
        s = s + dz / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0])
        ds = ds + dz / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])
    return s


minratio = 10.0
k = 1.0
for trial in range(120):
    P_ = random.uniform(1.05, 6.0)
    Q_ = random.uniform(0.01, 4.0)
    K = k * math.sqrt(P_)
    hmax = math.pi / K
    nl = random.randint(1, 6)
    cuts = sorted(random.uniform(0, hmax) for _ in range(nl - 1)) + [hmax]
    profile = [(zc, complex(random.uniform(1, P_), random.choice((0.0, random.uniform(0, Q_))))) for zc in cuts]
    hfrac = random.choice((0.5, 0.8, 0.95, 0.999))
    hh = hfrac * hmax
    sv = fundamental(profile, k, hh)
    minratio = min(minratio, abs(sv) / (math.sin(K * hh) / K))
check("diag: Lemma 4.1 |s(h)| >= sin(Kh)/K, 120 random stacks, h up to 0.999 pi/K", minratio >= 1 - 1e-6, minratio)

# ===================================================== Section 5.2 cubic logarithm coefficient
def expm2(A):
    nrm = max(abs(A[i][j]) for i in range(2) for j in range(2))
    sq = max(0, int(math.log2(nrm)) + 6) if nrm > 0 else 0
    As = [[A[i][j] / 2 ** sq for j in range(2)] for i in range(2)]
    R = eye(2)
    term = eye(2)
    for kk in range(1, 30):
        term = mm(term, As)
        term = [[term[i][j] / kk for j in range(2)] for i in range(2)]
        R = [[R[i][j] + term[i][j] for j in range(2)] for i in range(2)]
    for _ in range(sq):
        R = mm(R, R)
    return R


Pp, Qp = 4.0, 2.0
Am = [[0, 1j], [1j * Pp, 0]]
Bm = [[0, 0], [-Qp, 0]]
def Dxi(xi):
    E1 = expm2([[-Am[i][j] * xi / 2 for j in range(2)] for i in range(2)])
    E2 = expm2([[(Am[i][j] + Bm[i][j]) * xi for j in range(2)] for i in range(2)])
    return mm(mm(E1, E2), E1)
# (36) as printed (layout-mode p. 11): C3 = (1/12) [[0, -Q], [Q(P + 2iQ), 0]]
C3 = [[0, -Qp / 12], [Qp * (Pp + 2j * Qp) / 12, 0]]
errs = []
for xi in (1e-2, 5e-3):
    Dm_ = Dxi(xi)
    pred = [[(1 if i == j else 0) + xi * Bm[i][j] + xi ** 3 * C3[i][j] for j in range(2)] for i in range(2)]
    errs.append(max(abs(Dm_[i][j] - pred[i][j]) for i in range(2) for j in range(2)) / xi ** 4)
check("independent: D(xi) = I + xi B + xi^3 C3 + O(xi^4) (P=4,Q=2)", errs[1] < 5 and abs(errs[0] / errs[1] - 1) < 0.2, errs)
# c_m m^2 -> g0^4/(3Q^2) = 1/12 for g0 = kM = 1, Q = 2
def c_of(m):
    Dm_ = Dxi(1.0 / (Qp * m))
    F = eye(2)
    for _ in range(m):
        F = mm(Dm_, F)
    Sig = [[0, 1], [1, 0]]
    Dfx = mm(mm(ct(F), Sig), F)
    Dfx = [[Sig[i][j] - Dfx[i][j] for j in range(2)] for i in range(2)]
    return (Dfx[0][0] * Dfx[1][1] - Dfx[0][1] * Dfx[1][0]).real
vals = {m: c_of(m) * m * m for m in (8, 16, 32, 64)}
check("independent: m^2 c_m -> 1/12 (Table 2 column)", abs(vals[64] - 1 / 12) < 1e-4 and abs(vals[32] - 0.0833230479) < 1e-8, vals)

npass = sum(r["pass"] for r in results)
print(f"{npass}/{len(results)} checks passed")
if len(sys.argv) > 1:
    with open(sys.argv[1], "w", encoding="utf-8") as fh:
        json.dump({"source_sha256": "3f01036ff6bc99939b1f2b1a8a205ac4e755188930535db1336d841ca7d377bf",
                   "seed": 20261014, "passed": npass, "total": len(results), "checks": results}, fh, indent=1)
sys.exit(0 if npass == len(results) else 1)
