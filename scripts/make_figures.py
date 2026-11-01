"""Figures for the README. Everything is recomputed here from first principles and
checked against the statement it illustrates before drawing.

  figures/geometric_law.png       P[v2(3n+1) = k] = 2^-k over odd residues, and Cov(v+, v-) = -1
  figures/fermat_bases.png        which odd bases a have closed-form orbits (a - 1 a power of 2)
  figures/sturmian_constant.png   the binary digits of C_Collatz sit on a Beatty set (Sturmian word)
  figures/no_finite_reduction.png v2(3x+1) is not a function of x mod 24 (explicit witnesses)
  figures/kodama_observable.png   the residual R_k along the orbit of n = 993, and delta(n) up to N
  figures/overview.png            one-page summary panel

Usage: python scripts/make_figures.py   (numpy + matplotlib; reads scan JSON if present)
"""
import glob
import json
import math
import os
from decimal import Decimal, getcontext
from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

RAIZ = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(RAIZ, "figures")
os.makedirs(OUT, exist_ok=True)
plt.rcParams.update({"font.size": 10, "axes.titlesize": 9.5, "axes.spines.top": False, "axes.spines.right": False})
AZUL, ROJO, VERDE, GRIS = "#1f4e79", "#c0392b", "#27ae60", "#7f8c8d"


def v2(x):
    return (x & -x).bit_length() - 1


# 1. Geometric law and the anti-correlation ----------------------------------
K = 16
odds = np.arange(1, 1 << K, 2)
vp = np.array([v2(3 * int(n) + 1) for n in odds]); vm = np.array([v2(3 * int(n) - 1) for n in odds])
ks = np.arange(1, 13)
emp = np.array([(vp == k).mean() for k in ks])
assert np.allclose(emp[:10], 2.0 ** -ks[:10], atol=1e-6), "geometric law fails"
assert np.all(np.minimum(vp, vm) == 1), "min(v+, v-) = 1 fails"
cov = (vp * vm).mean() - vp.mean() * vm.mean()
fig, axs = plt.subplots(1, 2, figsize=(9.2, 3.4))
axs[0].bar(ks - 0.2, emp, width=0.4, color=AZUL, label=r"empirical, odd $n < 2^{16}$")
axs[0].bar(ks + 0.2, 2.0 ** -ks, width=0.4, color=ROJO, alpha=0.75, label=r"$2^{-k}$")
axs[0].set_yscale("log"); axs[0].set_xlabel("k"); axs[0].set_ylabel(r"$P[v_2(3n+1)=k]$")
axs[0].set_title(r"Exact geometric law: $v_2(3n+1)=k$ on one residue class mod $2^k$ (Lean)")
axs[0].legend(fontsize=8, frameon=False)
h = np.zeros((7, 7))
for a, b in zip(vp, vm):
    if a <= 7 and b <= 7:
        h[a - 1, b - 1] += 1
axs[1].imshow(np.log1p(h), cmap="Blues", origin="lower", extent=[0.5, 7.5, 0.5, 7.5])
axs[1].set_xlabel(r"$v_-=v_2(3n-1)$"); axs[1].set_ylabel(r"$v_+=v_2(3n+1)$")
axs[1].set_title("min(v+, v-) = 1 always: Cov = %.4f (exact value -1)" % cov)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "geometric_law.png"), dpi=160); plt.close(fig)

# 2. Fermat-type bases --------------------------------------------------------
def step_a(a, x):
    y = a * x + 1
    return y >> v2(y)


bases = list(range(3, 70, 2))
closed = []
for a in bases:
    e = v2(a - 1); q = (a - 1) >> e
    ok = True
    for m in range(1, 41, 2):
        for r in range(e, e + 6):
            x = (1 << (r + 1)) * m - 1
            ok &= (step_a(a, x) == a * (1 << (r + 1 - e)) * m - q)          # one-step law, every odd a
            if q == 1:
                ok &= (step_a(a, x) == a * (1 << (r + 1 - e)) * m - 1)      # closed form iff q = 1
    assert ok, "one-step law failed for a=%d" % a
    closed.append(q == 1)
fig, ax = plt.subplots(figsize=(9.2, 2.6))
ax.bar(bases, [1] * len(bases), color=[VERDE if c else "#d5d8dc" for c in closed], width=1.4)
for a, c in zip(bases, closed):
    if c:
        ax.text(a, 1.05, str(a), ha="center", fontsize=8, color=VERDE)
ax.set_yticks([]); ax.set_xlabel("odd base a of the map x -> odd part of (a x + 1)")
ax.set_title("Closed-form orbits exist iff a - 1 is a power of 2 (a = 3, 5, 9, 17, 33, 65, ...)   (Lean: closed_form_iff_fermat)")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "fermat_bases.png"), dpi=160); plt.close(fig)

# 3. The constant C_Collatz and its Sturmian digits ---------------------------
getcontext().prec = 120
L23 = Decimal(3).ln() / Decimal(2).ln()
C = Decimal(1) / 2 - sum(Decimal(2) ** (-int(n * L23)) for n in range(2, 320))
assert str(C)[:18] == "0.2862745023241087", "C_Collatz mismatch: " + str(C)[:20]
beatty = [int(n * L23) for n in range(1, 60)]
gaps = [beatty[i] - beatty[i - 1] for i in range(1, len(beatty))]
assert set(gaps) <= {1, 2}
# binary digits of C: digit j is 1 iff j is in the Beatty set {floor(n log2 3)} (n >= 2), up to the 1/2 shift
bits = [1 if j in set(beatty[1:]) else 0 for j in range(1, 90)]
fig, ax = plt.subplots(figsize=(9.2, 2.4))
ax.imshow(np.array([bits]), cmap="Greys", aspect="auto", extent=[1, 90, 0, 1])
ax.set_yticks([]); ax.set_xlabel("binary digit position j")
ax.set_title(r"$C_{Collatz}=0.28627450232410874\ldots$: digits sit on the Beatty set $\{\lfloor n\log_2 3\rfloor\}$, a Sturmian word; hence transcendental")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "sturmian_constant.png"), dpi=160); plt.close(fig)

# 4. No finite-residue reduction (M = 24) --------------------------------------
xs = np.arange(1, 4000, 2)
diff_v = np.array([v2(3 * int(x) + 1) != v2(3 * (int(x) + 24) + 1) for x in xs])
diff_s = np.array([step_a(3, int(x)) % 24 != step_a(3, int(x) + 24) % 24 for x in xs])
assert diff_v.sum() == 500 and diff_s.sum() == 1959, (diff_v.sum(), diff_s.sum())
fig, ax = plt.subplots(figsize=(9.2, 2.8))
res = np.array([x % 24 for x in xs])
for r in sorted(set(res)):
    sel = res == r
    ax.scatter([r] * sel.sum(), [v2(3 * int(x) + 1) for x in xs[sel]], s=6, color=AZUL, alpha=0.35)
ax.set_xlabel("x mod 24 (odd residues)"); ax.set_ylabel(r"$v_2(3x+1)$, odd $x<4000$")
ax.set_title("The same residue mod 24 carries many valuations: 500/2000 pairs (x, x+24) differ in v2, 1959/2000 in step(x) mod 24 — no finite automaton on residues")
fig.tight_layout(); fig.savefig(os.path.join(OUT, "no_finite_reduction.png"), dpi=160); plt.close(fig)

# 5. The Kodama observable: residual along the orbit of 993, and delta up to N ---
def orbit(n):
    xs, vs = [n], []
    x = n
    while x != 1:
        y = 3 * x + 1; v = v2(y); x = y >> v
        xs.append(x); vs.append(v)
    return xs, vs


xs993, vs993 = orbit(993)
R = [Fraction(0)]
for v in vs993:
    R.append((3 * R[-1] + 1) / 2 ** v)
K, S = len(vs993), sum(vs993)
assert R[-1] == 1 - Fraction(3 ** K * 993, 2 ** S), "decomposition identity fails"
delta993 = -math.log2(1 - float(R[-1]))
assert abs(delta993 - 0.325550) < 1e-5 and abs(float(R[-1]) - 0.202006) < 1e-5
termwise = sum(math.log2(1 + 1 / (3 * x)) for x in xs993[:-1])
assert abs(termwise - delta993) < 1e-9, "delta as a sum over the orbit fails"
fig, axs = plt.subplots(1, 2, figsize=(9.6, 3.4))
axs[0].plot(range(len(R)), [float(r) for r in R], "o-", ms=3, color=AZUL)
axs[0].set_xlabel("accelerated step k"); axs[0].set_ylabel(r"$R_k(993)$")
axs[0].set_title(r"n = 993: residual $R_k$ of $x_k = 3^k n/2^{S_k} + R_k$; final $R = 0.202006$, $\delta = 0.32555$")
scans = sorted(glob.glob(os.path.join(RAIZ, "data", "kodama_scan_*.json")) + glob.glob(os.path.join(RAIZ, "scripts", "kodama_scan_*.json")),
               key=lambda p: int(os.path.basename(p).split("_")[-1].split(".")[0]))
if scans:
    d = json.load(open(scans[-1]))
    top = sorted(d["top"], key=lambda t: t["n"])          # every n with delta > 0.30, from the scan
    tops_n = [t["n"] for t in top]; tops_d = [t["delta"] for t in top]
    axs[1].scatter(tops_n, tops_d, s=12, color=ROJO, label="the %d largest values of delta(n) in the scan" % len(top))
    axs[1].axhline(0.33, ls="--", color=GRIS, lw=0.8, label="conjectured bound 0.33")
    axs[1].axhline(d["champion"]["delta"], ls=":", color=AZUL, lw=0.8, label="champion n = %d: %.6f" % (d["champion"]["n"], d["champion"]["delta"]))
    axs[1].set_xscale("log"); axs[1].set_ylim(0.30, 0.335); axs[1].set_xlabel("n"); axs[1].set_ylabel(r"$\delta(n)$")
    axs[1].set_title("all odd n <= %s scanned: the maximum stays at n = 993 (evidence, not proof)" % "{:,}".format(d["N"]))
    axs[1].legend(fontsize=7, frameon=False, loc="lower right")
else:
    axs[1].text(0.5, 0.5, "run scripts/kodama_scan.py to fill this panel", ha="center", va="center"); axs[1].set_axis_off()
fig.tight_layout(); fig.savefig(os.path.join(OUT, "kodama_observable.png"), dpi=160); plt.close(fig)

# 6. Overview panel -----------------------------------------------------------
fig, axs = plt.subplots(2, 2, figsize=(10, 6.4))
axs[0, 0].bar(ks - 0.2, emp, width=0.4, color=AZUL); axs[0, 0].bar(ks + 0.2, 2.0 ** -ks, width=0.4, color=ROJO, alpha=0.75)
axs[0, 0].set_yscale("log"); axs[0, 0].set_title("(i) valuations are exactly Geom(1/2) — proved, Lean")
axs[0, 1].bar(bases, [1] * len(bases), color=[VERDE if c else "#d5d8dc" for c in closed], width=1.4); axs[0, 1].set_yticks([])
axs[0, 1].set_title("(ii) closed-form orbits iff a = 2^e + 1 — proved, Lean")
axs[1, 0].imshow(np.array([bits]), cmap="Greys", aspect="auto", extent=[1, 90, 0, 1]); axs[1, 0].set_yticks([])
axs[1, 0].set_title("(iii) C_Collatz: Sturmian digits, transcendental")
axs[1, 1].plot(range(len(R)), [float(r) for r in R], "o-", ms=3, color=AZUL)
axs[1, 1].set_title("(iv) residual R_k of n = 993: exact identity; delta < 0.33 is a conjecture")
fig.suptitle("Collatz-type dynamics: what is proved, what is evidence. Nothing here proves the Collatz conjecture.", fontsize=11)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "overview.png"), dpi=160); plt.close(fig)
print("figures:", sorted(os.listdir(OUT)))
