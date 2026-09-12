"""
Self-contained reproduction of EVERY number in the paper
"Three Exact Results Arising from Collatz-Type Dynamics".
Run:  python verify.py

No floating point where exactness is claimed: valuation statistics use Fraction,
the constant C_Collatz uses 80-digit Decimal. Each line prints [OK] or [FAIL].
"""
import sys, math
from decimal import Decimal, getcontext
from fractions import Fraction as F
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
getcontext().prec = 120

v2 = lambda x: (x & -x).bit_length() - 1
def check(c, m):
    print(("  [OK]   " if c else "  [FAIL] ") + m)

print("== (i) Valuation statistics ==")
# equidistribution / rotation law: v2(a*n+1) >= k  <=>  n = -a^{-1} (mod 2^k)
bad = sum(1 for a in range(3, 40, 2) for k in range(1, 9) for n in range(1, 1 << 11, 2)
          if (v2(a * n + 1) >= k) != (n % (1 << k) == (-pow(a, -1, 1 << k)) % (1 << k)))
check(bad == 0, f"rotation law, every odd a<40, k<=8 ({bad} bad)")
# geometric law, mean 2
bad = sum(1 for K in range(3, 16)
          if F(sum(min(v2(3 * n + 1), K) for n in range(1, 1 << K, 2)), 1 << (K - 1))
          != 2 - F(1, 1 << (K - 1)))
check(bad == 0, f"E[v2(3n+1)] = 2 - 2^(1-K) exact, mean -> 2 ({bad} bad)")
# variance 2: E[(v+)^2] = 6 - (4K+6)2^-K
bad = sum(1 for K in range(3, 17)
          if F(sum(min(v2(3 * n + 1), K) ** 2 for n in range(1, 1 << K, 2)), 1 << (K - 1))
          != 6 - F(4 * K + 6, 1 << K))
check(bad == 0, f"E[(v+)^2] = 6 - (4K+6)2^-K exact, Var -> 2 ({bad} bad)")
# covariance -1: min=1 always, so v+ * v- = max
b1 = sum(1 for n in range(3, 1 << 16, 2) if min(v2(3 * n + 1), v2(3 * n - 1)) != 1)
b2 = sum(1 for n in range(3, 1 << 16, 2)
         if v2(3 * n + 1) * v2(3 * n - 1) != max(v2(3 * n + 1), v2(3 * n - 1)))
K = 16; N = 1 << (K - 1)
epm = F(sum(min(v2(3*n+1), K) * min(v2(3*n-1), K) for n in range(1, 1 << K, 2)), N)
ep = F(sum(min(v2(3*n+1), K) for n in range(1, 1 << K, 2)), N)
check(b1 == 0 and b2 == 0 and abs(epm - ep*ep + 1) < F(1, 1 << 10),
      f"min(v+,v-)=1 always; v+*v-=max; Cov -> -1 ({float(epm-ep*ep):.5f})")

print("\n== (ii) Fermat bases ==")
def step_a(a, x):
    y = a * x + 1
    return y >> v2(y)
cf_true = []
for a in range(3, 1000, 2):
    e = v2(a - 1); q = (a - 1) >> e
    ok = all(step_a(a, (1 << (r + 1)) * m - 1) == a * (1 << (r + 1 - e)) * m - 1
             for m in range(1, 201, 2) for r in range(e, e + 8))
    if ok:
        cf_true.append(a)
check(cf_true == [3, 5, 9, 17, 33, 65, 129, 257, 513],
      f"closed form exactly for a=2^e+1: {cf_true}")

print("\n== (iii) The transcendental constant ==")
L3 = Decimal(3).ln() / Decimal(2).ln()
C = Decimal(1) / 2 - sum(Decimal(2) ** (-int(n * L3)) for n in range(2, 301))
check(str(C).startswith("0.28627450232410874196"), f"C_Collatz = {str(C)[:24]}")
check(Decimal(2) ** (-int(301 * L3)) < Decimal(2) ** -475, "tail below 2^-475")
w = [int(Decimal(n) * L3) - int(Decimal(n - 1) * L3) for n in range(1, 4001)]
check(set(w) == {1, 2}, f"Beatty gaps = {sorted(set(w))}")
comp = {k: len({tuple(w[i:i+k]) for i in range(len(w)-k)}) for k in range(1, 9)}
check(all(comp[k] == k + 1 for k in comp), f"factor complexity p(k)=k+1, k<=8")
# continued fraction
x = C; cf = []
for _ in range(5):
    a = int(x); cf.append(a)
    if x == a: break
    x = 1 / (x - a)
check(cf == [0, 3, 2, 36, 2056], f"continued fraction [0;3,2,36,2056,...] -> {cf}")
# not a known constant
check(abs(float(C) - (0.25 + math.pi / 1000)) > 1e-3,
      "C is NOT 1/4+pi/1000 (no spurious coincidence)")

print("\n== The limitative fact (no finite-residue reduction) ==")
step = lambda x: (3 * x + 1) >> v2(3 * x + 1)
bv = sum(1 for x in range(1, 4000, 2) if v2(3*x+1) != v2(3*(x+24)+1))
bs = sum(1 for x in range(1, 4000, 2) if step(x) % 24 != step(x + 24) % 24)
check(bv == 500 and bs == 1959, f"mod 24: v2 differs {bv}/2000, step differs {bs}/2000")

print("\nDone. Lean-certified items build with `lake build CollatzProof.KodamaCollatz "
      "CollatzProof.KodamaFermat` and pass `#print axioms` (kernel-only).")
