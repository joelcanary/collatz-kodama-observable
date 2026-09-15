"""Experimental evidence for the Kodama observable, reproduced from scratch.

For odd n, iterate the accelerated map x -> (3x+1)/2^v until x = 1, with K odd
steps and S = total 2-adic valuation. The EXACT decomposition
    x_k = 3^k n / 2^{S_k} + R_k,   R_0 = 0,  R_{k+1} = (3 R_k + 1) / 2^{v_{k+1}}
gives at termination (x_K = 1)
    R(n) = 1 - 3^K n / 2^S,        delta(n) = S - K log2(3) - log2(n) = -log2(1 - R(n)),
and, equivalently, delta(n) = sum over the odd orbit terms x_i (x_i > 1) of log2(1 + 1/(3 x_i)).

This script scans every odd n <= N, records the maximum of delta (= maximum of R),
the champion, the running maximum per decade, and a histogram of R. It is a
finite computation: it supports the CONJECTURE delta(n) < 0.33 (i.e. R(n) < 0.2021)
and proves nothing beyond the scanned range.

Usage: python kodama_scan.py N [PROCESOS]      e.g. python kodama_scan.py 100000000 8
Output: kodama_scan_N.json (summary).

EXACTNESS. Every comparison in the scan is an integer comparison: R(n) =
(2^S - 3^K n) / 2^S is kept as the pair (num, S), "R(a) > R(b)" is tested as
num_a * 2^S_b > num_b * 2^S_a, the histogram bin is floor(200 num / 2^S), and
the threshold R > 0.1877 (the top list) is 10000 num > 1877 * 2^S. The champion
and the plateau order therefore do not depend on floating point; delta(n) is
computed in floating point ONLY for display (it is a monotone function of R).
Before 15-Sep-2026 the scan compared delta as a double: same champion, same
plateau, but the verdict rested on floats; now it does not.
"""
import json
import math
import os
import sys
import time
import multiprocessing as mp
from fractions import Fraction

LOG2_3 = math.log2(3)


def orbit_KS(n):
    """(K, S) for odd n: number of accelerated steps and total valuation until x = 1."""
    K = S = 0
    x = n
    while x != 1:
        y = 3 * x + 1
        v = (y & -y).bit_length() - 1
        S += v
        x = y >> v
        K += 1
    return K, S


def delta_of(n, K, S):
    """Display only: delta = S - K log2(3) - log2(n) as a double."""
    return S - K * LOG2_3 - math.log2(n)


def R_num(n, K, S):
    """Numerator of R(n) = 1 - 3^K n / 2^S over the denominator 2^S (exact integer)."""
    return (1 << S) - 3 ** K * n


def R_mayor(a, b):
    """R(a) > R(b) exactly, for a = (num_a, S_a), b = (num_b, S_b)."""
    return a[0] * (1 << b[1]) > b[0] * (1 << a[1])


def scan_chunk(args):
    lo, hi = args
    best = (-1, 0, 0, 0, 0)         # (num, S, n, K, S): R = num / 2^S, exact
    hist = [0] * 60                 # R in [0, 0.30) in bins of 0.005, exact bins
    top = []
    for n in range(lo | 1, hi, 2):
        if n < 3:
            continue
        K, S = orbit_KS(n)
        num = R_num(n, K, S)
        if R_mayor((num, S), (best[0], best[1])):
            best = (num, S, n, K, S)
        b = (200 * num) >> S            # floor(R / 0.005) exactly
        if 0 <= b < 60:
            hist[b] += 1
        if 10000 * num > 1877 << S:     # R > 0.1877  (delta > 0.2999...)
            top.append((num, S, n, K, S))
    return best, hist, top


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 6
    P = int(sys.argv[2]) if len(sys.argv) > 2 else max(1, os.cpu_count() - 1)
    t0 = time.time()
    chunk = max(200_000, N // (P * 40))
    tareas = [(lo, min(lo + chunk, N + 1)) for lo in range(1, N + 1, chunk)]
    best = (-1, 0, 0, 0, 0); hist = [0] * 60; top = []
    por_decada = {}
    with mp.Pool(P) as pool:
        for (b, h, t), (lo, hi) in zip(pool.imap(scan_chunk, tareas), tareas):
            if R_mayor((b[0], b[1]), (best[0], best[1])):
                best = b
            hist = [x + y for x, y in zip(hist, h)]
            top.extend(t)
            dec = len(str(hi - 1)) - 1
            if dec not in por_decada or R_mayor((b[0], b[1]), (por_decada[dec][0], por_decada[dec][1])):
                por_decada[dec] = (b[0], b[1], b[2], b[3], b[4])
    num, _, n, K, S = best
    d = delta_of(n, K, S)
    R_exact = Fraction(num, 1 << S)
    assert R_exact == 1 - Fraction(3 ** K * n, 2 ** S)
    # exact descending order of R (ties broken by n), no floats involved
    import functools
    top.sort(key=functools.cmp_to_key(lambda a, b: -1 if R_mayor(a, b) else (1 if R_mayor(b, a) else (a[2] > b[2]) - (a[2] < b[2]))))
    por_decada = {k: (delta_of(v[2], v[3], v[4]), v[2]) for k, v in por_decada.items()}
    out = {
        "N": N, "odd_scanned": N // 2, "seconds": round(time.time() - t0, 1),
        "champion": {"n": n, "K": K, "S": S, "delta": d, "R": float(R_exact),
                     "R_exact": str(R_exact.limit_denominator(10 ** 12)) if R_exact.denominator > 10 ** 30 else str(R_exact)},
        "max_delta_by_decade": {("10^%d" % k): {"delta": v[0], "n": v[1]} for k, v in sorted(por_decada.items())},
        "top": [{"n": t[2], "delta": delta_of(t[2], t[3], t[4]), "K": t[3], "S": t[4], "R_exact": str(Fraction(t[0], 1 << t[1]))} for t in top[:20]],
        "hist_R_bins_0.005": hist,
        "conjecture": "delta(n) < 0.33 for all odd n > 1 (equivalently R(n) < 0.2021); supported up to N, not proved",
        "exact": "all comparisons are integer comparisons on R(n) = (2^S - 3^K n)/2^S; delta is display only",
    }
    json.dump(out, open("kodama_scan_%d.json" % N, "w"), indent=1)
    print("N=%d: champion n=%d  delta=%.6f  R=%.6f  (K=%d, S=%d)  in %.0fs" % (N, n, d, float(R_exact), K, S, time.time() - t0))
    for k, v in sorted(por_decada.items()):
        print("  up to 10^%d: max delta %.6f at n=%d" % (k, v[0], v[1]))


if __name__ == "__main__":
    main()
