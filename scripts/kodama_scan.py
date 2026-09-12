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
Output: kodama_scan_N.json (summary) — exact rationals are used for R(n) of the
champion; the scan itself uses exact integers for K and S and floats only for delta.
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
    return S - K * LOG2_3 - math.log2(n)


def scan_chunk(args):
    lo, hi = args
    best = (-1.0, 0, 0, 0)          # (delta, n, K, S)
    hist = [0] * 60                 # R in [0, 0.30) in bins of 0.005
    top = []
    for n in range(lo | 1, hi, 2):
        if n < 3:
            continue
        K, S = orbit_KS(n)
        d = delta_of(n, K, S)
        if d > best[0]:
            best = (d, n, K, S)
        R = 1.0 - 2.0 ** (-d)
        b = int(R / 0.005)
        if 0 <= b < 60:
            hist[b] += 1
        if d > 0.30:
            top.append((d, n, K, S))
    return best, hist, top


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 6
    P = int(sys.argv[2]) if len(sys.argv) > 2 else max(1, os.cpu_count() - 1)
    t0 = time.time()
    chunk = max(200_000, N // (P * 40))
    tareas = [(lo, min(lo + chunk, N + 1)) for lo in range(1, N + 1, chunk)]
    best = (-1.0, 0, 0, 0); hist = [0] * 60; top = []
    por_decada = {}
    with mp.Pool(P) as pool:
        for (b, h, t), (lo, hi) in zip(pool.imap(scan_chunk, tareas), tareas):
            if b[0] > best[0]:
                best = b
            hist = [x + y for x, y in zip(hist, h)]
            top.extend(t)
            dec = int(math.log10(max(hi - 1, 10)))
            if b[0] > por_decada.get(dec, (-1.0, 0))[0]:
                por_decada[dec] = (b[0], b[1])
    d, n, K, S = best
    R_exact = 1 - Fraction(3 ** K * n, 2 ** S)
    top.sort(reverse=True)
    out = {
        "N": N, "odd_scanned": N // 2, "seconds": round(time.time() - t0, 1),
        "champion": {"n": n, "K": K, "S": S, "delta": d, "R": float(R_exact),
                     "R_exact": str(R_exact.limit_denominator(10 ** 12)) if R_exact.denominator > 10 ** 30 else str(R_exact)},
        "max_delta_by_decade": {("10^%d" % k): {"delta": v[0], "n": v[1]} for k, v in sorted(por_decada.items())},
        "top": [{"n": t[1], "delta": t[0], "K": t[2], "S": t[3]} for t in top[:20]],
        "hist_R_bins_0.005": hist,
        "conjecture": "delta(n) < 0.33 for all odd n > 1 (equivalently R(n) < 0.2021); supported up to N, not proved",
    }
    json.dump(out, open("kodama_scan_%d.json" % N, "w"), indent=1)
    print("N=%d: champion n=%d  delta=%.6f  R=%.6f  (K=%d, S=%d)  in %.0fs" % (N, n, d, float(R_exact), K, S, time.time() - t0))
    for k, v in sorted(por_decada.items()):
        print("  up to 10^%d: max delta %.6f at n=%d" % (k, v[0], v[1]))


if __name__ == "__main__":
    main()
