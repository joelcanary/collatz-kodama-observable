"""Recompute the 1000 decimal digits of C_Collatz in data/b401012.txt, exactly, and compare.

C_Collatz = 1 - Sum_{n>=1} 2^(-floor(n log2 3)) = 0.28627450232410874196... is OEIS A401012
(approved 16 November 2026); data/b401012.txt holds the same 1000 terms as the OEIS b-file
(offset 0: a(0) = 2 is the first digit after the point).

No floating point. Each exponent floor(n log2 3) is the e with 2^e <= 3^n < 2^(e+1). Summing the
terms with e <= K gives an upper bound for C; the rest of the series is at most 2^(1-K'), K' being
the first exponent past K, which gives a lower bound. Both bounds are dyadic rationals, both are
written in base 10, and a digit counts only where the two agree.

    python scripts/check_b401012.py
"""
import os
import sys

DIGITS = 1000
K = 3400                      # 2^-3400 < 10^-1020: twenty digits of margin

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def bounds():
    """Upper and lower bound of C * 2^(K' + 1), K' the first exponent above K."""
    exps, p = [], 1
    while True:
        p *= 3
        e = p.bit_length() - 1
        if e > K:
            break
        exps.append(e)
    top = e + 1
    D = 1 << top
    s = sum(D >> x for x in exps)          # the exponents are distinct, so this is exact
    hi = D - s
    lo = hi - 2 * (D >> e)                 # minus the tail bound 2 * 2^-e
    return lo, hi, top


def digits():
    lo, hi, top = bounds()
    scale = 10 ** (DIGITS + 20)
    a = str((lo * scale) >> top).zfill(DIGITS + 20)
    b = str((hi * scale) >> top).zfill(DIGITS + 20)
    k = 0
    while k < len(a) and a[k] == b[k]:
        k += 1
    if k < DIGITS:
        sys.exit(f"only {k} digits are certified; raise K")
    return a[:DIGITS]


def main():
    want = digits()
    path = os.path.join(ROOT, "data", "b401012.txt")
    rows = [line.split() for line in open(path, encoding="utf-8") if line.strip() and not line.startswith("#")]
    bad = [r for r in rows if len(r) != 2 or not r[0].isdigit() or not r[1].isdigit()]
    if bad:
        sys.exit(f"malformed lines in data/b401012.txt: {bad[:3]}")
    if [int(r[0]) for r in rows] != list(range(DIGITS)):
        sys.exit("the indices must be 0..999, one per line")
    got = "".join(r[1] for r in rows)
    if got != want:
        k = next(i for i in range(DIGITS) if got[i] != want[i])
        sys.exit(f"digit a({k}) is {got[k]} in the file but {want[k]} by exact computation")
    print(f"ok  data/b401012.txt: all {DIGITS} digits of C_Collatz = 0.{want[:20]}... recomputed exactly")


if __name__ == "__main__":
    main()
