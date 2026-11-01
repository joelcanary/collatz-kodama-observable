"""
Self-contained reproduction of every number in the Prize 3 paper.
Run:  python verify_prize3.py       (takes ~1 min)

The game: odd n > 1 has two moves, n -> odd_part(3n+1) and n -> odd_part(3n-1).
Position 1 is terminal; the player who moves to 1 wins. Impartial game, so every
position is N (WIN, player to move wins) or P (LOSE), by Zermelo backward induction.
"""
import sys
from collections import deque
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

v2 = lambda x: (x & -x).bit_length() - 1
LIM = 500_000

# forward moves and reverse graph restricted to the box
kids, rev = {}, {}
for n in range(3, LIM + 1, 2):
    cs = [(3 * n + s) >> v2(3 * n + s) for s in (+1, -1)]
    kids[n] = cs
    for c in cs:
        if c <= LIM:
            rev.setdefault(c, []).append(n)

# Zermelo retrograde: 1 is P; N if some child is P; P if all children are N.
lab, dep = {1: "P"}, {1: 0}
left = {n: len(kids[n]) for n in kids}   # unresolved children count, for P-detection
mx = {}
q = deque([1])
while q:
    x = q.popleft()
    for p in rev.get(x, ()):
        if p in lab:
            continue
        if lab[x] == "P":                # p has a move to a P -> p is N
            lab[p], dep[p] = "N", 1 + dep[x]
            q.append(p)
        else:                            # x is N; p becomes P only if ALL children are N
            left[p] -= 1
            mx[p] = max(mx.get(p, 0), dep[x])
            if left[p] == 0:
                lab[p], dep[p] = "P", 1 + mx[p]
                q.append(p)

odd = (LIM + 1) // 2
res = len(lab)
wins = [n for n in lab if lab[n] == "N"]
wd = [dep[n] for n in wins]

print(f"odd positions n <= {LIM:,} : {odd:,}")
print(f"resolved               : {res:,}  ({100*res/odd:.1f}%)")
print(f"  WIN  (N)             : {len(wins):,}  ({100*len(wins)/res:.1f}% of resolved)")
print(f"  LOSE (P)             : {res-len(wins):,}  ({100*(res-len(wins))/res:.1f}%)")
print(f"maximal optimal depth  : {max(wd)}")
print(f"mean optimal depth     : {sum(wd)/len(wd):.1f}")

nolose = sum(1 for n in wins if n != 1
             and not any(lab.get(c) == "P" for c in kids.get(n, ())))
print(f"WIN with no LOSE child : {nolose}   (must be 0)")

print("\nNo 2-adic structure -- pure residue classes mod 2^j:")
for j in range(1, 13):
    m = 1 << j
    byres = {}
    for n, L in lab.items():
        if n != 1:
            byres.setdefault(n % m, set()).add(L)
    pure = sum(1 for r in byres if len(byres[r]) == 1)
    print(f"  j={j:>2}  (mod {m:>5}) : {pure} pure of {len(byres)}")

from collections import Counter
loses = [n for n in lab if lab[n] == "P" and n != 1]
print("\nLOSE positions are equidistributed:")
print(f"  mod 3: {dict(sorted(Counter(n % 3 for n in loses).items()))}")
print(f"  mod 4: {dict(sorted(Counter(n % 4 for n in loses).items()))}")
print(f"  mod 8: {dict(sorted(Counter(n % 8 for n in loses).items()))}")
