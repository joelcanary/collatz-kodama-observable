# The results, one by one

Notation: `v₂` is the 2-adic valuation, `step(x) = (3x+1)/2^{v₂(3x+1)}` on odd `x`, and for an
odd base `a`, `step_a(x) = odd part of (ax + 1)`.

## 1. The exact 2-adic law of the valuations

**Rotation law.** For every odd `a` and every `k ≥ 1`,
`v₂(an + 1) ≥ k ⟺ n ≡ −a⁻¹ (mod 2ᵏ)` — a single residue class, because `a` is a 2-adic unit.
Consequently, for `n` uniform on the odd residues mod `2ᴷ`, `P[v₂(an+1) = k] = 2⁻ᵏ` for
`k < K`: the law is `Geom(1/2)`, **independent of the base**; the base only rotates the class.

**Moments.** `E[v] = 2`, `E[v²] = 6 − (4K+6)2⁻ᴷ → 6`, so `Var(v) → 2` — exactly the geometric
values.

**Anti-correlation.** `3n+1` and `3n−1` are consecutive even numbers, so exactly one of them is
`≡ 2 (mod 4)`: `min(v₂(3n+1), v₂(3n−1)) = 1` identically. Hence `v₊v₋ = max(v₊, v₋)`,
`E[v₊v₋] → 3` and `Cov(v₊, v₋) = 3 − 2·2 = −1`. This is the quantitative form of the up/down
dichotomy of the two-sided map: when one branch rises sharply the other is forced to valuation 1.

**Scope.** These are statements about uniform residues, i.e. the exact form of the folklore
heuristic "expected factor 3/4 per step". They say nothing about any individual orbit; the
paper cites Althöfer–Zipproth's divergent map `n ↦ ⌊√2 n + 4⌋` as the standing reminder that a
negative mean drift decides nothing.

*Lean:* `unique_inverse_mod`, `modular_solution_odd`, `geometric_distribution_informal`
(`lean/CollatzProof/KodamaCollatz.lean`), rotation law certified for six bases.

## 2. Which bases have closed-form orbits

Write odd `x` uniquely as `x = 2^{r+1} m − 1` (`m` odd, `r = v₂(x+1) − 1`) and `a − 1 = 2^e q`
with `q` odd.

**One-step law** (every odd `a`, `r ≥ e`): `v₂(ax+1) = e` exactly and
`step_a(x) = a·2^{r+1−e} m − q`.

**Characterisation.** The image lands back in the family (`… − 1`) — so the law iterates to a
closed formula `xᵢ = aⁱ 2^{r+1−ie} m − 1` — **iff `q = 1`, i.e. iff `a = 2^e + 1`**: `3, 5, 9, 17, 33, 65, 129, 257, 513, …`
("Fermat-type" bases; the Fermat numbers are the sub-family `e = 2^k`). Collatz is the
smallest one, and by §1 the only one whose heuristic drift `log a − 2 log 2` is negative.

*Lean:* `step_a_general` (one-step law), `closed_form_iff_fermat` (both directions),
`fermat_iff_pow_two`, `orbit_formula_fermat` (`lean/CollatzProof/KodamaFermat.lean`).

## 3. A transcendental density constant

Counting odd integers whose first block does not immediately shrink gives

`C_Collatz = ½ − Σ_{n≥2} 2^{−⌊n log₂3⌋} = 0.28627450232410874196…`

The exponents `⌊n log₂3⌋` form a Beatty sequence of irrational slope; its gap word (gaps in
`{1, 2}`) is Sturmian (Morse–Hedlund), so the binary expansion of `C_Collatz` has factor
complexity `p(k) = k + 1`. Numbers with Sturmian expansions are transcendental
(Ferenczi–Mauduit 1997; alternatively Adamczewski–Bugeaud 2007). The same argument gives
transcendence of `C_a = 1 − Σ 2^{−⌊n log₂ a⌋}` for every `a` with `log₂ a` irrational.

*Checked exactly:* 80-digit value, gap alphabet, `p(k) = k+1` for `k ≤ 8`, continued fraction
`[0; 3, 2, 36, 2056, …]`; no match with standard constants.

## 4. No finite-residue reduction (limitative)

**Proposition.** For every modulus `M`, `v₂(3x+1)` is not a function of `x mod M`.

*Proof.* Write `M = 2^s M'`. `v₂(3x+1) ≥ s` is decided by `x mod 2^s`, but `v₂(3x+1) = s`
exactly is decided by the digit of `x` at position `s`, which `x mod M` does not see; by CRT
pick `x ≡ y (mod M)` with `3x+1 ≡ 2^s` and `3y+1 ≡ 0 (mod 2^{s+1})`. ∎

At `M = 24`, among the 2000 odd `x < 4000`: 500 pairs `(x, x+24)` differ in `v₂`, 1959 differ
in `step(x) mod 24`; least witness `x = 1, y = 25`. So the dynamics is **not** a finite automaton
on residues, and checking residue representatives establishes nothing about their classes.

## 5. The structural note: run lengths, dichotomy, orbit identities

* **Run-length law:** `v₂(x+1) − 1` is exactly the number of initial valuation-one steps.
* **2-adic resistance descent** for the two-sided map `3x ± 1`.
* **Exact orbit identity** `2^S = 3^A n + Σ_{i<A} 3^{A−1−i} 2^{S_i}` and the **logarithmic
  defect** `δ = Σ log₂(1 + 1/(3aᵢ)) > 0` (see `observable.md`).
* **Predecessor law mod 3:** `aᵢ ≡ 0 (mod 3)` has no odd predecessor; `v_{i−1}` is even iff
  `aᵢ ≡ 1`, odd iff `aᵢ ≡ 2 (mod 3)`. Corollary: the last odd term before `1` is
  `(4^m − 1)/3 ∈ {1, 5, 21, 85, …}` with `v_A = 2m` even, and the "modulus 6" pattern in the last
  pair is modulus 3 in disguise.
* **Descent atlas:** 197 minimal residue classes `n ≡ r (mod 2ʲ)` on which the orbit provably
  drops below `n` within `t` steps, found by exact tree walk and auto-formalized by orbit
  unrolling into 1398 Lean theorems (`MicroscopeDescent.lean`, no `sorry`, kernel axioms only —
  three sampled in `AxiomAudit.lean`). Exact descent densities `d(1) = ½, d(2) = d(3) = ¾, …,
  d(10) = 955/1024` (a recomputation of Terras's classical result, not a new theorem).
* **The ceiling:** the resistant fraction `ρ(j)` (classes whose `j` known bits do not decide
  descent) thins — `91/512, 805/8192, 7933/131072` at `j = 10, 15, 20` — but the resistant set
  grows without bound, and its ratios oscillate with the irrational rotation by `log₂3` (no
  geometric law fits, checked exactly). Hence: **enumeration of descent classes proves the
  conjecture for almost all `n` and for no finite `j` for all `n`.** With §4 this delimits the
  whole family of residue-class methods.

## 6. Althöfer's Prize 3: the game `3n ± 1`

In Althöfer's game (choose `3n+1` or `3n−1`, then halve), the question is whether some
residue structure decides who wins. Exact computation: **0 pure classes mod `2ʲ` for every
`j ≤ 12`**, and the LOSE positions are equidistributed mod 3, 4 and 8 (`verify_prize3.py`).
In contrast with the deterministic map (197 pure descent classes), the game has no 2-adic
structure at all. A closed negative result.

## What none of this is

A proof of the Collatz conjecture, or progress towards one beyond the "almost all" regime that
Terras and Tao already established by other means. Sections 1–3 are independent of the
conjecture; 4 and the ceiling are limitative; 5 is structure; the observable's bound is a
conjecture (`observable.md`).
