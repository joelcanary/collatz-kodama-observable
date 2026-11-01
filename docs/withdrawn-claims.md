# Withdrawn claims

This project announced, in earlier documents, more than it had proved. This page lists those
claims, where they appeared, what each rested on, and why it does not hold. It is kept
deliberately, next to the results that do hold, because a reader who finds the earlier
documents should be able to see the correction in the same place as the work.

| Claim | Where it appeared | What it rested on | Status |
|---|---|---|---|
| "The Collatz conjecture is proved." | README of the (then private) repository `kodama-observable`, July 2026; draft manuscripts titled *Finite Automata for Linear Recurrence Maps … and the Resolution of the 3x+1 Problem*. | A "finite automaton mod 24": the claim that the accelerated step depends only on `x mod 24`, verified on the 12 residue representatives. | **Withdrawn — false.** `v₂(3x+1)` is not a function of `x mod M` for any `M` (`papers/three-exact-results` §5 and `papers/structure-note` §5, with explicit witnesses: `x = 1` and `x = 25` are in the same class mod 24 and `step(1) = 1 ≠ 19 = step(25)`). Checking representatives proves nothing about the other members of the classes. |
| "`δ(n) < 0.33` for all odd `n > 1`" stated as a theorem ("structural bound"). | Draft *The Kodama Observable for Collatz Dynamics: A Structural Bound δ(n) < 0.33 …*; abstract of the Zenodo preprint 10.5281/zenodo.21087140. | The exact identity `δ(n) = Σ log₂(1 + 1/(3xᵢ))` and a decomposition of the sum into "suffix, transient and huge" components, plus computation. | **Withdrawn as a theorem; kept as a conjecture.** The identity is exact but presupposes that the orbit terminates (it sums over the orbit); the bound on the sum was never proved. It is supported by an exhaustive scan to `10⁸` (this repository) and, per the earlier documents, to `10⁹`. |
| "The orbit reaches 1 iff `R_k < ½` for some `k`" / "iff `R_k = 0` for some `k`". | Draft manuscripts (definition of the observable). | A misreading of the residual `R_k`. | **Withdrawn.** `R_k > 0` for every `k ≥ 1` by its recurrence, and the value of `R_k` at an intermediate step decides nothing; the residual is an exact bookkeeping identity, not a convergence criterion. |
| "`n = 993` is the unique global maximiser of `R`." | Zenodo preprint, `COLLATZ_STATUS.md` of the old repository ("proven unique"). | Exhaustive scan. | **Not a theorem.** It is the champion conjecture (`papers/structure-note` §8), checked to `10⁸` here; a universal statement over an infinite set cannot be established by a finite scan. |
| "Twelve theorems", "197 auto-certified descent classes" presented as progress on the conjecture. | Zenodo abstract; old README. | The descent atlas (real, machine-checked: 1398 theorems in `lean/CollatzProof/MicroscopeDescent.lean`). | **Reframed.** The atlas is correct and is included, but it establishes the conjecture only on a set of density `1 − ρ(j) → 1` and, by the ceiling proposition (`papers/structure-note` §7), no finite atlas can cover all `n`. It is evidence of the method's reach and of its limit, not of the conjecture. |
| A "Collatz–Riemann consistency" and a "Collatz–Hodge morphism". | Exploratory Lean files and JSON notes of the campaign (not shipped here). | Numerical coincidences. | **Withdrawn, not shipped.** Those files contain `sorry` and were never certified; they are excluded from this repository on purpose. |

## What survives

Everything in the README's "What is proved" table, and the observable as an exact identity
with a conjecture attached. The corrections above are not a retreat from the mathematics;
they are the mathematics, applied to the project's own earlier claims. The limitative theorem
that refutes the first row was proved by this project, in the same month, once the
representatives-versus-classes error was noticed — and it is, in our view, the most useful
single statement in the repository, because the error it closes is easy to make and recurs
in the literature around the problem.

## For the record

* Zenodo preprint v2, 2026-07-01, DOI 10.5281/zenodo.21087140 — superseded by this
  repository; not deleted.
* *Experimental Mathematics* (Taylor & Francis), manuscript 261387702, submitted 2026-07-01
  (*Three Exact Results …*, which already contained the limitative result and made no
  conjecture-level claim) — declined.
* Repository `kodama-observable` (private) — superseded by this one.
