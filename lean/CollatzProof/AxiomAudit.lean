/-
  Axiom audit for the theorems cited in `discoveries-paper/`.

  Build with:   lake build CollatzProof.AxiomAudit

  Each `#print axioms` below must report exactly
      [propext, Classical.choice, Quot.sound]
  i.e. the ambient kernel axioms only -- no `sorry`, no custom axioms.
  Any other output means a paper is overclaiming and must be corrected.

  Last run: all four report kernel-only axioms.
-/
import CollatzProof.KodamaCollatz
import CollatzProof.KodamaFermat
import CollatzProof.MicroscopeDescent

-- Thm "exactly one odd m in [0,2^k) with v2(3^r m - 1) >= k"  (03-geometric-law, EM Thm 2.2)
#print axioms geometric_distribution_informal
#print axioms unique_inverse_mod
#print axioms modular_solution_odd

-- Orbit formula for a = 2^e+1  (02-fermat-bases, EM eq. (3))
#print axioms CollatzProof.orbit_formula_fermat

-- The general one-step law, EVERY odd base a (a-1 = 2^e*q, q odd):
--   nu2(a*n+1) = e  and  step_a a (2^(s+e)*m - 1) = a*2^s*m - q
#print axioms CollatzProof.step_a_general

-- The characterisation, BOTH directions in the kernel: closed form <-> q = 1.
-- (Previously only (<=) was certified and the converse was proved by hand.)
#print axioms CollatzProof.closed_form_iff_fermat
#print axioms CollatzProof.fermat_iff_pow_two

-- Descent atlas (MicroscopeDescent.lean, 1398 auto-formalized theorems): three samples,
-- first, middle and last. The whole file has no `sorry`.
#print axioms CollatzProof.descent_m8_5
#print axioms CollatzProof.step4_m8192_2271
#print axioms CollatzProof.descent_m16384_8193
