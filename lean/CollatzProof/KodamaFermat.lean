/-
# KodamaFermat.lean — the Kodama orbit formula for Fermat-type bases a = 2^e + 1

Discovery & framework: Joel Cruz Cabrera (ORCID 0009-0005-4048-1237).
Original result of the Kodama-Observable project.

Generalizes the 3x+1 orbit formula (the e = 1 case) to every base a = 2^e + 1:
for the ax+1 accelerated map,
    step_a^i (2^(r+1)·m - 1) = a^i · 2^(r+1 - i·e) · m - 1     (i·e ≤ r, m odd).
The single-step heart is `step_a_fermat`. No dependence on the Collatz conjecture.
-/

import CollatzProof.KodamaCollatz

namespace CollatzProof

/-- The ax+1 accelerated (Syracuse) map. -/
def step_a (a n : ℕ) : ℕ := (a * n + 1) / 2 ^ ν₂ (a * n + 1)

/-- Iterate of `step_a` (recurses on the inner argument, like `iter`). -/
def iter_a (a : ℕ) : ℕ → ℕ → ℕ
  | 0,     x => x
  | s + 1, x => iter_a a s (step_a a x)

theorem iter_a_succ_apply (a j x : ℕ) : iter_a a (j + 1) x = step_a a (iter_a a j x) := by
  induction j generalizing x with
  | zero => simp [iter_a]
  | succ k ih => rw [iter_a, ih, iter_a]

/-- **Single-step identity for a = 2^e + 1.** With the 2-power dropping by `e`:
    `step_a a (a^i · 2^(s+e) · m - 1) = a^(i+1) · 2^s · m - 1`  (s ≥ 1, m odd). -/
theorem step_a_fermat (e i s m a : ℕ) (ha : a = 2 ^ e + 1) (he : e ≥ 1)
    (hs : s ≥ 1) (hm : m % 2 = 1) (hm_pos : m ≥ 1) :
    step_a a (a ^ i * 2 ^ (s + e) * m - 1) = a ^ (i + 1) * 2 ^ s * m - 1 := by
  subst ha
  have hNpos : (2 ^ e + 1) ^ i * 2 ^ (s + e) * m ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hIpos : (2 ^ e + 1) ^ (i + 1) * 2 ^ s * m ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- Key identity:  a·(a^i·2^(s+e)·m − 1) + 1 = 2^e · (a^(i+1)·2^s·m − 1)
  have hkey : (2 ^ e + 1) * ((2 ^ e + 1) ^ i * 2 ^ (s + e) * m - 1) + 1
      = 2 ^ e * ((2 ^ e + 1) ^ (i + 1) * 2 ^ s * m - 1) := by
    zify [hNpos, hIpos]
    ring
  -- The inner factor is odd (s ≥ 1 ⇒ a^(i+1)·2^s·m even)
  have hEven : (2 ^ e + 1) ^ (i + 1) * 2 ^ s * m % 2 = 0 := by
    have h2s : (2 : ℕ) ∣ 2 ^ s := dvd_pow_self 2 (by omega : s ≠ 0)
    have hdvd : (2 : ℕ) ∣ (2 ^ e + 1) ^ (i + 1) * 2 ^ s * m := (h2s.mul_left _).mul_right m
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hInnerOdd : ((2 ^ e + 1) ^ (i + 1) * 2 ^ s * m - 1) % 2 = 1 := by omega
  have hInnerNe : (2 ^ e + 1) ^ (i + 1) * 2 ^ s * m - 1 ≠ 0 := by omega
  -- ν₂(a·n+1) = e
  have hν₂ : ν₂ ((2 ^ e + 1) * ((2 ^ e + 1) ^ i * 2 ^ (s + e) * m - 1) + 1) = e := by
    rw [hkey, ν₂_mul (2 ^ e) _ (by positivity) hInnerNe, ν₂_pow_two' e, ν₂_odd _ hInnerOdd]
    omega
  -- Conclude
  unfold step_a
  rw [hν₂, hkey, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ e)]

/-- **General single-step law — every odd base `a`, not just Fermat-type.**

Write `a - 1 = 2^e * q` with `q` odd. Then for `s ≥ 1` and `m` odd,
    `ν₂(a·n + 1) = e` exactly   and   `step_a a (2^(s+e)·m − 1) = a·2^s·m − q`.

This is the heart of the characterisation: the right-hand side lands back in the family
`2^j·m' − 1` exactly when `q = 1`.  `step_a_fermat` is the special case `q = 1`. -/
theorem step_a_general (a e q s m : ℕ) (ha : a = 2 ^ e * q + 1) (hq : q % 2 = 1)
    (he : e ≥ 1) (hs : s ≥ 1) (hm : m % 2 = 1) (hm_pos : m ≥ 1) :
    step_a a (2 ^ (s + e) * m - 1) = a * 2 ^ s * m - q := by
  subst ha
  have hqpos : q ≥ 1 := by omega
  have hNpos : 2 ^ (s + e) * m ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2sm : 2 ^ s * m ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- a·2^s·m ≥ a ≥ q + 1 > q, so the ℕ subtraction is honest
  have hIge : (2 ^ e * q + 1) * 2 ^ s * m ≥ q + 1 := by
    have h2e : 2 ^ e ≥ 1 := Nat.one_le_two_pow
    calc (2 ^ e * q + 1) * 2 ^ s * m
        = (2 ^ e * q + 1) * (2 ^ s * m) := by ring
      _ ≥ (2 ^ e * q + 1) * 1 := Nat.mul_le_mul_left _ h2sm
      _ = 2 ^ e * q + 1 := by ring
      _ ≥ 1 * q + 1 := by exact Nat.add_le_add_right (Nat.mul_le_mul_right q h2e) 1
      _ = q + 1 := by ring
  -- Key identity:  a·(2^(s+e)·m − 1) + 1 = 2^e · (a·2^s·m − q)
  have hkey : (2 ^ e * q + 1) * (2 ^ (s + e) * m - 1) + 1
      = 2 ^ e * ((2 ^ e * q + 1) * 2 ^ s * m - q) := by
    zify [hNpos, show q ≤ (2 ^ e * q + 1) * 2 ^ s * m by omega]
    ring
  -- The bracket is (even) − (odd) = odd
  have hEven : (2 ^ e * q + 1) * 2 ^ s * m % 2 = 0 := by
    have h2s : (2 : ℕ) ∣ 2 ^ s := dvd_pow_self 2 (by omega : s ≠ 0)
    have hdvd : (2 : ℕ) ∣ (2 ^ e * q + 1) * 2 ^ s * m := (h2s.mul_left _).mul_right m
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hInnerOdd : ((2 ^ e * q + 1) * 2 ^ s * m - q) % 2 = 1 := by omega
  have hInnerNe : (2 ^ e * q + 1) * 2 ^ s * m - q ≠ 0 := by omega
  have hν₂ : ν₂ ((2 ^ e * q + 1) * (2 ^ (s + e) * m - 1) + 1) = e := by
    rw [hkey, ν₂_mul (2 ^ e) _ (by positivity) hInnerNe, ν₂_pow_two' e, ν₂_odd _ hInnerOdd]
    omega
  unfold step_a
  rw [hν₂, hkey, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ e)]

/-- **The characterisation, both directions, in the kernel.**

The closed form `step_a a (2^(s+e)·m − 1) = a·2^s·m − 1` holds **iff** `q = 1`, i.e. iff
`a − 1` is a power of two, i.e. iff `a = 2^e + 1` is Fermat-type.

(⇐) is `step_a_fermat`; (⇒) is the new content: any odd part `q ≠ 1` in `a − 1` survives
into the image and pushes it out of the family. -/
theorem closed_form_iff_fermat (a e q s m : ℕ) (ha : a = 2 ^ e * q + 1) (hq : q % 2 = 1)
    (he : e ≥ 1) (hs : s ≥ 1) (hm : m % 2 = 1) (hm_pos : m ≥ 1) :
    step_a a (2 ^ (s + e) * m - 1) = a * 2 ^ s * m - 1 ↔ q = 1 := by
  have hgen := step_a_general a e q s m ha hq he hs hm hm_pos
  have hqpos : q ≥ 1 := by omega
  have h2sm : 2 ^ s * m ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hIge : a * 2 ^ s * m ≥ q + 1 := by
    subst ha
    have h2e : 2 ^ e ≥ 1 := Nat.one_le_two_pow
    calc (2 ^ e * q + 1) * 2 ^ s * m
        = (2 ^ e * q + 1) * (2 ^ s * m) := by ring
      _ ≥ (2 ^ e * q + 1) * 1 := Nat.mul_le_mul_left _ h2sm
      _ = 2 ^ e * q + 1 := by ring
      _ ≥ 1 * q + 1 := by exact Nat.add_le_add_right (Nat.mul_le_mul_right q h2e) 1
      _ = q + 1 := by ring
  rw [hgen]
  constructor
  · intro h; omega
  · intro h; rw [h]

/-- **Corollary: `a = 2^e + 1` is exactly the Fermat-type condition.**
    `a - 1` is a power of two iff the odd part `q` of `a - 1` is `1`. -/
theorem fermat_iff_pow_two (a e q : ℕ) (ha : a = 2 ^ e * q + 1) (hq : q % 2 = 1) :
    a = 2 ^ e + 1 ↔ q = 1 := by
  constructor
  · intro h
    have heq : 2 ^ e * q = 2 ^ e := by omega
    have heq1 : 2 ^ e * q = 2 ^ e * 1 := by rw [mul_one]; exact heq
    exact Nat.eq_of_mul_eq_mul_left (by positivity) heq1
  · intro h; rw [ha, h, Nat.mul_one]

/-- **Orbit formula for a = 2^e + 1.**
    `iter_a a i (2^(r+1)·m − 1) = a^i · 2^(r+1 − i·e) · m − 1`  for `i·e ≤ r`. -/
theorem orbit_formula_fermat (e r m a : ℕ) (ha : a = 2 ^ e + 1) (he : e ≥ 1)
    (hm : m % 2 = 1) (hm_pos : m ≥ 1) (i : ℕ) (hi : i * e ≤ r) :
    iter_a a i (2 ^ (r + 1) * m - 1) = a ^ i * 2 ^ (r + 1 - i * e) * m - 1 := by
  induction i with
  | zero => simp [iter_a]
  | succ j ih =>
    have hrel : (j + 1) * e = j * e + e := by ring
    have hj : j * e ≤ r := by omega
    have hs1 : r + 1 - (j + 1) * e ≥ 1 := by omega
    have hsplit : r + 1 - j * e = (r + 1 - (j + 1) * e) + e := by omega
    rw [iter_a_succ_apply, ih hj, hsplit,
        step_a_fermat e j (r + 1 - (j + 1) * e) m a ha he hs1 hm hm_pos, pow_succ]

end CollatzProof
