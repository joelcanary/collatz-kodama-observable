/-
# MicroscopeDescent.lean — descent classes discovered AND proved by the microscope.

Each theorem here was found by `microscope/` (models → signals → validation),
verified numerically to 10,000,000, and then AUTO-FORMALIZED by
`microscope/formalize.py` (orbit unrolling → Lean). No hand proof.

Author of the framework and results: Joel Cruz Cabrera (ORCID 0009-0005-4048-1237).
-/
import CollatzProof.KodamaCollatz

namespace CollatzProof

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5 (mod 8) ⇒ step^1(n) < n. -/
theorem descent_m8_5 (q : ℕ) (hq : 8 * q + 5 > 1) :
    step (8 * q + 5) < 8 * q + 5 := by
  have h_bound : step (8 * q + 5) ≤ 3 * q + 2 := by
    unfold step
    have h3n1 : 3 * (8 * q + 5) + 1 = 2 ^ 3 * (3 * q + 2) := by ring
    have hne : (3 * q + 2) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8 * q + 5) + 1) = 3 + ν₂ (3 * q + 2) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (3 * q + 2) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (3 * q + 2) (2 ^ ν₂ (3 * q + 2)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m16_3 (q : ℕ) : step (16 * q + 3) = 24 * q + 5 := by
  unfold step
  have h3n1 : 3 * (16 * q + 3) + 1 = 2 ^ 1 * (24 * q + 5) := by ring
  have h_odd : (24 * q + 5) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (16 * q + 3) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (24 * q + 5) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (24 * q + 5) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (24 * q + 5) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3 (mod 16) ⇒ step^2(n) < n. -/
theorem descent_m16_3 (q : ℕ) (hq : 16 * q + 3 > 1) :
    step (step (16 * q + 3)) < 16 * q + 3 := by
  rw [step_m16_3 q]
  have h_bound : step (24 * q + 5) ≤ 9 * q + 2 := by
    unfold step
    have h3n1 : 3 * (24 * q + 5) + 1 = 2 ^ 3 * (9 * q + 2) := by ring
    have hne : (9 * q + 2) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (24 * q + 5) + 1) = 3 + ν₂ (9 * q + 2) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (9 * q + 2) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (9 * q + 2) (2 ^ ν₂ (9 * q + 2)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m32_11 (q : ℕ) : step (32 * q + 11) = 48 * q + 17 := by
  unfold step
  have h3n1 : 3 * (32 * q + 11) + 1 = 2 ^ 1 * (48 * q + 17) := by ring
  have h_odd : (48 * q + 17) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (32 * q + 11) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (48 * q + 17) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (48 * q + 17) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (48 * q + 17) (by positivity)]

theorem step2_m32_11 (q : ℕ) : step (step (32 * q + 11)) = 36 * q + 13 := by
  rw [step_m32_11 q]
  unfold step
  have h3n1 : 3 * (48 * q + 17) + 1 = 2 ^ 2 * (36 * q + 13) := by ring
  have h_odd : (36 * q + 13) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (48 * q + 17) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (36 * q + 13) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (36 * q + 13) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (36 * q + 13) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 11 (mod 32) ⇒ step^3(n) < n. -/
theorem descent_m32_11 (q : ℕ) (hq : 32 * q + 11 > 1) :
    step (step (step (32 * q + 11))) < 32 * q + 11 := by
  rw [step2_m32_11 q]
  have h_bound : step (36 * q + 13) ≤ 27 * q + 10 := by
    unfold step
    have h3n1 : 3 * (36 * q + 13) + 1 = 2 ^ 2 * (27 * q + 10) := by ring
    have hne : (27 * q + 10) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (36 * q + 13) + 1) = 2 + ν₂ (27 * q + 10) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (27 * q + 10) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (27 * q + 10) (2 ^ ν₂ (27 * q + 10)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m32_17 (q : ℕ) : step (32 * q + 17) = 24 * q + 13 := by
  unfold step
  have h3n1 : 3 * (32 * q + 17) + 1 = 2 ^ 2 * (24 * q + 13) := by ring
  have h_odd : (24 * q + 13) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (32 * q + 17) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (24 * q + 13) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (24 * q + 13) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (24 * q + 13) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 17 (mod 32) ⇒ step^2(n) < n. -/
theorem descent_m32_17 (q : ℕ) (hq : 32 * q + 17 > 1) :
    step (step (32 * q + 17)) < 32 * q + 17 := by
  rw [step_m32_17 q]
  have h_bound : step (24 * q + 13) ≤ 9 * q + 5 := by
    unfold step
    have h3n1 : 3 * (24 * q + 13) + 1 = 2 ^ 3 * (9 * q + 5) := by ring
    have hne : (9 * q + 5) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (24 * q + 13) + 1) = 3 + ν₂ (9 * q + 5) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (9 * q + 5) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (9 * q + 5) (2 ^ ν₂ (9 * q + 5)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m32_23 (q : ℕ) : step (32 * q + 23) = 48 * q + 35 := by
  unfold step
  have h3n1 : 3 * (32 * q + 23) + 1 = 2 ^ 1 * (48 * q + 35) := by ring
  have h_odd : (48 * q + 35) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (32 * q + 23) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (48 * q + 35) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (48 * q + 35) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (48 * q + 35) (by positivity)]

theorem step2_m32_23 (q : ℕ) : step (step (32 * q + 23)) = 72 * q + 53 := by
  rw [step_m32_23 q]
  unfold step
  have h3n1 : 3 * (48 * q + 35) + 1 = 2 ^ 1 * (72 * q + 53) := by ring
  have h_odd : (72 * q + 53) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (48 * q + 35) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (72 * q + 53) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (72 * q + 53) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (72 * q + 53) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 23 (mod 32) ⇒ step^3(n) < n. -/
theorem descent_m32_23 (q : ℕ) (hq : 32 * q + 23 > 1) :
    step (step (step (32 * q + 23))) < 32 * q + 23 := by
  rw [step2_m32_23 q]
  have h_bound : step (72 * q + 53) ≤ 27 * q + 20 := by
    unfold step
    have h3n1 : 3 * (72 * q + 53) + 1 = 2 ^ 3 * (27 * q + 20) := by ring
    have hne : (27 * q + 20) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (72 * q + 53) + 1) = 3 + ν₂ (27 * q + 20) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (27 * q + 20) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (27 * q + 20) (2 ^ ν₂ (27 * q + 20)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m32_25 (q : ℕ) : step (32 * q + 25) = 24 * q + 19 := by
  unfold step
  have h3n1 : 3 * (32 * q + 25) + 1 = 2 ^ 2 * (24 * q + 19) := by ring
  have h_odd : (24 * q + 19) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (32 * q + 25) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (24 * q + 19) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (24 * q + 19) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (24 * q + 19) (by positivity)]

theorem step2_m32_25 (q : ℕ) : step (step (32 * q + 25)) = 36 * q + 29 := by
  rw [step_m32_25 q]
  unfold step
  have h3n1 : 3 * (24 * q + 19) + 1 = 2 ^ 1 * (36 * q + 29) := by ring
  have h_odd : (36 * q + 29) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (24 * q + 19) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (36 * q + 29) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (36 * q + 29) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (36 * q + 29) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 25 (mod 32) ⇒ step^3(n) < n. -/
theorem descent_m32_25 (q : ℕ) (hq : 32 * q + 25 > 1) :
    step (step (step (32 * q + 25))) < 32 * q + 25 := by
  rw [step2_m32_25 q]
  have h_bound : step (36 * q + 29) ≤ 27 * q + 22 := by
    unfold step
    have h3n1 : 3 * (36 * q + 29) + 1 = 2 ^ 2 * (27 * q + 22) := by ring
    have hne : (27 * q + 22) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (36 * q + 29) + 1) = 2 + ν₂ (27 * q + 22) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (27 * q + 22) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (27 * q + 22) (2 ^ ν₂ (27 * q + 22)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m128_7 (q : ℕ) : step (128 * q + 7) = 192 * q + 11 := by
  unfold step
  have h3n1 : 3 * (128 * q + 7) + 1 = 2 ^ 1 * (192 * q + 11) := by ring
  have h_odd : (192 * q + 11) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (128 * q + 7) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (192 * q + 11) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (192 * q + 11) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (192 * q + 11) (by positivity)]

theorem step2_m128_7 (q : ℕ) : step (step (128 * q + 7)) = 288 * q + 17 := by
  rw [step_m128_7 q]
  unfold step
  have h3n1 : 3 * (192 * q + 11) + 1 = 2 ^ 1 * (288 * q + 17) := by ring
  have h_odd : (288 * q + 17) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (192 * q + 11) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (288 * q + 17) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (288 * q + 17) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (288 * q + 17) (by positivity)]

theorem step3_m128_7 (q : ℕ) : step (step (step (128 * q + 7))) = 216 * q + 13 := by
  rw [step2_m128_7 q]
  unfold step
  have h3n1 : 3 * (288 * q + 17) + 1 = 2 ^ 2 * (216 * q + 13) := by ring
  have h_odd : (216 * q + 13) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (288 * q + 17) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (216 * q + 13) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (216 * q + 13) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (216 * q + 13) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7 (mod 128) ⇒ step^4(n) < n. -/
theorem descent_m128_7 (q : ℕ) (hq : 128 * q + 7 > 1) :
    step (step (step (step (128 * q + 7)))) < 128 * q + 7 := by
  rw [step3_m128_7 q]
  have h_bound : step (216 * q + 13) ≤ 81 * q + 5 := by
    unfold step
    have h3n1 : 3 * (216 * q + 13) + 1 = 2 ^ 3 * (81 * q + 5) := by ring
    have hne : (81 * q + 5) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (216 * q + 13) + 1) = 3 + ν₂ (81 * q + 5) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (81 * q + 5) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (81 * q + 5) (2 ^ ν₂ (81 * q + 5)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m128_15 (q : ℕ) : step (128 * q + 15) = 192 * q + 23 := by
  unfold step
  have h3n1 : 3 * (128 * q + 15) + 1 = 2 ^ 1 * (192 * q + 23) := by ring
  have h_odd : (192 * q + 23) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (128 * q + 15) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (192 * q + 23) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (192 * q + 23) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (192 * q + 23) (by positivity)]

theorem step2_m128_15 (q : ℕ) : step (step (128 * q + 15)) = 288 * q + 35 := by
  rw [step_m128_15 q]
  unfold step
  have h3n1 : 3 * (192 * q + 23) + 1 = 2 ^ 1 * (288 * q + 35) := by ring
  have h_odd : (288 * q + 35) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (192 * q + 23) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (288 * q + 35) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (288 * q + 35) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (288 * q + 35) (by positivity)]

theorem step3_m128_15 (q : ℕ) : step (step (step (128 * q + 15))) = 432 * q + 53 := by
  rw [step2_m128_15 q]
  unfold step
  have h3n1 : 3 * (288 * q + 35) + 1 = 2 ^ 1 * (432 * q + 53) := by ring
  have h_odd : (432 * q + 53) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (288 * q + 35) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (432 * q + 53) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (432 * q + 53) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (432 * q + 53) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 15 (mod 128) ⇒ step^4(n) < n. -/
theorem descent_m128_15 (q : ℕ) (hq : 128 * q + 15 > 1) :
    step (step (step (step (128 * q + 15)))) < 128 * q + 15 := by
  rw [step3_m128_15 q]
  have h_bound : step (432 * q + 53) ≤ 81 * q + 10 := by
    unfold step
    have h3n1 : 3 * (432 * q + 53) + 1 = 2 ^ 4 * (81 * q + 10) := by ring
    have hne : (81 * q + 10) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (432 * q + 53) + 1) = 4 + ν₂ (81 * q + 10) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (81 * q + 10) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (81 * q + 10) (2 ^ ν₂ (81 * q + 10)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m128_33 (q : ℕ) : step (128 * q + 33) = 96 * q + 25 := by
  unfold step
  have h3n1 : 3 * (128 * q + 33) + 1 = 2 ^ 2 * (96 * q + 25) := by ring
  have h_odd : (96 * q + 25) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (128 * q + 33) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (96 * q + 25) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (96 * q + 25) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (96 * q + 25) (by positivity)]

theorem step2_m128_33 (q : ℕ) : step (step (128 * q + 33)) = 72 * q + 19 := by
  rw [step_m128_33 q]
  unfold step
  have h3n1 : 3 * (96 * q + 25) + 1 = 2 ^ 2 * (72 * q + 19) := by ring
  have h_odd : (72 * q + 19) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (96 * q + 25) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (72 * q + 19) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (72 * q + 19) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (72 * q + 19) (by positivity)]

theorem step3_m128_33 (q : ℕ) : step (step (step (128 * q + 33))) = 108 * q + 29 := by
  rw [step2_m128_33 q]
  unfold step
  have h3n1 : 3 * (72 * q + 19) + 1 = 2 ^ 1 * (108 * q + 29) := by ring
  have h_odd : (108 * q + 29) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (72 * q + 19) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (108 * q + 29) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (108 * q + 29) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (108 * q + 29) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 33 (mod 128) ⇒ step^4(n) < n. -/
theorem descent_m128_33 (q : ℕ) (hq : 128 * q + 33 > 1) :
    step (step (step (step (128 * q + 33)))) < 128 * q + 33 := by
  rw [step3_m128_33 q]
  have h_bound : step (108 * q + 29) ≤ 81 * q + 22 := by
    unfold step
    have h3n1 : 3 * (108 * q + 29) + 1 = 2 ^ 2 * (81 * q + 22) := by ring
    have hne : (81 * q + 22) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (108 * q + 29) + 1) = 2 + ν₂ (81 * q + 22) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (81 * q + 22) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (81 * q + 22) (2 ^ ν₂ (81 * q + 22)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m128_59 (q : ℕ) : step (128 * q + 59) = 192 * q + 89 := by
  unfold step
  have h3n1 : 3 * (128 * q + 59) + 1 = 2 ^ 1 * (192 * q + 89) := by ring
  have h_odd : (192 * q + 89) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (128 * q + 59) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (192 * q + 89) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (192 * q + 89) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (192 * q + 89) (by positivity)]

theorem step2_m128_59 (q : ℕ) : step (step (128 * q + 59)) = 144 * q + 67 := by
  rw [step_m128_59 q]
  unfold step
  have h3n1 : 3 * (192 * q + 89) + 1 = 2 ^ 2 * (144 * q + 67) := by ring
  have h_odd : (144 * q + 67) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (192 * q + 89) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (144 * q + 67) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (144 * q + 67) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (144 * q + 67) (by positivity)]

theorem step3_m128_59 (q : ℕ) : step (step (step (128 * q + 59))) = 216 * q + 101 := by
  rw [step2_m128_59 q]
  unfold step
  have h3n1 : 3 * (144 * q + 67) + 1 = 2 ^ 1 * (216 * q + 101) := by ring
  have h_odd : (216 * q + 101) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (144 * q + 67) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (216 * q + 101) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (216 * q + 101) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (216 * q + 101) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 59 (mod 128) ⇒ step^4(n) < n. -/
theorem descent_m128_59 (q : ℕ) (hq : 128 * q + 59 > 1) :
    step (step (step (step (128 * q + 59)))) < 128 * q + 59 := by
  rw [step3_m128_59 q]
  have h_bound : step (216 * q + 101) ≤ 81 * q + 38 := by
    unfold step
    have h3n1 : 3 * (216 * q + 101) + 1 = 2 ^ 3 * (81 * q + 38) := by ring
    have hne : (81 * q + 38) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (216 * q + 101) + 1) = 3 + ν₂ (81 * q + 38) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (81 * q + 38) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (81 * q + 38) (2 ^ ν₂ (81 * q + 38)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m128_65 (q : ℕ) : step (128 * q + 65) = 96 * q + 49 := by
  unfold step
  have h3n1 : 3 * (128 * q + 65) + 1 = 2 ^ 2 * (96 * q + 49) := by ring
  have h_odd : (96 * q + 49) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (128 * q + 65) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (96 * q + 49) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (96 * q + 49) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (96 * q + 49) (by positivity)]

theorem step2_m128_65 (q : ℕ) : step (step (128 * q + 65)) = 72 * q + 37 := by
  rw [step_m128_65 q]
  unfold step
  have h3n1 : 3 * (96 * q + 49) + 1 = 2 ^ 2 * (72 * q + 37) := by ring
  have h_odd : (72 * q + 37) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (96 * q + 49) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (72 * q + 37) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (72 * q + 37) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (72 * q + 37) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 65 (mod 128) ⇒ step^3(n) < n. -/
theorem descent_m128_65 (q : ℕ) (hq : 128 * q + 65 > 1) :
    step (step (step (128 * q + 65))) < 128 * q + 65 := by
  rw [step2_m128_65 q]
  have h_bound : step (72 * q + 37) ≤ 27 * q + 14 := by
    unfold step
    have h3n1 : 3 * (72 * q + 37) + 1 = 2 ^ 3 * (27 * q + 14) := by ring
    have hne : (27 * q + 14) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (72 * q + 37) + 1) = 3 + ν₂ (27 * q + 14) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (27 * q + 14) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (27 * q + 14) (2 ^ ν₂ (27 * q + 14)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m128_73 (q : ℕ) : step (128 * q + 73) = 96 * q + 55 := by
  unfold step
  have h3n1 : 3 * (128 * q + 73) + 1 = 2 ^ 2 * (96 * q + 55) := by ring
  have h_odd : (96 * q + 55) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (128 * q + 73) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (96 * q + 55) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (96 * q + 55) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (96 * q + 55) (by positivity)]

theorem step2_m128_73 (q : ℕ) : step (step (128 * q + 73)) = 144 * q + 83 := by
  rw [step_m128_73 q]
  unfold step
  have h3n1 : 3 * (96 * q + 55) + 1 = 2 ^ 1 * (144 * q + 83) := by ring
  have h_odd : (144 * q + 83) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (96 * q + 55) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (144 * q + 83) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (144 * q + 83) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (144 * q + 83) (by positivity)]

theorem step3_m128_73 (q : ℕ) : step (step (step (128 * q + 73))) = 216 * q + 125 := by
  rw [step2_m128_73 q]
  unfold step
  have h3n1 : 3 * (144 * q + 83) + 1 = 2 ^ 1 * (216 * q + 125) := by ring
  have h_odd : (216 * q + 125) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (144 * q + 83) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (216 * q + 125) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (216 * q + 125) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (216 * q + 125) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 73 (mod 128) ⇒ step^4(n) < n. -/
theorem descent_m128_73 (q : ℕ) (hq : 128 * q + 73 > 1) :
    step (step (step (step (128 * q + 73)))) < 128 * q + 73 := by
  rw [step3_m128_73 q]
  have h_bound : step (216 * q + 125) ≤ 81 * q + 47 := by
    unfold step
    have h3n1 : 3 * (216 * q + 125) + 1 = 2 ^ 3 * (81 * q + 47) := by ring
    have hne : (81 * q + 47) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (216 * q + 125) + 1) = 3 + ν₂ (81 * q + 47) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (81 * q + 47) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (81 * q + 47) (2 ^ ν₂ (81 * q + 47)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_39 (q : ℕ) : step (256 * q + 39) = 384 * q + 59 := by
  unfold step
  have h3n1 : 3 * (256 * q + 39) + 1 = 2 ^ 1 * (384 * q + 59) := by ring
  have h_odd : (384 * q + 59) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 39) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (384 * q + 59) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (384 * q + 59) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 59) (by positivity)]

theorem step2_m256_39 (q : ℕ) : step (step (256 * q + 39)) = 576 * q + 89 := by
  rw [step_m256_39 q]
  unfold step
  have h3n1 : 3 * (384 * q + 59) + 1 = 2 ^ 1 * (576 * q + 89) := by ring
  have h_odd : (576 * q + 89) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 59) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (576 * q + 89) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (576 * q + 89) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 89) (by positivity)]

theorem step3_m256_39 (q : ℕ) : step (step (step (256 * q + 39))) = 432 * q + 67 := by
  rw [step2_m256_39 q]
  unfold step
  have h3n1 : 3 * (576 * q + 89) + 1 = 2 ^ 2 * (432 * q + 67) := by ring
  have h_odd : (432 * q + 67) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 89) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (432 * q + 67) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (432 * q + 67) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (432 * q + 67) (by positivity)]

theorem step4_m256_39 (q : ℕ) : step (step (step (step (256 * q + 39)))) = 648 * q + 101 := by
  rw [step3_m256_39 q]
  unfold step
  have h3n1 : 3 * (432 * q + 67) + 1 = 2 ^ 1 * (648 * q + 101) := by ring
  have h_odd : (648 * q + 101) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (432 * q + 67) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (648 * q + 101) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (648 * q + 101) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (648 * q + 101) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 39 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_39 (q : ℕ) (hq : 256 * q + 39 > 1) :
    step (step (step (step (step (256 * q + 39))))) < 256 * q + 39 := by
  rw [step4_m256_39 q]
  have h_bound : step (648 * q + 101) ≤ 243 * q + 38 := by
    unfold step
    have h3n1 : 3 * (648 * q + 101) + 1 = 2 ^ 3 * (243 * q + 38) := by ring
    have hne : (243 * q + 38) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (648 * q + 101) + 1) = 3 + ν₂ (243 * q + 38) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (243 * q + 38) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 38) (2 ^ ν₂ (243 * q + 38)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_79 (q : ℕ) : step (256 * q + 79) = 384 * q + 119 := by
  unfold step
  have h3n1 : 3 * (256 * q + 79) + 1 = 2 ^ 1 * (384 * q + 119) := by ring
  have h_odd : (384 * q + 119) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 79) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (384 * q + 119) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (384 * q + 119) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 119) (by positivity)]

theorem step2_m256_79 (q : ℕ) : step (step (256 * q + 79)) = 576 * q + 179 := by
  rw [step_m256_79 q]
  unfold step
  have h3n1 : 3 * (384 * q + 119) + 1 = 2 ^ 1 * (576 * q + 179) := by ring
  have h_odd : (576 * q + 179) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 119) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (576 * q + 179) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (576 * q + 179) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 179) (by positivity)]

theorem step3_m256_79 (q : ℕ) : step (step (step (256 * q + 79))) = 864 * q + 269 := by
  rw [step2_m256_79 q]
  unfold step
  have h3n1 : 3 * (576 * q + 179) + 1 = 2 ^ 1 * (864 * q + 269) := by ring
  have h_odd : (864 * q + 269) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 179) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (864 * q + 269) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (864 * q + 269) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (864 * q + 269) (by positivity)]

theorem step4_m256_79 (q : ℕ) : step (step (step (step (256 * q + 79)))) = 324 * q + 101 := by
  rw [step3_m256_79 q]
  unfold step
  have h3n1 : 3 * (864 * q + 269) + 1 = 2 ^ 3 * (324 * q + 101) := by ring
  have h_odd : (324 * q + 101) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (864 * q + 269) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (324 * q + 101) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (324 * q + 101) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (324 * q + 101) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 79 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_79 (q : ℕ) (hq : 256 * q + 79 > 1) :
    step (step (step (step (step (256 * q + 79))))) < 256 * q + 79 := by
  rw [step4_m256_79 q]
  have h_bound : step (324 * q + 101) ≤ 243 * q + 76 := by
    unfold step
    have h3n1 : 3 * (324 * q + 101) + 1 = 2 ^ 2 * (243 * q + 76) := by ring
    have hne : (243 * q + 76) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (324 * q + 101) + 1) = 2 + ν₂ (243 * q + 76) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (243 * q + 76) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 76) (2 ^ ν₂ (243 * q + 76)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_95 (q : ℕ) : step (256 * q + 95) = 384 * q + 143 := by
  unfold step
  have h3n1 : 3 * (256 * q + 95) + 1 = 2 ^ 1 * (384 * q + 143) := by ring
  have h_odd : (384 * q + 143) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 95) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (384 * q + 143) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (384 * q + 143) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 143) (by positivity)]

theorem step2_m256_95 (q : ℕ) : step (step (256 * q + 95)) = 576 * q + 215 := by
  rw [step_m256_95 q]
  unfold step
  have h3n1 : 3 * (384 * q + 143) + 1 = 2 ^ 1 * (576 * q + 215) := by ring
  have h_odd : (576 * q + 215) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 143) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (576 * q + 215) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (576 * q + 215) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 215) (by positivity)]

theorem step3_m256_95 (q : ℕ) : step (step (step (256 * q + 95))) = 864 * q + 323 := by
  rw [step2_m256_95 q]
  unfold step
  have h3n1 : 3 * (576 * q + 215) + 1 = 2 ^ 1 * (864 * q + 323) := by ring
  have h_odd : (864 * q + 323) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 215) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (864 * q + 323) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (864 * q + 323) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (864 * q + 323) (by positivity)]

theorem step4_m256_95 (q : ℕ) : step (step (step (step (256 * q + 95)))) = 1296 * q + 485 := by
  rw [step3_m256_95 q]
  unfold step
  have h3n1 : 3 * (864 * q + 323) + 1 = 2 ^ 1 * (1296 * q + 485) := by ring
  have h_odd : (1296 * q + 485) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (864 * q + 323) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1296 * q + 485) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1296 * q + 485) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 485) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 95 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_95 (q : ℕ) (hq : 256 * q + 95 > 1) :
    step (step (step (step (step (256 * q + 95))))) < 256 * q + 95 := by
  rw [step4_m256_95 q]
  have h_bound : step (1296 * q + 485) ≤ 243 * q + 91 := by
    unfold step
    have h3n1 : 3 * (1296 * q + 485) + 1 = 2 ^ 4 * (243 * q + 91) := by ring
    have hne : (243 * q + 91) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1296 * q + 485) + 1) = 4 + ν₂ (243 * q + 91) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (243 * q + 91) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 91) (2 ^ ν₂ (243 * q + 91)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_97 (q : ℕ) : step (256 * q + 97) = 192 * q + 73 := by
  unfold step
  have h3n1 : 3 * (256 * q + 97) + 1 = 2 ^ 2 * (192 * q + 73) := by ring
  have h_odd : (192 * q + 73) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 97) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (192 * q + 73) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (192 * q + 73) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (192 * q + 73) (by positivity)]

theorem step2_m256_97 (q : ℕ) : step (step (256 * q + 97)) = 144 * q + 55 := by
  rw [step_m256_97 q]
  unfold step
  have h3n1 : 3 * (192 * q + 73) + 1 = 2 ^ 2 * (144 * q + 55) := by ring
  have h_odd : (144 * q + 55) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (192 * q + 73) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (144 * q + 55) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (144 * q + 55) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (144 * q + 55) (by positivity)]

theorem step3_m256_97 (q : ℕ) : step (step (step (256 * q + 97))) = 216 * q + 83 := by
  rw [step2_m256_97 q]
  unfold step
  have h3n1 : 3 * (144 * q + 55) + 1 = 2 ^ 1 * (216 * q + 83) := by ring
  have h_odd : (216 * q + 83) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (144 * q + 55) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (216 * q + 83) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (216 * q + 83) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (216 * q + 83) (by positivity)]

theorem step4_m256_97 (q : ℕ) : step (step (step (step (256 * q + 97)))) = 324 * q + 125 := by
  rw [step3_m256_97 q]
  unfold step
  have h3n1 : 3 * (216 * q + 83) + 1 = 2 ^ 1 * (324 * q + 125) := by ring
  have h_odd : (324 * q + 125) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (216 * q + 83) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (324 * q + 125) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (324 * q + 125) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (324 * q + 125) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 97 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_97 (q : ℕ) (hq : 256 * q + 97 > 1) :
    step (step (step (step (step (256 * q + 97))))) < 256 * q + 97 := by
  rw [step4_m256_97 q]
  have h_bound : step (324 * q + 125) ≤ 243 * q + 94 := by
    unfold step
    have h3n1 : 3 * (324 * q + 125) + 1 = 2 ^ 2 * (243 * q + 94) := by ring
    have hne : (243 * q + 94) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (324 * q + 125) + 1) = 2 + ν₂ (243 * q + 94) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (243 * q + 94) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 94) (2 ^ ν₂ (243 * q + 94)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_105 (q : ℕ) : step (256 * q + 105) = 192 * q + 79 := by
  unfold step
  have h3n1 : 3 * (256 * q + 105) + 1 = 2 ^ 2 * (192 * q + 79) := by ring
  have h_odd : (192 * q + 79) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 105) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (192 * q + 79) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (192 * q + 79) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (192 * q + 79) (by positivity)]

theorem step2_m256_105 (q : ℕ) : step (step (256 * q + 105)) = 288 * q + 119 := by
  rw [step_m256_105 q]
  unfold step
  have h3n1 : 3 * (192 * q + 79) + 1 = 2 ^ 1 * (288 * q + 119) := by ring
  have h_odd : (288 * q + 119) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (192 * q + 79) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (288 * q + 119) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (288 * q + 119) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (288 * q + 119) (by positivity)]

theorem step3_m256_105 (q : ℕ) : step (step (step (256 * q + 105))) = 432 * q + 179 := by
  rw [step2_m256_105 q]
  unfold step
  have h3n1 : 3 * (288 * q + 119) + 1 = 2 ^ 1 * (432 * q + 179) := by ring
  have h_odd : (432 * q + 179) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (288 * q + 119) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (432 * q + 179) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (432 * q + 179) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (432 * q + 179) (by positivity)]

theorem step4_m256_105 (q : ℕ) : step (step (step (step (256 * q + 105)))) = 648 * q + 269 := by
  rw [step3_m256_105 q]
  unfold step
  have h3n1 : 3 * (432 * q + 179) + 1 = 2 ^ 1 * (648 * q + 269) := by ring
  have h_odd : (648 * q + 269) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (432 * q + 179) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (648 * q + 269) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (648 * q + 269) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (648 * q + 269) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 105 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_105 (q : ℕ) (hq : 256 * q + 105 > 1) :
    step (step (step (step (step (256 * q + 105))))) < 256 * q + 105 := by
  rw [step4_m256_105 q]
  have h_bound : step (648 * q + 269) ≤ 243 * q + 101 := by
    unfold step
    have h3n1 : 3 * (648 * q + 269) + 1 = 2 ^ 3 * (243 * q + 101) := by ring
    have hne : (243 * q + 101) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (648 * q + 269) + 1) = 3 + ν₂ (243 * q + 101) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (243 * q + 101) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 101) (2 ^ ν₂ (243 * q + 101)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_123 (q : ℕ) : step (256 * q + 123) = 384 * q + 185 := by
  unfold step
  have h3n1 : 3 * (256 * q + 123) + 1 = 2 ^ 1 * (384 * q + 185) := by ring
  have h_odd : (384 * q + 185) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 123) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (384 * q + 185) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (384 * q + 185) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 185) (by positivity)]

theorem step2_m256_123 (q : ℕ) : step (step (256 * q + 123)) = 288 * q + 139 := by
  rw [step_m256_123 q]
  unfold step
  have h3n1 : 3 * (384 * q + 185) + 1 = 2 ^ 2 * (288 * q + 139) := by ring
  have h_odd : (288 * q + 139) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 185) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (288 * q + 139) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (288 * q + 139) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (288 * q + 139) (by positivity)]

theorem step3_m256_123 (q : ℕ) : step (step (step (256 * q + 123))) = 432 * q + 209 := by
  rw [step2_m256_123 q]
  unfold step
  have h3n1 : 3 * (288 * q + 139) + 1 = 2 ^ 1 * (432 * q + 209) := by ring
  have h_odd : (432 * q + 209) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (288 * q + 139) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (432 * q + 209) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (432 * q + 209) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (432 * q + 209) (by positivity)]

theorem step4_m256_123 (q : ℕ) : step (step (step (step (256 * q + 123)))) = 324 * q + 157 := by
  rw [step3_m256_123 q]
  unfold step
  have h3n1 : 3 * (432 * q + 209) + 1 = 2 ^ 2 * (324 * q + 157) := by ring
  have h_odd : (324 * q + 157) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (432 * q + 209) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (324 * q + 157) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (324 * q + 157) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (324 * q + 157) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 123 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_123 (q : ℕ) (hq : 256 * q + 123 > 1) :
    step (step (step (step (step (256 * q + 123))))) < 256 * q + 123 := by
  rw [step4_m256_123 q]
  have h_bound : step (324 * q + 157) ≤ 243 * q + 118 := by
    unfold step
    have h3n1 : 3 * (324 * q + 157) + 1 = 2 ^ 2 * (243 * q + 118) := by ring
    have hne : (243 * q + 118) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (324 * q + 157) + 1) = 2 + ν₂ (243 * q + 118) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (243 * q + 118) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 118) (2 ^ ν₂ (243 * q + 118)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_129 (q : ℕ) : step (256 * q + 129) = 192 * q + 97 := by
  unfold step
  have h3n1 : 3 * (256 * q + 129) + 1 = 2 ^ 2 * (192 * q + 97) := by ring
  have h_odd : (192 * q + 97) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 129) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (192 * q + 97) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (192 * q + 97) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (192 * q + 97) (by positivity)]

theorem step2_m256_129 (q : ℕ) : step (step (256 * q + 129)) = 144 * q + 73 := by
  rw [step_m256_129 q]
  unfold step
  have h3n1 : 3 * (192 * q + 97) + 1 = 2 ^ 2 * (144 * q + 73) := by ring
  have h_odd : (144 * q + 73) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (192 * q + 97) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (144 * q + 73) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (144 * q + 73) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (144 * q + 73) (by positivity)]

theorem step3_m256_129 (q : ℕ) : step (step (step (256 * q + 129))) = 108 * q + 55 := by
  rw [step2_m256_129 q]
  unfold step
  have h3n1 : 3 * (144 * q + 73) + 1 = 2 ^ 2 * (108 * q + 55) := by ring
  have h_odd : (108 * q + 55) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (144 * q + 73) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (108 * q + 55) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (108 * q + 55) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (108 * q + 55) (by positivity)]

theorem step4_m256_129 (q : ℕ) : step (step (step (step (256 * q + 129)))) = 162 * q + 83 := by
  rw [step3_m256_129 q]
  unfold step
  have h3n1 : 3 * (108 * q + 55) + 1 = 2 ^ 1 * (162 * q + 83) := by ring
  have h_odd : (162 * q + 83) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (108 * q + 55) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (162 * q + 83) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (162 * q + 83) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (162 * q + 83) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 129 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_129 (q : ℕ) (hq : 256 * q + 129 > 1) :
    step (step (step (step (step (256 * q + 129))))) < 256 * q + 129 := by
  rw [step4_m256_129 q]
  have h_bound : step (162 * q + 83) ≤ 243 * q + 125 := by
    unfold step
    have h3n1 : 3 * (162 * q + 83) + 1 = 2 ^ 1 * (243 * q + 125) := by ring
    have hne : (243 * q + 125) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (162 * q + 83) + 1) = 1 + ν₂ (243 * q + 125) := by
      rw [h3n1, ν₂_mul (2 ^ 1) (243 * q + 125) (by positivity) hne, ν₂_pow_two' 1]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 125) (2 ^ ν₂ (243 * q + 125)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_175 (q : ℕ) : step (256 * q + 175) = 384 * q + 263 := by
  unfold step
  have h3n1 : 3 * (256 * q + 175) + 1 = 2 ^ 1 * (384 * q + 263) := by ring
  have h_odd : (384 * q + 263) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 175) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (384 * q + 263) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (384 * q + 263) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 263) (by positivity)]

theorem step2_m256_175 (q : ℕ) : step (step (256 * q + 175)) = 576 * q + 395 := by
  rw [step_m256_175 q]
  unfold step
  have h3n1 : 3 * (384 * q + 263) + 1 = 2 ^ 1 * (576 * q + 395) := by ring
  have h_odd : (576 * q + 395) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 263) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (576 * q + 395) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (576 * q + 395) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 395) (by positivity)]

theorem step3_m256_175 (q : ℕ) : step (step (step (256 * q + 175))) = 864 * q + 593 := by
  rw [step2_m256_175 q]
  unfold step
  have h3n1 : 3 * (576 * q + 395) + 1 = 2 ^ 1 * (864 * q + 593) := by ring
  have h_odd : (864 * q + 593) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 395) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (864 * q + 593) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (864 * q + 593) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (864 * q + 593) (by positivity)]

theorem step4_m256_175 (q : ℕ) : step (step (step (step (256 * q + 175)))) = 648 * q + 445 := by
  rw [step3_m256_175 q]
  unfold step
  have h3n1 : 3 * (864 * q + 593) + 1 = 2 ^ 2 * (648 * q + 445) := by ring
  have h_odd : (648 * q + 445) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (864 * q + 593) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (648 * q + 445) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (648 * q + 445) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (648 * q + 445) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 175 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_175 (q : ℕ) (hq : 256 * q + 175 > 1) :
    step (step (step (step (step (256 * q + 175))))) < 256 * q + 175 := by
  rw [step4_m256_175 q]
  have h_bound : step (648 * q + 445) ≤ 243 * q + 167 := by
    unfold step
    have h3n1 : 3 * (648 * q + 445) + 1 = 2 ^ 3 * (243 * q + 167) := by ring
    have hne : (243 * q + 167) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (648 * q + 445) + 1) = 3 + ν₂ (243 * q + 167) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (243 * q + 167) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 167) (2 ^ ν₂ (243 * q + 167)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_199 (q : ℕ) : step (256 * q + 199) = 384 * q + 299 := by
  unfold step
  have h3n1 : 3 * (256 * q + 199) + 1 = 2 ^ 1 * (384 * q + 299) := by ring
  have h_odd : (384 * q + 299) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 199) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (384 * q + 299) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (384 * q + 299) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 299) (by positivity)]

theorem step2_m256_199 (q : ℕ) : step (step (256 * q + 199)) = 576 * q + 449 := by
  rw [step_m256_199 q]
  unfold step
  have h3n1 : 3 * (384 * q + 299) + 1 = 2 ^ 1 * (576 * q + 449) := by ring
  have h_odd : (576 * q + 449) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 299) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (576 * q + 449) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (576 * q + 449) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 449) (by positivity)]

theorem step3_m256_199 (q : ℕ) : step (step (step (256 * q + 199))) = 432 * q + 337 := by
  rw [step2_m256_199 q]
  unfold step
  have h3n1 : 3 * (576 * q + 449) + 1 = 2 ^ 2 * (432 * q + 337) := by ring
  have h_odd : (432 * q + 337) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 449) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (432 * q + 337) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (432 * q + 337) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (432 * q + 337) (by positivity)]

theorem step4_m256_199 (q : ℕ) : step (step (step (step (256 * q + 199)))) = 324 * q + 253 := by
  rw [step3_m256_199 q]
  unfold step
  have h3n1 : 3 * (432 * q + 337) + 1 = 2 ^ 2 * (324 * q + 253) := by ring
  have h_odd : (324 * q + 253) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (432 * q + 337) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (324 * q + 253) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (324 * q + 253) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (324 * q + 253) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 199 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_199 (q : ℕ) (hq : 256 * q + 199 > 1) :
    step (step (step (step (step (256 * q + 199))))) < 256 * q + 199 := by
  rw [step4_m256_199 q]
  have h_bound : step (324 * q + 253) ≤ 243 * q + 190 := by
    unfold step
    have h3n1 : 3 * (324 * q + 253) + 1 = 2 ^ 2 * (243 * q + 190) := by ring
    have hne : (243 * q + 190) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (324 * q + 253) + 1) = 2 + ν₂ (243 * q + 190) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (243 * q + 190) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 190) (2 ^ ν₂ (243 * q + 190)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m256_219 (q : ℕ) : step (256 * q + 219) = 384 * q + 329 := by
  unfold step
  have h3n1 : 3 * (256 * q + 219) + 1 = 2 ^ 1 * (384 * q + 329) := by ring
  have h_odd : (384 * q + 329) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (256 * q + 219) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (384 * q + 329) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (384 * q + 329) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 329) (by positivity)]

theorem step2_m256_219 (q : ℕ) : step (step (256 * q + 219)) = 288 * q + 247 := by
  rw [step_m256_219 q]
  unfold step
  have h3n1 : 3 * (384 * q + 329) + 1 = 2 ^ 2 * (288 * q + 247) := by ring
  have h_odd : (288 * q + 247) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 329) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (288 * q + 247) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (288 * q + 247) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (288 * q + 247) (by positivity)]

theorem step3_m256_219 (q : ℕ) : step (step (step (256 * q + 219))) = 432 * q + 371 := by
  rw [step2_m256_219 q]
  unfold step
  have h3n1 : 3 * (288 * q + 247) + 1 = 2 ^ 1 * (432 * q + 371) := by ring
  have h_odd : (432 * q + 371) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (288 * q + 247) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (432 * q + 371) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (432 * q + 371) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (432 * q + 371) (by positivity)]

theorem step4_m256_219 (q : ℕ) : step (step (step (step (256 * q + 219)))) = 648 * q + 557 := by
  rw [step3_m256_219 q]
  unfold step
  have h3n1 : 3 * (432 * q + 371) + 1 = 2 ^ 1 * (648 * q + 557) := by ring
  have h_odd : (648 * q + 557) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (432 * q + 371) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (648 * q + 557) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (648 * q + 557) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (648 * q + 557) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 219 (mod 256) ⇒ step^5(n) < n. -/
theorem descent_m256_219 (q : ℕ) (hq : 256 * q + 219 > 1) :
    step (step (step (step (step (256 * q + 219))))) < 256 * q + 219 := by
  rw [step4_m256_219 q]
  have h_bound : step (648 * q + 557) ≤ 243 * q + 209 := by
    unfold step
    have h3n1 : 3 * (648 * q + 557) + 1 = 2 ^ 3 * (243 * q + 209) := by ring
    have hne : (243 * q + 209) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (648 * q + 557) + 1) = 3 + ν₂ (243 * q + 209) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (243 * q + 209) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 209) (2 ^ ν₂ (243 * q + 209)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m512_9 (q : ℕ) : step (512 * q + 9) = 384 * q + 7 := by
  unfold step
  have h3n1 : 3 * (512 * q + 9) + 1 = 2 ^ 2 * (384 * q + 7) := by ring
  have h_odd : (384 * q + 7) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (512 * q + 9) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (384 * q + 7) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (384 * q + 7) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 7) (by positivity)]

theorem step2_m512_9 (q : ℕ) : step (step (512 * q + 9)) = 576 * q + 11 := by
  rw [step_m512_9 q]
  unfold step
  have h3n1 : 3 * (384 * q + 7) + 1 = 2 ^ 1 * (576 * q + 11) := by ring
  have h_odd : (576 * q + 11) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 7) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (576 * q + 11) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (576 * q + 11) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 11) (by positivity)]

theorem step3_m512_9 (q : ℕ) : step (step (step (512 * q + 9))) = 864 * q + 17 := by
  rw [step2_m512_9 q]
  unfold step
  have h3n1 : 3 * (576 * q + 11) + 1 = 2 ^ 1 * (864 * q + 17) := by ring
  have h_odd : (864 * q + 17) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 11) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (864 * q + 17) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (864 * q + 17) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (864 * q + 17) (by positivity)]

theorem step4_m512_9 (q : ℕ) : step (step (step (step (512 * q + 9)))) = 648 * q + 13 := by
  rw [step3_m512_9 q]
  unfold step
  have h3n1 : 3 * (864 * q + 17) + 1 = 2 ^ 2 * (648 * q + 13) := by ring
  have h_odd : (648 * q + 13) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (864 * q + 17) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (648 * q + 13) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (648 * q + 13) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (648 * q + 13) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 9 (mod 512) ⇒ step^5(n) < n. -/
theorem descent_m512_9 (q : ℕ) (hq : 512 * q + 9 > 1) :
    step (step (step (step (step (512 * q + 9))))) < 512 * q + 9 := by
  rw [step4_m512_9 q]
  have h_bound : step (648 * q + 13) ≤ 243 * q + 5 := by
    unfold step
    have h3n1 : 3 * (648 * q + 13) + 1 = 2 ^ 3 * (243 * q + 5) := by ring
    have hne : (243 * q + 5) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (648 * q + 13) + 1) = 3 + ν₂ (243 * q + 5) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (243 * q + 5) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 5) (2 ^ ν₂ (243 * q + 5)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m512_257 (q : ℕ) : step (512 * q + 257) = 384 * q + 193 := by
  unfold step
  have h3n1 : 3 * (512 * q + 257) + 1 = 2 ^ 2 * (384 * q + 193) := by ring
  have h_odd : (384 * q + 193) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (512 * q + 257) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (384 * q + 193) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (384 * q + 193) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (384 * q + 193) (by positivity)]

theorem step2_m512_257 (q : ℕ) : step (step (512 * q + 257)) = 288 * q + 145 := by
  rw [step_m512_257 q]
  unfold step
  have h3n1 : 3 * (384 * q + 193) + 1 = 2 ^ 2 * (288 * q + 145) := by ring
  have h_odd : (288 * q + 145) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (384 * q + 193) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (288 * q + 145) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (288 * q + 145) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (288 * q + 145) (by positivity)]

theorem step3_m512_257 (q : ℕ) : step (step (step (512 * q + 257))) = 216 * q + 109 := by
  rw [step2_m512_257 q]
  unfold step
  have h3n1 : 3 * (288 * q + 145) + 1 = 2 ^ 2 * (216 * q + 109) := by ring
  have h_odd : (216 * q + 109) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (288 * q + 145) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (216 * q + 109) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (216 * q + 109) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (216 * q + 109) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 257 (mod 512) ⇒ step^4(n) < n. -/
theorem descent_m512_257 (q : ℕ) (hq : 512 * q + 257 > 1) :
    step (step (step (step (512 * q + 257)))) < 512 * q + 257 := by
  rw [step3_m512_257 q]
  have h_bound : step (216 * q + 109) ≤ 81 * q + 41 := by
    unfold step
    have h3n1 : 3 * (216 * q + 109) + 1 = 2 ^ 3 * (81 * q + 41) := by ring
    have hne : (81 * q + 41) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (216 * q + 109) + 1) = 3 + ν₂ (81 * q + 41) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (81 * q + 41) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (81 * q + 41) (2 ^ ν₂ (81 * q + 41)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_233 (q : ℕ) : step (1024 * q + 233) = 768 * q + 175 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 233) + 1 = 2 ^ 2 * (768 * q + 175) := by ring
  have h_odd : (768 * q + 175) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 233) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (768 * q + 175) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (768 * q + 175) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (768 * q + 175) (by positivity)]

theorem step2_m1024_233 (q : ℕ) : step (step (1024 * q + 233)) = 1152 * q + 263 := by
  rw [step_m1024_233 q]
  unfold step
  have h3n1 : 3 * (768 * q + 175) + 1 = 2 ^ 1 * (1152 * q + 263) := by ring
  have h_odd : (1152 * q + 263) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (768 * q + 175) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1152 * q + 263) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1152 * q + 263) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 263) (by positivity)]

theorem step3_m1024_233 (q : ℕ) : step (step (step (1024 * q + 233))) = 1728 * q + 395 := by
  rw [step2_m1024_233 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 263) + 1 = 2 ^ 1 * (1728 * q + 395) := by ring
  have h_odd : (1728 * q + 395) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 263) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1728 * q + 395) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1728 * q + 395) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 395) (by positivity)]

theorem step4_m1024_233 (q : ℕ) : step (step (step (step (1024 * q + 233)))) = 2592 * q + 593 := by
  rw [step3_m1024_233 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 395) + 1 = 2 ^ 1 * (2592 * q + 593) := by ring
  have h_odd : (2592 * q + 593) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 395) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2592 * q + 593) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2592 * q + 593) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 593) (by positivity)]

theorem step5_m1024_233 (q : ℕ) : step (step (step (step (step (1024 * q + 233))))) = 1944 * q + 445 := by
  rw [step4_m1024_233 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 593) + 1 = 2 ^ 2 * (1944 * q + 445) := by ring
  have h_odd : (1944 * q + 445) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 593) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1944 * q + 445) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1944 * q + 445) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 445) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 233 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_233 (q : ℕ) (hq : 1024 * q + 233 > 1) :
    step (step (step (step (step (step (1024 * q + 233)))))) < 1024 * q + 233 := by
  rw [step5_m1024_233 q]
  have h_bound : step (1944 * q + 445) ≤ 729 * q + 167 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 445) + 1 = 2 ^ 3 * (729 * q + 167) := by ring
    have hne : (729 * q + 167) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 445) + 1) = 3 + ν₂ (729 * q + 167) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 167) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 167) (2 ^ ν₂ (729 * q + 167)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_265 (q : ℕ) : step (1024 * q + 265) = 768 * q + 199 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 265) + 1 = 2 ^ 2 * (768 * q + 199) := by ring
  have h_odd : (768 * q + 199) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 265) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (768 * q + 199) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (768 * q + 199) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (768 * q + 199) (by positivity)]

theorem step2_m1024_265 (q : ℕ) : step (step (1024 * q + 265)) = 1152 * q + 299 := by
  rw [step_m1024_265 q]
  unfold step
  have h3n1 : 3 * (768 * q + 199) + 1 = 2 ^ 1 * (1152 * q + 299) := by ring
  have h_odd : (1152 * q + 299) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (768 * q + 199) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1152 * q + 299) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1152 * q + 299) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 299) (by positivity)]

theorem step3_m1024_265 (q : ℕ) : step (step (step (1024 * q + 265))) = 1728 * q + 449 := by
  rw [step2_m1024_265 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 299) + 1 = 2 ^ 1 * (1728 * q + 449) := by ring
  have h_odd : (1728 * q + 449) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 299) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1728 * q + 449) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1728 * q + 449) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 449) (by positivity)]

theorem step4_m1024_265 (q : ℕ) : step (step (step (step (1024 * q + 265)))) = 1296 * q + 337 := by
  rw [step3_m1024_265 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 449) + 1 = 2 ^ 2 * (1296 * q + 337) := by ring
  have h_odd : (1296 * q + 337) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 449) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1296 * q + 337) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1296 * q + 337) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 337) (by positivity)]

theorem step5_m1024_265 (q : ℕ) : step (step (step (step (step (1024 * q + 265))))) = 972 * q + 253 := by
  rw [step4_m1024_265 q]
  unfold step
  have h3n1 : 3 * (1296 * q + 337) + 1 = 2 ^ 2 * (972 * q + 253) := by ring
  have h_odd : (972 * q + 253) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1296 * q + 337) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (972 * q + 253) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (972 * q + 253) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (972 * q + 253) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 265 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_265 (q : ℕ) (hq : 1024 * q + 265 > 1) :
    step (step (step (step (step (step (1024 * q + 265)))))) < 1024 * q + 265 := by
  rw [step5_m1024_265 q]
  have h_bound : step (972 * q + 253) ≤ 729 * q + 190 := by
    unfold step
    have h3n1 : 3 * (972 * q + 253) + 1 = 2 ^ 2 * (729 * q + 190) := by ring
    have hne : (729 * q + 190) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (972 * q + 253) + 1) = 2 + ν₂ (729 * q + 190) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (729 * q + 190) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 190) (2 ^ ν₂ (729 * q + 190)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_287 (q : ℕ) : step (1024 * q + 287) = 1536 * q + 431 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 287) + 1 = 2 ^ 1 * (1536 * q + 431) := by ring
  have h_odd : (1536 * q + 431) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 287) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 431) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 431) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 431) (by positivity)]

theorem step2_m1024_287 (q : ℕ) : step (step (1024 * q + 287)) = 2304 * q + 647 := by
  rw [step_m1024_287 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 431) + 1 = 2 ^ 1 * (2304 * q + 647) := by ring
  have h_odd : (2304 * q + 647) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 431) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 647) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 647) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 647) (by positivity)]

theorem step3_m1024_287 (q : ℕ) : step (step (step (1024 * q + 287))) = 3456 * q + 971 := by
  rw [step2_m1024_287 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 647) + 1 = 2 ^ 1 * (3456 * q + 971) := by ring
  have h_odd : (3456 * q + 971) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 647) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 971) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 971) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 971) (by positivity)]

theorem step4_m1024_287 (q : ℕ) : step (step (step (step (1024 * q + 287)))) = 5184 * q + 1457 := by
  rw [step3_m1024_287 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 971) + 1 = 2 ^ 1 * (5184 * q + 1457) := by ring
  have h_odd : (5184 * q + 1457) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 971) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (5184 * q + 1457) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (5184 * q + 1457) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 1457) (by positivity)]

theorem step5_m1024_287 (q : ℕ) : step (step (step (step (step (1024 * q + 287))))) = 3888 * q + 1093 := by
  rw [step4_m1024_287 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 1457) + 1 = 2 ^ 2 * (3888 * q + 1093) := by ring
  have h_odd : (3888 * q + 1093) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 1457) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3888 * q + 1093) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3888 * q + 1093) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3888 * q + 1093) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 287 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_287 (q : ℕ) (hq : 1024 * q + 287 > 1) :
    step (step (step (step (step (step (1024 * q + 287)))))) < 1024 * q + 287 := by
  rw [step5_m1024_287 q]
  have h_bound : step (3888 * q + 1093) ≤ 729 * q + 205 := by
    unfold step
    have h3n1 : 3 * (3888 * q + 1093) + 1 = 2 ^ 4 * (729 * q + 205) := by ring
    have hne : (729 * q + 205) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (3888 * q + 1093) + 1) = 4 + ν₂ (729 * q + 205) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (729 * q + 205) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 205) (2 ^ ν₂ (729 * q + 205)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_347 (q : ℕ) : step (1024 * q + 347) = 1536 * q + 521 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 347) + 1 = 2 ^ 1 * (1536 * q + 521) := by ring
  have h_odd : (1536 * q + 521) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 347) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 521) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 521) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 521) (by positivity)]

theorem step2_m1024_347 (q : ℕ) : step (step (1024 * q + 347)) = 1152 * q + 391 := by
  rw [step_m1024_347 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 521) + 1 = 2 ^ 2 * (1152 * q + 391) := by ring
  have h_odd : (1152 * q + 391) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 521) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1152 * q + 391) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1152 * q + 391) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 391) (by positivity)]

theorem step3_m1024_347 (q : ℕ) : step (step (step (1024 * q + 347))) = 1728 * q + 587 := by
  rw [step2_m1024_347 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 391) + 1 = 2 ^ 1 * (1728 * q + 587) := by ring
  have h_odd : (1728 * q + 587) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 391) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1728 * q + 587) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1728 * q + 587) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 587) (by positivity)]

theorem step4_m1024_347 (q : ℕ) : step (step (step (step (1024 * q + 347)))) = 2592 * q + 881 := by
  rw [step3_m1024_347 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 587) + 1 = 2 ^ 1 * (2592 * q + 881) := by ring
  have h_odd : (2592 * q + 881) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 587) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2592 * q + 881) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2592 * q + 881) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 881) (by positivity)]

theorem step5_m1024_347 (q : ℕ) : step (step (step (step (step (1024 * q + 347))))) = 1944 * q + 661 := by
  rw [step4_m1024_347 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 881) + 1 = 2 ^ 2 * (1944 * q + 661) := by ring
  have h_odd : (1944 * q + 661) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 881) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1944 * q + 661) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1944 * q + 661) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 661) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 347 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_347 (q : ℕ) (hq : 1024 * q + 347 > 1) :
    step (step (step (step (step (step (1024 * q + 347)))))) < 1024 * q + 347 := by
  rw [step5_m1024_347 q]
  have h_bound : step (1944 * q + 661) ≤ 729 * q + 248 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 661) + 1 = 2 ^ 3 * (729 * q + 248) := by ring
    have hne : (729 * q + 248) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 661) + 1) = 3 + ν₂ (729 * q + 248) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 248) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 248) (2 ^ ν₂ (729 * q + 248)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_367 (q : ℕ) : step (1024 * q + 367) = 1536 * q + 551 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 367) + 1 = 2 ^ 1 * (1536 * q + 551) := by ring
  have h_odd : (1536 * q + 551) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 367) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 551) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 551) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 551) (by positivity)]

theorem step2_m1024_367 (q : ℕ) : step (step (1024 * q + 367)) = 2304 * q + 827 := by
  rw [step_m1024_367 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 551) + 1 = 2 ^ 1 * (2304 * q + 827) := by ring
  have h_odd : (2304 * q + 827) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 551) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 827) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 827) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 827) (by positivity)]

theorem step3_m1024_367 (q : ℕ) : step (step (step (1024 * q + 367))) = 3456 * q + 1241 := by
  rw [step2_m1024_367 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 827) + 1 = 2 ^ 1 * (3456 * q + 1241) := by ring
  have h_odd : (3456 * q + 1241) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 827) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 1241) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 1241) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 1241) (by positivity)]

theorem step4_m1024_367 (q : ℕ) : step (step (step (step (1024 * q + 367)))) = 2592 * q + 931 := by
  rw [step3_m1024_367 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 1241) + 1 = 2 ^ 2 * (2592 * q + 931) := by ring
  have h_odd : (2592 * q + 931) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 1241) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (2592 * q + 931) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (2592 * q + 931) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 931) (by positivity)]

theorem step5_m1024_367 (q : ℕ) : step (step (step (step (step (1024 * q + 367))))) = 3888 * q + 1397 := by
  rw [step4_m1024_367 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 931) + 1 = 2 ^ 1 * (3888 * q + 1397) := by ring
  have h_odd : (3888 * q + 1397) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 931) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3888 * q + 1397) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3888 * q + 1397) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3888 * q + 1397) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 367 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_367 (q : ℕ) (hq : 1024 * q + 367 > 1) :
    step (step (step (step (step (step (1024 * q + 367)))))) < 1024 * q + 367 := by
  rw [step5_m1024_367 q]
  have h_bound : step (3888 * q + 1397) ≤ 729 * q + 262 := by
    unfold step
    have h3n1 : 3 * (3888 * q + 1397) + 1 = 2 ^ 4 * (729 * q + 262) := by ring
    have hne : (729 * q + 262) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (3888 * q + 1397) + 1) = 4 + ν₂ (729 * q + 262) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (729 * q + 262) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 262) (2 ^ ν₂ (729 * q + 262)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_393 (q : ℕ) : step (1024 * q + 393) = 768 * q + 295 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 393) + 1 = 2 ^ 2 * (768 * q + 295) := by ring
  have h_odd : (768 * q + 295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 393) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (768 * q + 295) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (768 * q + 295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (768 * q + 295) (by positivity)]

theorem step2_m1024_393 (q : ℕ) : step (step (1024 * q + 393)) = 1152 * q + 443 := by
  rw [step_m1024_393 q]
  unfold step
  have h3n1 : 3 * (768 * q + 295) + 1 = 2 ^ 1 * (1152 * q + 443) := by ring
  have h_odd : (1152 * q + 443) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (768 * q + 295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1152 * q + 443) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1152 * q + 443) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 443) (by positivity)]

theorem step3_m1024_393 (q : ℕ) : step (step (step (1024 * q + 393))) = 1728 * q + 665 := by
  rw [step2_m1024_393 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 443) + 1 = 2 ^ 1 * (1728 * q + 665) := by ring
  have h_odd : (1728 * q + 665) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 443) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1728 * q + 665) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1728 * q + 665) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 665) (by positivity)]

theorem step4_m1024_393 (q : ℕ) : step (step (step (step (1024 * q + 393)))) = 1296 * q + 499 := by
  rw [step3_m1024_393 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 665) + 1 = 2 ^ 2 * (1296 * q + 499) := by ring
  have h_odd : (1296 * q + 499) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 665) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1296 * q + 499) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1296 * q + 499) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 499) (by positivity)]

theorem step5_m1024_393 (q : ℕ) : step (step (step (step (step (1024 * q + 393))))) = 1944 * q + 749 := by
  rw [step4_m1024_393 q]
  unfold step
  have h3n1 : 3 * (1296 * q + 499) + 1 = 2 ^ 1 * (1944 * q + 749) := by ring
  have h_odd : (1944 * q + 749) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1296 * q + 499) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1944 * q + 749) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1944 * q + 749) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 749) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 393 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_393 (q : ℕ) (hq : 1024 * q + 393 > 1) :
    step (step (step (step (step (step (1024 * q + 393)))))) < 1024 * q + 393 := by
  rw [step5_m1024_393 q]
  have h_bound : step (1944 * q + 749) ≤ 729 * q + 281 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 749) + 1 = 2 ^ 3 * (729 * q + 281) := by ring
    have hne : (729 * q + 281) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 749) + 1) = 3 + ν₂ (729 * q + 281) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 281) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 281) (2 ^ ν₂ (729 * q + 281)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_423 (q : ℕ) : step (1024 * q + 423) = 1536 * q + 635 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 423) + 1 = 2 ^ 1 * (1536 * q + 635) := by ring
  have h_odd : (1536 * q + 635) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 423) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 635) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 635) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 635) (by positivity)]

theorem step2_m1024_423 (q : ℕ) : step (step (1024 * q + 423)) = 2304 * q + 953 := by
  rw [step_m1024_423 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 635) + 1 = 2 ^ 1 * (2304 * q + 953) := by ring
  have h_odd : (2304 * q + 953) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 635) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 953) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 953) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 953) (by positivity)]

theorem step3_m1024_423 (q : ℕ) : step (step (step (1024 * q + 423))) = 1728 * q + 715 := by
  rw [step2_m1024_423 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 953) + 1 = 2 ^ 2 * (1728 * q + 715) := by ring
  have h_odd : (1728 * q + 715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 953) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1728 * q + 715) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1728 * q + 715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 715) (by positivity)]

theorem step4_m1024_423 (q : ℕ) : step (step (step (step (1024 * q + 423)))) = 2592 * q + 1073 := by
  rw [step3_m1024_423 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 715) + 1 = 2 ^ 1 * (2592 * q + 1073) := by ring
  have h_odd : (2592 * q + 1073) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2592 * q + 1073) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2592 * q + 1073) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 1073) (by positivity)]

theorem step5_m1024_423 (q : ℕ) : step (step (step (step (step (1024 * q + 423))))) = 1944 * q + 805 := by
  rw [step4_m1024_423 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 1073) + 1 = 2 ^ 2 * (1944 * q + 805) := by ring
  have h_odd : (1944 * q + 805) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 1073) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1944 * q + 805) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1944 * q + 805) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 805) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 423 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_423 (q : ℕ) (hq : 1024 * q + 423 > 1) :
    step (step (step (step (step (step (1024 * q + 423)))))) < 1024 * q + 423 := by
  rw [step5_m1024_423 q]
  have h_bound : step (1944 * q + 805) ≤ 729 * q + 302 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 805) + 1 = 2 ^ 3 * (729 * q + 302) := by ring
    have hne : (729 * q + 302) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 805) + 1) = 3 + ν₂ (729 * q + 302) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 302) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 302) (2 ^ ν₂ (729 * q + 302)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_481 (q : ℕ) : step (1024 * q + 481) = 768 * q + 361 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 481) + 1 = 2 ^ 2 * (768 * q + 361) := by ring
  have h_odd : (768 * q + 361) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 481) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (768 * q + 361) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (768 * q + 361) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (768 * q + 361) (by positivity)]

theorem step2_m1024_481 (q : ℕ) : step (step (1024 * q + 481)) = 576 * q + 271 := by
  rw [step_m1024_481 q]
  unfold step
  have h3n1 : 3 * (768 * q + 361) + 1 = 2 ^ 2 * (576 * q + 271) := by ring
  have h_odd : (576 * q + 271) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (768 * q + 361) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (576 * q + 271) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (576 * q + 271) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 271) (by positivity)]

theorem step3_m1024_481 (q : ℕ) : step (step (step (1024 * q + 481))) = 864 * q + 407 := by
  rw [step2_m1024_481 q]
  unfold step
  have h3n1 : 3 * (576 * q + 271) + 1 = 2 ^ 1 * (864 * q + 407) := by ring
  have h_odd : (864 * q + 407) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 271) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (864 * q + 407) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (864 * q + 407) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (864 * q + 407) (by positivity)]

theorem step4_m1024_481 (q : ℕ) : step (step (step (step (1024 * q + 481)))) = 1296 * q + 611 := by
  rw [step3_m1024_481 q]
  unfold step
  have h3n1 : 3 * (864 * q + 407) + 1 = 2 ^ 1 * (1296 * q + 611) := by ring
  have h_odd : (1296 * q + 611) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (864 * q + 407) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1296 * q + 611) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1296 * q + 611) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 611) (by positivity)]

theorem step5_m1024_481 (q : ℕ) : step (step (step (step (step (1024 * q + 481))))) = 1944 * q + 917 := by
  rw [step4_m1024_481 q]
  unfold step
  have h3n1 : 3 * (1296 * q + 611) + 1 = 2 ^ 1 * (1944 * q + 917) := by ring
  have h_odd : (1944 * q + 917) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1296 * q + 611) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1944 * q + 917) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1944 * q + 917) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 917) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 481 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_481 (q : ℕ) (hq : 1024 * q + 481 > 1) :
    step (step (step (step (step (step (1024 * q + 481)))))) < 1024 * q + 481 := by
  rw [step5_m1024_481 q]
  have h_bound : step (1944 * q + 917) ≤ 729 * q + 344 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 917) + 1 = 2 ^ 3 * (729 * q + 344) := by ring
    have hne : (729 * q + 344) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 917) + 1) = 3 + ν₂ (729 * q + 344) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 344) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 344) (2 ^ ν₂ (729 * q + 344)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_507 (q : ℕ) : step (1024 * q + 507) = 1536 * q + 761 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 507) + 1 = 2 ^ 1 * (1536 * q + 761) := by ring
  have h_odd : (1536 * q + 761) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 507) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 761) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 761) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 761) (by positivity)]

theorem step2_m1024_507 (q : ℕ) : step (step (1024 * q + 507)) = 1152 * q + 571 := by
  rw [step_m1024_507 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 761) + 1 = 2 ^ 2 * (1152 * q + 571) := by ring
  have h_odd : (1152 * q + 571) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 761) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1152 * q + 571) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1152 * q + 571) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 571) (by positivity)]

theorem step3_m1024_507 (q : ℕ) : step (step (step (1024 * q + 507))) = 1728 * q + 857 := by
  rw [step2_m1024_507 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 571) + 1 = 2 ^ 1 * (1728 * q + 857) := by ring
  have h_odd : (1728 * q + 857) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 571) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1728 * q + 857) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1728 * q + 857) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 857) (by positivity)]

theorem step4_m1024_507 (q : ℕ) : step (step (step (step (1024 * q + 507)))) = 1296 * q + 643 := by
  rw [step3_m1024_507 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 857) + 1 = 2 ^ 2 * (1296 * q + 643) := by ring
  have h_odd : (1296 * q + 643) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 857) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1296 * q + 643) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1296 * q + 643) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 643) (by positivity)]

theorem step5_m1024_507 (q : ℕ) : step (step (step (step (step (1024 * q + 507))))) = 1944 * q + 965 := by
  rw [step4_m1024_507 q]
  unfold step
  have h3n1 : 3 * (1296 * q + 643) + 1 = 2 ^ 1 * (1944 * q + 965) := by ring
  have h_odd : (1944 * q + 965) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1296 * q + 643) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1944 * q + 965) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1944 * q + 965) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 965) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 507 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_507 (q : ℕ) (hq : 1024 * q + 507 > 1) :
    step (step (step (step (step (step (1024 * q + 507)))))) < 1024 * q + 507 := by
  rw [step5_m1024_507 q]
  have h_bound : step (1944 * q + 965) ≤ 729 * q + 362 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 965) + 1 = 2 ^ 3 * (729 * q + 362) := by ring
    have hne : (729 * q + 362) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 965) + 1) = 3 + ν₂ (729 * q + 362) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 362) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 362) (2 ^ ν₂ (729 * q + 362)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_513 (q : ℕ) : step (1024 * q + 513) = 768 * q + 385 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 513) + 1 = 2 ^ 2 * (768 * q + 385) := by ring
  have h_odd : (768 * q + 385) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 513) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (768 * q + 385) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (768 * q + 385) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (768 * q + 385) (by positivity)]

theorem step2_m1024_513 (q : ℕ) : step (step (1024 * q + 513)) = 576 * q + 289 := by
  rw [step_m1024_513 q]
  unfold step
  have h3n1 : 3 * (768 * q + 385) + 1 = 2 ^ 2 * (576 * q + 289) := by ring
  have h_odd : (576 * q + 289) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (768 * q + 385) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (576 * q + 289) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (576 * q + 289) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (576 * q + 289) (by positivity)]

theorem step3_m1024_513 (q : ℕ) : step (step (step (1024 * q + 513))) = 432 * q + 217 := by
  rw [step2_m1024_513 q]
  unfold step
  have h3n1 : 3 * (576 * q + 289) + 1 = 2 ^ 2 * (432 * q + 217) := by ring
  have h_odd : (432 * q + 217) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (576 * q + 289) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (432 * q + 217) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (432 * q + 217) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (432 * q + 217) (by positivity)]

theorem step4_m1024_513 (q : ℕ) : step (step (step (step (1024 * q + 513)))) = 324 * q + 163 := by
  rw [step3_m1024_513 q]
  unfold step
  have h3n1 : 3 * (432 * q + 217) + 1 = 2 ^ 2 * (324 * q + 163) := by ring
  have h_odd : (324 * q + 163) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (432 * q + 217) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (324 * q + 163) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (324 * q + 163) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (324 * q + 163) (by positivity)]

theorem step5_m1024_513 (q : ℕ) : step (step (step (step (step (1024 * q + 513))))) = 486 * q + 245 := by
  rw [step4_m1024_513 q]
  unfold step
  have h3n1 : 3 * (324 * q + 163) + 1 = 2 ^ 1 * (486 * q + 245) := by ring
  have h_odd : (486 * q + 245) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (324 * q + 163) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (486 * q + 245) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (486 * q + 245) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (486 * q + 245) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 513 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_513 (q : ℕ) (hq : 1024 * q + 513 > 1) :
    step (step (step (step (step (step (1024 * q + 513)))))) < 1024 * q + 513 := by
  rw [step5_m1024_513 q]
  have h_bound : step (486 * q + 245) ≤ 729 * q + 368 := by
    unfold step
    have h3n1 : 3 * (486 * q + 245) + 1 = 2 ^ 1 * (729 * q + 368) := by ring
    have hne : (729 * q + 368) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (486 * q + 245) + 1) = 1 + ν₂ (729 * q + 368) := by
      rw [h3n1, ν₂_mul (2 ^ 1) (729 * q + 368) (by positivity) hne, ν₂_pow_two' 1]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 368) (2 ^ ν₂ (729 * q + 368)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_575 (q : ℕ) : step (1024 * q + 575) = 1536 * q + 863 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 575) + 1 = 2 ^ 1 * (1536 * q + 863) := by ring
  have h_odd : (1536 * q + 863) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 575) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 863) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 863) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 863) (by positivity)]

theorem step2_m1024_575 (q : ℕ) : step (step (1024 * q + 575)) = 2304 * q + 1295 := by
  rw [step_m1024_575 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 863) + 1 = 2 ^ 1 * (2304 * q + 1295) := by ring
  have h_odd : (2304 * q + 1295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 863) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 1295) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 1295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 1295) (by positivity)]

theorem step3_m1024_575 (q : ℕ) : step (step (step (1024 * q + 575))) = 3456 * q + 1943 := by
  rw [step2_m1024_575 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 1295) + 1 = 2 ^ 1 * (3456 * q + 1943) := by ring
  have h_odd : (3456 * q + 1943) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 1295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 1943) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 1943) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 1943) (by positivity)]

theorem step4_m1024_575 (q : ℕ) : step (step (step (step (1024 * q + 575)))) = 5184 * q + 2915 := by
  rw [step3_m1024_575 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 1943) + 1 = 2 ^ 1 * (5184 * q + 2915) := by ring
  have h_odd : (5184 * q + 2915) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 1943) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (5184 * q + 2915) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (5184 * q + 2915) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 2915) (by positivity)]

theorem step5_m1024_575 (q : ℕ) : step (step (step (step (step (1024 * q + 575))))) = 7776 * q + 4373 := by
  rw [step4_m1024_575 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 2915) + 1 = 2 ^ 1 * (7776 * q + 4373) := by ring
  have h_odd : (7776 * q + 4373) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 2915) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 4373) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 4373) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 4373) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 575 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_575 (q : ℕ) (hq : 1024 * q + 575 > 1) :
    step (step (step (step (step (step (1024 * q + 575)))))) < 1024 * q + 575 := by
  rw [step5_m1024_575 q]
  have h_bound : step (7776 * q + 4373) ≤ 729 * q + 410 := by
    unfold step
    have h3n1 : 3 * (7776 * q + 4373) + 1 = 2 ^ 5 * (729 * q + 410) := by ring
    have hne : (729 * q + 410) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (7776 * q + 4373) + 1) = 5 + ν₂ (729 * q + 410) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (729 * q + 410) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 410) (2 ^ ν₂ (729 * q + 410)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_583 (q : ℕ) : step (1024 * q + 583) = 1536 * q + 875 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 583) + 1 = 2 ^ 1 * (1536 * q + 875) := by ring
  have h_odd : (1536 * q + 875) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 583) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 875) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 875) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 875) (by positivity)]

theorem step2_m1024_583 (q : ℕ) : step (step (1024 * q + 583)) = 2304 * q + 1313 := by
  rw [step_m1024_583 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 875) + 1 = 2 ^ 1 * (2304 * q + 1313) := by ring
  have h_odd : (2304 * q + 1313) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 875) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 1313) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 1313) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 1313) (by positivity)]

theorem step3_m1024_583 (q : ℕ) : step (step (step (1024 * q + 583))) = 1728 * q + 985 := by
  rw [step2_m1024_583 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 1313) + 1 = 2 ^ 2 * (1728 * q + 985) := by ring
  have h_odd : (1728 * q + 985) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 1313) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1728 * q + 985) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1728 * q + 985) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 985) (by positivity)]

theorem step4_m1024_583 (q : ℕ) : step (step (step (step (1024 * q + 583)))) = 1296 * q + 739 := by
  rw [step3_m1024_583 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 985) + 1 = 2 ^ 2 * (1296 * q + 739) := by ring
  have h_odd : (1296 * q + 739) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 985) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1296 * q + 739) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1296 * q + 739) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 739) (by positivity)]

theorem step5_m1024_583 (q : ℕ) : step (step (step (step (step (1024 * q + 583))))) = 1944 * q + 1109 := by
  rw [step4_m1024_583 q]
  unfold step
  have h3n1 : 3 * (1296 * q + 739) + 1 = 2 ^ 1 * (1944 * q + 1109) := by ring
  have h_odd : (1944 * q + 1109) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1296 * q + 739) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1944 * q + 1109) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1944 * q + 1109) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 1109) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 583 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_583 (q : ℕ) (hq : 1024 * q + 583 > 1) :
    step (step (step (step (step (step (1024 * q + 583)))))) < 1024 * q + 583 := by
  rw [step5_m1024_583 q]
  have h_bound : step (1944 * q + 1109) ≤ 729 * q + 416 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 1109) + 1 = 2 ^ 3 * (729 * q + 416) := by ring
    have hne : (729 * q + 416) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 1109) + 1) = 3 + ν₂ (729 * q + 416) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 416) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 416) (2 ^ ν₂ (729 * q + 416)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_735 (q : ℕ) : step (1024 * q + 735) = 1536 * q + 1103 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 735) + 1 = 2 ^ 1 * (1536 * q + 1103) := by ring
  have h_odd : (1536 * q + 1103) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 735) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 1103) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 1103) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 1103) (by positivity)]

theorem step2_m1024_735 (q : ℕ) : step (step (1024 * q + 735)) = 2304 * q + 1655 := by
  rw [step_m1024_735 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 1103) + 1 = 2 ^ 1 * (2304 * q + 1655) := by ring
  have h_odd : (2304 * q + 1655) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 1103) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 1655) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 1655) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 1655) (by positivity)]

theorem step3_m1024_735 (q : ℕ) : step (step (step (1024 * q + 735))) = 3456 * q + 2483 := by
  rw [step2_m1024_735 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 1655) + 1 = 2 ^ 1 * (3456 * q + 2483) := by ring
  have h_odd : (3456 * q + 2483) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 1655) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 2483) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 2483) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 2483) (by positivity)]

theorem step4_m1024_735 (q : ℕ) : step (step (step (step (1024 * q + 735)))) = 5184 * q + 3725 := by
  rw [step3_m1024_735 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 2483) + 1 = 2 ^ 1 * (5184 * q + 3725) := by ring
  have h_odd : (5184 * q + 3725) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 2483) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (5184 * q + 3725) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (5184 * q + 3725) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 3725) (by positivity)]

theorem step5_m1024_735 (q : ℕ) : step (step (step (step (step (1024 * q + 735))))) = 1944 * q + 1397 := by
  rw [step4_m1024_735 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 3725) + 1 = 2 ^ 3 * (1944 * q + 1397) := by ring
  have h_odd : (1944 * q + 1397) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 3725) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (1944 * q + 1397) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (1944 * q + 1397) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 1397) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 735 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_735 (q : ℕ) (hq : 1024 * q + 735 > 1) :
    step (step (step (step (step (step (1024 * q + 735)))))) < 1024 * q + 735 := by
  rw [step5_m1024_735 q]
  have h_bound : step (1944 * q + 1397) ≤ 729 * q + 524 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 1397) + 1 = 2 ^ 3 * (729 * q + 524) := by ring
    have hne : (729 * q + 524) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 1397) + 1) = 3 + ν₂ (729 * q + 524) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 524) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 524) (2 ^ ν₂ (729 * q + 524)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_809 (q : ℕ) : step (1024 * q + 809) = 768 * q + 607 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 809) + 1 = 2 ^ 2 * (768 * q + 607) := by ring
  have h_odd : (768 * q + 607) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 809) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (768 * q + 607) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (768 * q + 607) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (768 * q + 607) (by positivity)]

theorem step2_m1024_809 (q : ℕ) : step (step (1024 * q + 809)) = 1152 * q + 911 := by
  rw [step_m1024_809 q]
  unfold step
  have h3n1 : 3 * (768 * q + 607) + 1 = 2 ^ 1 * (1152 * q + 911) := by ring
  have h_odd : (1152 * q + 911) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (768 * q + 607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1152 * q + 911) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1152 * q + 911) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 911) (by positivity)]

theorem step3_m1024_809 (q : ℕ) : step (step (step (1024 * q + 809))) = 1728 * q + 1367 := by
  rw [step2_m1024_809 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 911) + 1 = 2 ^ 1 * (1728 * q + 1367) := by ring
  have h_odd : (1728 * q + 1367) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1728 * q + 1367) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1728 * q + 1367) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 1367) (by positivity)]

theorem step4_m1024_809 (q : ℕ) : step (step (step (step (1024 * q + 809)))) = 2592 * q + 2051 := by
  rw [step3_m1024_809 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 1367) + 1 = 2 ^ 1 * (2592 * q + 2051) := by ring
  have h_odd : (2592 * q + 2051) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 1367) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2592 * q + 2051) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2592 * q + 2051) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 2051) (by positivity)]

theorem step5_m1024_809 (q : ℕ) : step (step (step (step (step (1024 * q + 809))))) = 3888 * q + 3077 := by
  rw [step4_m1024_809 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 2051) + 1 = 2 ^ 1 * (3888 * q + 3077) := by ring
  have h_odd : (3888 * q + 3077) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 2051) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3888 * q + 3077) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3888 * q + 3077) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3888 * q + 3077) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 809 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_809 (q : ℕ) (hq : 1024 * q + 809 > 1) :
    step (step (step (step (step (step (1024 * q + 809)))))) < 1024 * q + 809 := by
  rw [step5_m1024_809 q]
  have h_bound : step (3888 * q + 3077) ≤ 729 * q + 577 := by
    unfold step
    have h3n1 : 3 * (3888 * q + 3077) + 1 = 2 ^ 4 * (729 * q + 577) := by ring
    have hne : (729 * q + 577) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (3888 * q + 3077) + 1) = 4 + ν₂ (729 * q + 577) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (729 * q + 577) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 577) (2 ^ ν₂ (729 * q + 577)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_815 (q : ℕ) : step (1024 * q + 815) = 1536 * q + 1223 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 815) + 1 = 2 ^ 1 * (1536 * q + 1223) := by ring
  have h_odd : (1536 * q + 1223) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 815) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 1223) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 1223) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 1223) (by positivity)]

theorem step2_m1024_815 (q : ℕ) : step (step (1024 * q + 815)) = 2304 * q + 1835 := by
  rw [step_m1024_815 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 1223) + 1 = 2 ^ 1 * (2304 * q + 1835) := by ring
  have h_odd : (2304 * q + 1835) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 1223) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 1835) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 1835) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 1835) (by positivity)]

theorem step3_m1024_815 (q : ℕ) : step (step (step (1024 * q + 815))) = 3456 * q + 2753 := by
  rw [step2_m1024_815 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 1835) + 1 = 2 ^ 1 * (3456 * q + 2753) := by ring
  have h_odd : (3456 * q + 2753) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 1835) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 2753) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 2753) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 2753) (by positivity)]

theorem step4_m1024_815 (q : ℕ) : step (step (step (step (1024 * q + 815)))) = 2592 * q + 2065 := by
  rw [step3_m1024_815 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 2753) + 1 = 2 ^ 2 * (2592 * q + 2065) := by ring
  have h_odd : (2592 * q + 2065) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 2753) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (2592 * q + 2065) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (2592 * q + 2065) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 2065) (by positivity)]

theorem step5_m1024_815 (q : ℕ) : step (step (step (step (step (1024 * q + 815))))) = 1944 * q + 1549 := by
  rw [step4_m1024_815 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 2065) + 1 = 2 ^ 2 * (1944 * q + 1549) := by ring
  have h_odd : (1944 * q + 1549) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 2065) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1944 * q + 1549) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1944 * q + 1549) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 1549) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 815 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_815 (q : ℕ) (hq : 1024 * q + 815 > 1) :
    step (step (step (step (step (step (1024 * q + 815)))))) < 1024 * q + 815 := by
  rw [step5_m1024_815 q]
  have h_bound : step (1944 * q + 1549) ≤ 729 * q + 581 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 1549) + 1 = 2 ^ 3 * (729 * q + 581) := by ring
    have hne : (729 * q + 581) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 1549) + 1) = 3 + ν₂ (729 * q + 581) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 581) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 581) (2 ^ ν₂ (729 * q + 581)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_923 (q : ℕ) : step (1024 * q + 923) = 1536 * q + 1385 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 923) + 1 = 2 ^ 1 * (1536 * q + 1385) := by ring
  have h_odd : (1536 * q + 1385) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 923) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 1385) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 1385) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 1385) (by positivity)]

theorem step2_m1024_923 (q : ℕ) : step (step (1024 * q + 923)) = 1152 * q + 1039 := by
  rw [step_m1024_923 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 1385) + 1 = 2 ^ 2 * (1152 * q + 1039) := by ring
  have h_odd : (1152 * q + 1039) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 1385) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1152 * q + 1039) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1152 * q + 1039) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 1039) (by positivity)]

theorem step3_m1024_923 (q : ℕ) : step (step (step (1024 * q + 923))) = 1728 * q + 1559 := by
  rw [step2_m1024_923 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 1039) + 1 = 2 ^ 1 * (1728 * q + 1559) := by ring
  have h_odd : (1728 * q + 1559) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 1039) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1728 * q + 1559) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1728 * q + 1559) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 1559) (by positivity)]

theorem step4_m1024_923 (q : ℕ) : step (step (step (step (1024 * q + 923)))) = 2592 * q + 2339 := by
  rw [step3_m1024_923 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 1559) + 1 = 2 ^ 1 * (2592 * q + 2339) := by ring
  have h_odd : (2592 * q + 2339) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 1559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2592 * q + 2339) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2592 * q + 2339) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 2339) (by positivity)]

theorem step5_m1024_923 (q : ℕ) : step (step (step (step (step (1024 * q + 923))))) = 3888 * q + 3509 := by
  rw [step4_m1024_923 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 2339) + 1 = 2 ^ 1 * (3888 * q + 3509) := by ring
  have h_odd : (3888 * q + 3509) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 2339) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3888 * q + 3509) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3888 * q + 3509) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3888 * q + 3509) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 923 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_923 (q : ℕ) (hq : 1024 * q + 923 > 1) :
    step (step (step (step (step (step (1024 * q + 923)))))) < 1024 * q + 923 := by
  rw [step5_m1024_923 q]
  have h_bound : step (3888 * q + 3509) ≤ 729 * q + 658 := by
    unfold step
    have h3n1 : 3 * (3888 * q + 3509) + 1 = 2 ^ 4 * (729 * q + 658) := by ring
    have hne : (729 * q + 658) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (3888 * q + 3509) + 1) = 4 + ν₂ (729 * q + 658) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (729 * q + 658) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 658) (2 ^ ν₂ (729 * q + 658)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_975 (q : ℕ) : step (1024 * q + 975) = 1536 * q + 1463 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 975) + 1 = 2 ^ 1 * (1536 * q + 1463) := by ring
  have h_odd : (1536 * q + 1463) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 975) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 1463) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 1463) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 1463) (by positivity)]

theorem step2_m1024_975 (q : ℕ) : step (step (1024 * q + 975)) = 2304 * q + 2195 := by
  rw [step_m1024_975 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 1463) + 1 = 2 ^ 1 * (2304 * q + 2195) := by ring
  have h_odd : (2304 * q + 2195) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 1463) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 2195) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 2195) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 2195) (by positivity)]

theorem step3_m1024_975 (q : ℕ) : step (step (step (1024 * q + 975))) = 3456 * q + 3293 := by
  rw [step2_m1024_975 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 2195) + 1 = 2 ^ 1 * (3456 * q + 3293) := by ring
  have h_odd : (3456 * q + 3293) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 2195) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 3293) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 3293) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 3293) (by positivity)]

theorem step4_m1024_975 (q : ℕ) : step (step (step (step (1024 * q + 975)))) = 1296 * q + 1235 := by
  rw [step3_m1024_975 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 3293) + 1 = 2 ^ 3 * (1296 * q + 1235) := by ring
  have h_odd : (1296 * q + 1235) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 3293) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (1296 * q + 1235) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (1296 * q + 1235) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 1235) (by positivity)]

theorem step5_m1024_975 (q : ℕ) : step (step (step (step (step (1024 * q + 975))))) = 1944 * q + 1853 := by
  rw [step4_m1024_975 q]
  unfold step
  have h3n1 : 3 * (1296 * q + 1235) + 1 = 2 ^ 1 * (1944 * q + 1853) := by ring
  have h_odd : (1944 * q + 1853) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1296 * q + 1235) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1944 * q + 1853) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1944 * q + 1853) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 1853) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 975 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_975 (q : ℕ) (hq : 1024 * q + 975 > 1) :
    step (step (step (step (step (step (1024 * q + 975)))))) < 1024 * q + 975 := by
  rw [step5_m1024_975 q]
  have h_bound : step (1944 * q + 1853) ≤ 729 * q + 695 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 1853) + 1 = 2 ^ 3 * (729 * q + 695) := by ring
    have hne : (729 * q + 695) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 1853) + 1) = 3 + ν₂ (729 * q + 695) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 695) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 695) (2 ^ ν₂ (729 * q + 695)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m1024_999 (q : ℕ) : step (1024 * q + 999) = 1536 * q + 1499 := by
  unfold step
  have h3n1 : 3 * (1024 * q + 999) + 1 = 2 ^ 1 * (1536 * q + 1499) := by ring
  have h_odd : (1536 * q + 1499) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1024 * q + 999) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1536 * q + 1499) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1536 * q + 1499) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 1499) (by positivity)]

theorem step2_m1024_999 (q : ℕ) : step (step (1024 * q + 999)) = 2304 * q + 2249 := by
  rw [step_m1024_999 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 1499) + 1 = 2 ^ 1 * (2304 * q + 2249) := by ring
  have h_odd : (2304 * q + 2249) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 1499) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2304 * q + 2249) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2304 * q + 2249) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 2249) (by positivity)]

theorem step3_m1024_999 (q : ℕ) : step (step (step (1024 * q + 999))) = 1728 * q + 1687 := by
  rw [step2_m1024_999 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 2249) + 1 = 2 ^ 2 * (1728 * q + 1687) := by ring
  have h_odd : (1728 * q + 1687) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 2249) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1728 * q + 1687) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1728 * q + 1687) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 1687) (by positivity)]

theorem step4_m1024_999 (q : ℕ) : step (step (step (step (1024 * q + 999)))) = 2592 * q + 2531 := by
  rw [step3_m1024_999 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 1687) + 1 = 2 ^ 1 * (2592 * q + 2531) := by ring
  have h_odd : (2592 * q + 2531) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 1687) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (2592 * q + 2531) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (2592 * q + 2531) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 2531) (by positivity)]

theorem step5_m1024_999 (q : ℕ) : step (step (step (step (step (1024 * q + 999))))) = 3888 * q + 3797 := by
  rw [step4_m1024_999 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 2531) + 1 = 2 ^ 1 * (3888 * q + 3797) := by ring
  have h_odd : (3888 * q + 3797) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 2531) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3888 * q + 3797) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3888 * q + 3797) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3888 * q + 3797) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 999 (mod 1024) ⇒ step^6(n) < n. -/
theorem descent_m1024_999 (q : ℕ) (hq : 1024 * q + 999 > 1) :
    step (step (step (step (step (step (1024 * q + 999)))))) < 1024 * q + 999 := by
  rw [step5_m1024_999 q]
  have h_bound : step (3888 * q + 3797) ≤ 729 * q + 712 := by
    unfold step
    have h3n1 : 3 * (3888 * q + 3797) + 1 = 2 ^ 4 * (729 * q + 712) := by ring
    have hne : (729 * q + 712) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (3888 * q + 3797) + 1) = 4 + ν₂ (729 * q + 712) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (729 * q + 712) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 712) (2 ^ ν₂ (729 * q + 712)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m2048_1025 (q : ℕ) : step (2048 * q + 1025) = 1536 * q + 769 := by
  unfold step
  have h3n1 : 3 * (2048 * q + 1025) + 1 = 2 ^ 2 * (1536 * q + 769) := by ring
  have h_odd : (1536 * q + 769) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2048 * q + 1025) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1536 * q + 769) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1536 * q + 769) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1536 * q + 769) (by positivity)]

theorem step2_m2048_1025 (q : ℕ) : step (step (2048 * q + 1025)) = 1152 * q + 577 := by
  rw [step_m2048_1025 q]
  unfold step
  have h3n1 : 3 * (1536 * q + 769) + 1 = 2 ^ 2 * (1152 * q + 577) := by ring
  have h_odd : (1152 * q + 577) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1536 * q + 769) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1152 * q + 577) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1152 * q + 577) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1152 * q + 577) (by positivity)]

theorem step3_m2048_1025 (q : ℕ) : step (step (step (2048 * q + 1025))) = 864 * q + 433 := by
  rw [step2_m2048_1025 q]
  unfold step
  have h3n1 : 3 * (1152 * q + 577) + 1 = 2 ^ 2 * (864 * q + 433) := by ring
  have h_odd : (864 * q + 433) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1152 * q + 577) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (864 * q + 433) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (864 * q + 433) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (864 * q + 433) (by positivity)]

theorem step4_m2048_1025 (q : ℕ) : step (step (step (step (2048 * q + 1025)))) = 648 * q + 325 := by
  rw [step3_m2048_1025 q]
  unfold step
  have h3n1 : 3 * (864 * q + 433) + 1 = 2 ^ 2 * (648 * q + 325) := by ring
  have h_odd : (648 * q + 325) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (864 * q + 433) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (648 * q + 325) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (648 * q + 325) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (648 * q + 325) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1025 (mod 2048) ⇒ step^5(n) < n. -/
theorem descent_m2048_1025 (q : ℕ) (hq : 2048 * q + 1025 > 1) :
    step (step (step (step (step (2048 * q + 1025))))) < 2048 * q + 1025 := by
  rw [step4_m2048_1025 q]
  have h_bound : step (648 * q + 325) ≤ 243 * q + 122 := by
    unfold step
    have h3n1 : 3 * (648 * q + 325) + 1 = 2 ^ 3 * (243 * q + 122) := by ring
    have hne : (243 * q + 122) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (648 * q + 325) + 1) = 3 + ν₂ (243 * q + 122) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (243 * q + 122) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (243 * q + 122) (2 ^ ν₂ (243 * q + 122)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_231 (q : ℕ) : step (4096 * q + 231) = 6144 * q + 347 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 231) + 1 = 2 ^ 1 * (6144 * q + 347) := by ring
  have h_odd : (6144 * q + 347) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 231) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 347) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 347) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 347) (by positivity)]

theorem step2_m4096_231 (q : ℕ) : step (step (4096 * q + 231)) = 9216 * q + 521 := by
  rw [step_m4096_231 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 347) + 1 = 2 ^ 1 * (9216 * q + 521) := by ring
  have h_odd : (9216 * q + 521) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 347) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 521) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 521) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 521) (by positivity)]

theorem step3_m4096_231 (q : ℕ) : step (step (step (4096 * q + 231))) = 6912 * q + 391 := by
  rw [step2_m4096_231 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 521) + 1 = 2 ^ 2 * (6912 * q + 391) := by ring
  have h_odd : (6912 * q + 391) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 521) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 391) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 391) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 391) (by positivity)]

theorem step4_m4096_231 (q : ℕ) : step (step (step (step (4096 * q + 231)))) = 10368 * q + 587 := by
  rw [step3_m4096_231 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 391) + 1 = 2 ^ 1 * (10368 * q + 587) := by ring
  have h_odd : (10368 * q + 587) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 391) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 587) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 587) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 587) (by positivity)]

theorem step5_m4096_231 (q : ℕ) : step (step (step (step (step (4096 * q + 231))))) = 15552 * q + 881 := by
  rw [step4_m4096_231 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 587) + 1 = 2 ^ 1 * (15552 * q + 881) := by ring
  have h_odd : (15552 * q + 881) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 587) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 881) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 881) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 881) (by positivity)]

theorem step6_m4096_231 (q : ℕ) : step (step (step (step (step (step (4096 * q + 231)))))) = 11664 * q + 661 := by
  rw [step5_m4096_231 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 881) + 1 = 2 ^ 2 * (11664 * q + 661) := by ring
  have h_odd : (11664 * q + 661) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 881) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 661) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 661) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 661) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 231 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_231 (q : ℕ) (hq : 4096 * q + 231 > 1) :
    step (step (step (step (step (step (step (4096 * q + 231))))))) < 4096 * q + 231 := by
  rw [step6_m4096_231 q]
  have h_bound : step (11664 * q + 661) ≤ 2187 * q + 124 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 661) + 1 = 2 ^ 4 * (2187 * q + 124) := by ring
    have hne : (2187 * q + 124) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 661) + 1) = 4 + ν₂ (2187 * q + 124) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 124) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 124) (2 ^ ν₂ (2187 * q + 124)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_383 (q : ℕ) : step (4096 * q + 383) = 6144 * q + 575 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 383) + 1 = 2 ^ 1 * (6144 * q + 575) := by ring
  have h_odd : (6144 * q + 575) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 383) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 575) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 575) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 575) (by positivity)]

theorem step2_m4096_383 (q : ℕ) : step (step (4096 * q + 383)) = 9216 * q + 863 := by
  rw [step_m4096_383 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 575) + 1 = 2 ^ 1 * (9216 * q + 863) := by ring
  have h_odd : (9216 * q + 863) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 575) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 863) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 863) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 863) (by positivity)]

theorem step3_m4096_383 (q : ℕ) : step (step (step (4096 * q + 383))) = 13824 * q + 1295 := by
  rw [step2_m4096_383 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 863) + 1 = 2 ^ 1 * (13824 * q + 1295) := by ring
  have h_odd : (13824 * q + 1295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 863) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 1295) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 1295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 1295) (by positivity)]

theorem step4_m4096_383 (q : ℕ) : step (step (step (step (4096 * q + 383)))) = 20736 * q + 1943 := by
  rw [step3_m4096_383 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 1295) + 1 = 2 ^ 1 * (20736 * q + 1943) := by ring
  have h_odd : (20736 * q + 1943) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 1295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 1943) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 1943) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 1943) (by positivity)]

theorem step5_m4096_383 (q : ℕ) : step (step (step (step (step (4096 * q + 383))))) = 31104 * q + 2915 := by
  rw [step4_m4096_383 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 1943) + 1 = 2 ^ 1 * (31104 * q + 2915) := by ring
  have h_odd : (31104 * q + 2915) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 1943) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 2915) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 2915) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 2915) (by positivity)]

theorem step6_m4096_383 (q : ℕ) : step (step (step (step (step (step (4096 * q + 383)))))) = 46656 * q + 4373 := by
  rw [step5_m4096_383 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 2915) + 1 = 2 ^ 1 * (46656 * q + 4373) := by ring
  have h_odd : (46656 * q + 4373) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 2915) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 4373) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 4373) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 4373) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 383 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_383 (q : ℕ) (hq : 4096 * q + 383 > 1) :
    step (step (step (step (step (step (step (4096 * q + 383))))))) < 4096 * q + 383 := by
  rw [step6_m4096_383 q]
  have h_bound : step (46656 * q + 4373) ≤ 2187 * q + 205 := by
    unfold step
    have h3n1 : 3 * (46656 * q + 4373) + 1 = 2 ^ 6 * (2187 * q + 205) := by ring
    have hne : (2187 * q + 205) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (46656 * q + 4373) + 1) = 6 + ν₂ (2187 * q + 205) := by
      rw [h3n1, ν₂_mul (2 ^ 6) (2187 * q + 205) (by positivity) hne, ν₂_pow_two' 6]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 205) (2 ^ ν₂ (2187 * q + 205)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_463 (q : ℕ) : step (4096 * q + 463) = 6144 * q + 695 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 463) + 1 = 2 ^ 1 * (6144 * q + 695) := by ring
  have h_odd : (6144 * q + 695) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 463) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 695) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 695) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 695) (by positivity)]

theorem step2_m4096_463 (q : ℕ) : step (step (4096 * q + 463)) = 9216 * q + 1043 := by
  rw [step_m4096_463 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 695) + 1 = 2 ^ 1 * (9216 * q + 1043) := by ring
  have h_odd : (9216 * q + 1043) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 695) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 1043) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 1043) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 1043) (by positivity)]

theorem step3_m4096_463 (q : ℕ) : step (step (step (4096 * q + 463))) = 13824 * q + 1565 := by
  rw [step2_m4096_463 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 1043) + 1 = 2 ^ 1 * (13824 * q + 1565) := by ring
  have h_odd : (13824 * q + 1565) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 1043) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 1565) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 1565) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 1565) (by positivity)]

theorem step4_m4096_463 (q : ℕ) : step (step (step (step (4096 * q + 463)))) = 5184 * q + 587 := by
  rw [step3_m4096_463 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 1565) + 1 = 2 ^ 3 * (5184 * q + 587) := by ring
  have h_odd : (5184 * q + 587) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 1565) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (5184 * q + 587) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (5184 * q + 587) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 587) (by positivity)]

theorem step5_m4096_463 (q : ℕ) : step (step (step (step (step (4096 * q + 463))))) = 7776 * q + 881 := by
  rw [step4_m4096_463 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 587) + 1 = 2 ^ 1 * (7776 * q + 881) := by ring
  have h_odd : (7776 * q + 881) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 587) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 881) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 881) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 881) (by positivity)]

theorem step6_m4096_463 (q : ℕ) : step (step (step (step (step (step (4096 * q + 463)))))) = 5832 * q + 661 := by
  rw [step5_m4096_463 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 881) + 1 = 2 ^ 2 * (5832 * q + 661) := by ring
  have h_odd : (5832 * q + 661) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 881) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 661) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 661) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 661) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 463 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_463 (q : ℕ) (hq : 4096 * q + 463 > 1) :
    step (step (step (step (step (step (step (4096 * q + 463))))))) < 4096 * q + 463 := by
  rw [step6_m4096_463 q]
  have h_bound : step (5832 * q + 661) ≤ 2187 * q + 248 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 661) + 1 = 2 ^ 3 * (2187 * q + 248) := by ring
    have hne : (2187 * q + 248) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 661) + 1) = 3 + ν₂ (2187 * q + 248) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 248) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 248) (2 ^ ν₂ (2187 * q + 248)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_489 (q : ℕ) : step (4096 * q + 489) = 3072 * q + 367 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 489) + 1 = 2 ^ 2 * (3072 * q + 367) := by ring
  have h_odd : (3072 * q + 367) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 489) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 367) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 367) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 367) (by positivity)]

theorem step2_m4096_489 (q : ℕ) : step (step (4096 * q + 489)) = 4608 * q + 551 := by
  rw [step_m4096_489 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 367) + 1 = 2 ^ 1 * (4608 * q + 551) := by ring
  have h_odd : (4608 * q + 551) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 367) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 551) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 551) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 551) (by positivity)]

theorem step3_m4096_489 (q : ℕ) : step (step (step (4096 * q + 489))) = 6912 * q + 827 := by
  rw [step2_m4096_489 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 551) + 1 = 2 ^ 1 * (6912 * q + 827) := by ring
  have h_odd : (6912 * q + 827) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 551) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 827) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 827) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 827) (by positivity)]

theorem step4_m4096_489 (q : ℕ) : step (step (step (step (4096 * q + 489)))) = 10368 * q + 1241 := by
  rw [step3_m4096_489 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 827) + 1 = 2 ^ 1 * (10368 * q + 1241) := by ring
  have h_odd : (10368 * q + 1241) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 827) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 1241) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 1241) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 1241) (by positivity)]

theorem step5_m4096_489 (q : ℕ) : step (step (step (step (step (4096 * q + 489))))) = 7776 * q + 931 := by
  rw [step4_m4096_489 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 1241) + 1 = 2 ^ 2 * (7776 * q + 931) := by ring
  have h_odd : (7776 * q + 931) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 1241) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 931) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 931) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 931) (by positivity)]

theorem step6_m4096_489 (q : ℕ) : step (step (step (step (step (step (4096 * q + 489)))))) = 11664 * q + 1397 := by
  rw [step5_m4096_489 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 931) + 1 = 2 ^ 1 * (11664 * q + 1397) := by ring
  have h_odd : (11664 * q + 1397) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 931) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 1397) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 1397) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 1397) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 489 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_489 (q : ℕ) (hq : 4096 * q + 489 > 1) :
    step (step (step (step (step (step (step (4096 * q + 489))))))) < 4096 * q + 489 := by
  rw [step6_m4096_489 q]
  have h_bound : step (11664 * q + 1397) ≤ 2187 * q + 262 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 1397) + 1 = 2 ^ 4 * (2187 * q + 262) := by ring
    have hne : (2187 * q + 262) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 1397) + 1) = 4 + ν₂ (2187 * q + 262) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 262) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 262) (2 ^ ν₂ (2187 * q + 262)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_615 (q : ℕ) : step (4096 * q + 615) = 6144 * q + 923 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 615) + 1 = 2 ^ 1 * (6144 * q + 923) := by ring
  have h_odd : (6144 * q + 923) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 615) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 923) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 923) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 923) (by positivity)]

theorem step2_m4096_615 (q : ℕ) : step (step (4096 * q + 615)) = 9216 * q + 1385 := by
  rw [step_m4096_615 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 923) + 1 = 2 ^ 1 * (9216 * q + 1385) := by ring
  have h_odd : (9216 * q + 1385) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 923) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 1385) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 1385) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 1385) (by positivity)]

theorem step3_m4096_615 (q : ℕ) : step (step (step (4096 * q + 615))) = 6912 * q + 1039 := by
  rw [step2_m4096_615 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 1385) + 1 = 2 ^ 2 * (6912 * q + 1039) := by ring
  have h_odd : (6912 * q + 1039) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 1385) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 1039) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 1039) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 1039) (by positivity)]

theorem step4_m4096_615 (q : ℕ) : step (step (step (step (4096 * q + 615)))) = 10368 * q + 1559 := by
  rw [step3_m4096_615 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 1039) + 1 = 2 ^ 1 * (10368 * q + 1559) := by ring
  have h_odd : (10368 * q + 1559) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 1039) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 1559) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 1559) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 1559) (by positivity)]

theorem step5_m4096_615 (q : ℕ) : step (step (step (step (step (4096 * q + 615))))) = 15552 * q + 2339 := by
  rw [step4_m4096_615 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 1559) + 1 = 2 ^ 1 * (15552 * q + 2339) := by ring
  have h_odd : (15552 * q + 2339) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 1559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 2339) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 2339) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 2339) (by positivity)]

theorem step6_m4096_615 (q : ℕ) : step (step (step (step (step (step (4096 * q + 615)))))) = 23328 * q + 3509 := by
  rw [step5_m4096_615 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 2339) + 1 = 2 ^ 1 * (23328 * q + 3509) := by ring
  have h_odd : (23328 * q + 3509) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 2339) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 3509) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 3509) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 3509) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 615 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_615 (q : ℕ) (hq : 4096 * q + 615 > 1) :
    step (step (step (step (step (step (step (4096 * q + 615))))))) < 4096 * q + 615 := by
  rw [step6_m4096_615 q]
  have h_bound : step (23328 * q + 3509) ≤ 2187 * q + 329 := by
    unfold step
    have h3n1 : 3 * (23328 * q + 3509) + 1 = 2 ^ 5 * (2187 * q + 329) := by ring
    have hne : (2187 * q + 329) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (23328 * q + 3509) + 1) = 5 + ν₂ (2187 * q + 329) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (2187 * q + 329) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 329) (2 ^ ν₂ (2187 * q + 329)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_777 (q : ℕ) : step (4096 * q + 777) = 3072 * q + 583 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 777) + 1 = 2 ^ 2 * (3072 * q + 583) := by ring
  have h_odd : (3072 * q + 583) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 777) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 583) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 583) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 583) (by positivity)]

theorem step2_m4096_777 (q : ℕ) : step (step (4096 * q + 777)) = 4608 * q + 875 := by
  rw [step_m4096_777 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 583) + 1 = 2 ^ 1 * (4608 * q + 875) := by ring
  have h_odd : (4608 * q + 875) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 583) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 875) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 875) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 875) (by positivity)]

theorem step3_m4096_777 (q : ℕ) : step (step (step (4096 * q + 777))) = 6912 * q + 1313 := by
  rw [step2_m4096_777 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 875) + 1 = 2 ^ 1 * (6912 * q + 1313) := by ring
  have h_odd : (6912 * q + 1313) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 875) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 1313) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 1313) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 1313) (by positivity)]

theorem step4_m4096_777 (q : ℕ) : step (step (step (step (4096 * q + 777)))) = 5184 * q + 985 := by
  rw [step3_m4096_777 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 1313) + 1 = 2 ^ 2 * (5184 * q + 985) := by ring
  have h_odd : (5184 * q + 985) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 1313) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 985) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 985) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 985) (by positivity)]

theorem step5_m4096_777 (q : ℕ) : step (step (step (step (step (4096 * q + 777))))) = 3888 * q + 739 := by
  rw [step4_m4096_777 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 985) + 1 = 2 ^ 2 * (3888 * q + 739) := by ring
  have h_odd : (3888 * q + 739) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 985) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3888 * q + 739) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3888 * q + 739) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3888 * q + 739) (by positivity)]

theorem step6_m4096_777 (q : ℕ) : step (step (step (step (step (step (4096 * q + 777)))))) = 5832 * q + 1109 := by
  rw [step5_m4096_777 q]
  unfold step
  have h3n1 : 3 * (3888 * q + 739) + 1 = 2 ^ 1 * (5832 * q + 1109) := by ring
  have h_odd : (5832 * q + 1109) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3888 * q + 739) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (5832 * q + 1109) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (5832 * q + 1109) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 1109) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 777 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_777 (q : ℕ) (hq : 4096 * q + 777 > 1) :
    step (step (step (step (step (step (step (4096 * q + 777))))))) < 4096 * q + 777 := by
  rw [step6_m4096_777 q]
  have h_bound : step (5832 * q + 1109) ≤ 2187 * q + 416 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 1109) + 1 = 2 ^ 3 * (2187 * q + 416) := by ring
    have hne : (2187 * q + 416) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 1109) + 1) = 3 + ν₂ (2187 * q + 416) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 416) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 416) (2 ^ ν₂ (2187 * q + 416)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_879 (q : ℕ) : step (4096 * q + 879) = 6144 * q + 1319 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 879) + 1 = 2 ^ 1 * (6144 * q + 1319) := by ring
  have h_odd : (6144 * q + 1319) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 879) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 1319) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 1319) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 1319) (by positivity)]

theorem step2_m4096_879 (q : ℕ) : step (step (4096 * q + 879)) = 9216 * q + 1979 := by
  rw [step_m4096_879 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 1319) + 1 = 2 ^ 1 * (9216 * q + 1979) := by ring
  have h_odd : (9216 * q + 1979) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 1319) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 1979) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 1979) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 1979) (by positivity)]

theorem step3_m4096_879 (q : ℕ) : step (step (step (4096 * q + 879))) = 13824 * q + 2969 := by
  rw [step2_m4096_879 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 1979) + 1 = 2 ^ 1 * (13824 * q + 2969) := by ring
  have h_odd : (13824 * q + 2969) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 1979) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 2969) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 2969) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 2969) (by positivity)]

theorem step4_m4096_879 (q : ℕ) : step (step (step (step (4096 * q + 879)))) = 10368 * q + 2227 := by
  rw [step3_m4096_879 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 2969) + 1 = 2 ^ 2 * (10368 * q + 2227) := by ring
  have h_odd : (10368 * q + 2227) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 2969) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 2227) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 2227) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 2227) (by positivity)]

theorem step5_m4096_879 (q : ℕ) : step (step (step (step (step (4096 * q + 879))))) = 15552 * q + 3341 := by
  rw [step4_m4096_879 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 2227) + 1 = 2 ^ 1 * (15552 * q + 3341) := by ring
  have h_odd : (15552 * q + 3341) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 2227) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 3341) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 3341) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 3341) (by positivity)]

theorem step6_m4096_879 (q : ℕ) : step (step (step (step (step (step (4096 * q + 879)))))) = 5832 * q + 1253 := by
  rw [step5_m4096_879 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 3341) + 1 = 2 ^ 3 * (5832 * q + 1253) := by ring
  have h_odd : (5832 * q + 1253) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 3341) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (5832 * q + 1253) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (5832 * q + 1253) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 1253) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 879 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_879 (q : ℕ) (hq : 4096 * q + 879 > 1) :
    step (step (step (step (step (step (step (4096 * q + 879))))))) < 4096 * q + 879 := by
  rw [step6_m4096_879 q]
  have h_bound : step (5832 * q + 1253) ≤ 2187 * q + 470 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 1253) + 1 = 2 ^ 3 * (2187 * q + 470) := by ring
    have hne : (2187 * q + 470) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 1253) + 1) = 3 + ν₂ (2187 * q + 470) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 470) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 470) (2 ^ ν₂ (2187 * q + 470)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_935 (q : ℕ) : step (4096 * q + 935) = 6144 * q + 1403 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 935) + 1 = 2 ^ 1 * (6144 * q + 1403) := by ring
  have h_odd : (6144 * q + 1403) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 935) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 1403) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 1403) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 1403) (by positivity)]

theorem step2_m4096_935 (q : ℕ) : step (step (4096 * q + 935)) = 9216 * q + 2105 := by
  rw [step_m4096_935 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 1403) + 1 = 2 ^ 1 * (9216 * q + 2105) := by ring
  have h_odd : (9216 * q + 2105) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 1403) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 2105) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 2105) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 2105) (by positivity)]

theorem step3_m4096_935 (q : ℕ) : step (step (step (4096 * q + 935))) = 6912 * q + 1579 := by
  rw [step2_m4096_935 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 2105) + 1 = 2 ^ 2 * (6912 * q + 1579) := by ring
  have h_odd : (6912 * q + 1579) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 2105) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 1579) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 1579) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 1579) (by positivity)]

theorem step4_m4096_935 (q : ℕ) : step (step (step (step (4096 * q + 935)))) = 10368 * q + 2369 := by
  rw [step3_m4096_935 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 1579) + 1 = 2 ^ 1 * (10368 * q + 2369) := by ring
  have h_odd : (10368 * q + 2369) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 1579) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 2369) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 2369) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 2369) (by positivity)]

theorem step5_m4096_935 (q : ℕ) : step (step (step (step (step (4096 * q + 935))))) = 7776 * q + 1777 := by
  rw [step4_m4096_935 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 2369) + 1 = 2 ^ 2 * (7776 * q + 1777) := by ring
  have h_odd : (7776 * q + 1777) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 2369) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 1777) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 1777) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 1777) (by positivity)]

theorem step6_m4096_935 (q : ℕ) : step (step (step (step (step (step (4096 * q + 935)))))) = 5832 * q + 1333 := by
  rw [step5_m4096_935 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 1777) + 1 = 2 ^ 2 * (5832 * q + 1333) := by ring
  have h_odd : (5832 * q + 1333) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 1777) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 1333) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 1333) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 1333) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 935 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_935 (q : ℕ) (hq : 4096 * q + 935 > 1) :
    step (step (step (step (step (step (step (4096 * q + 935))))))) < 4096 * q + 935 := by
  rw [step6_m4096_935 q]
  have h_bound : step (5832 * q + 1333) ≤ 2187 * q + 500 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 1333) + 1 = 2 ^ 3 * (2187 * q + 500) := by ring
    have hne : (2187 * q + 500) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 1333) + 1) = 3 + ν₂ (2187 * q + 500) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 500) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 500) (2 ^ ν₂ (2187 * q + 500)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1019 (q : ℕ) : step (4096 * q + 1019) = 6144 * q + 1529 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1019) + 1 = 2 ^ 1 * (6144 * q + 1529) := by ring
  have h_odd : (6144 * q + 1529) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1019) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 1529) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 1529) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 1529) (by positivity)]

theorem step2_m4096_1019 (q : ℕ) : step (step (4096 * q + 1019)) = 4608 * q + 1147 := by
  rw [step_m4096_1019 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 1529) + 1 = 2 ^ 2 * (4608 * q + 1147) := by ring
  have h_odd : (4608 * q + 1147) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 1529) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 1147) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 1147) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 1147) (by positivity)]

theorem step3_m4096_1019 (q : ℕ) : step (step (step (4096 * q + 1019))) = 6912 * q + 1721 := by
  rw [step2_m4096_1019 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 1147) + 1 = 2 ^ 1 * (6912 * q + 1721) := by ring
  have h_odd : (6912 * q + 1721) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 1147) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 1721) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 1721) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 1721) (by positivity)]

theorem step4_m4096_1019 (q : ℕ) : step (step (step (step (4096 * q + 1019)))) = 5184 * q + 1291 := by
  rw [step3_m4096_1019 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 1721) + 1 = 2 ^ 2 * (5184 * q + 1291) := by ring
  have h_odd : (5184 * q + 1291) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 1721) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 1291) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 1291) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 1291) (by positivity)]

theorem step5_m4096_1019 (q : ℕ) : step (step (step (step (step (4096 * q + 1019))))) = 7776 * q + 1937 := by
  rw [step4_m4096_1019 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 1291) + 1 = 2 ^ 1 * (7776 * q + 1937) := by ring
  have h_odd : (7776 * q + 1937) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 1291) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 1937) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 1937) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 1937) (by positivity)]

theorem step6_m4096_1019 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1019)))))) = 5832 * q + 1453 := by
  rw [step5_m4096_1019 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 1937) + 1 = 2 ^ 2 * (5832 * q + 1453) := by ring
  have h_odd : (5832 * q + 1453) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 1937) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 1453) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 1453) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 1453) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1019 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1019 (q : ℕ) (hq : 4096 * q + 1019 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1019))))))) < 4096 * q + 1019 := by
  rw [step6_m4096_1019 q]
  have h_bound : step (5832 * q + 1453) ≤ 2187 * q + 545 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 1453) + 1 = 2 ^ 3 * (2187 * q + 545) := by ring
    have hne : (2187 * q + 545) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 1453) + 1) = 3 + ν₂ (2187 * q + 545) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 545) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 545) (2 ^ ν₂ (2187 * q + 545)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1087 (q : ℕ) : step (4096 * q + 1087) = 6144 * q + 1631 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1087) + 1 = 2 ^ 1 * (6144 * q + 1631) := by ring
  have h_odd : (6144 * q + 1631) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1087) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 1631) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 1631) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 1631) (by positivity)]

theorem step2_m4096_1087 (q : ℕ) : step (step (4096 * q + 1087)) = 9216 * q + 2447 := by
  rw [step_m4096_1087 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 1631) + 1 = 2 ^ 1 * (9216 * q + 2447) := by ring
  have h_odd : (9216 * q + 2447) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 1631) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 2447) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 2447) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 2447) (by positivity)]

theorem step3_m4096_1087 (q : ℕ) : step (step (step (4096 * q + 1087))) = 13824 * q + 3671 := by
  rw [step2_m4096_1087 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 2447) + 1 = 2 ^ 1 * (13824 * q + 3671) := by ring
  have h_odd : (13824 * q + 3671) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 2447) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 3671) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 3671) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 3671) (by positivity)]

theorem step4_m4096_1087 (q : ℕ) : step (step (step (step (4096 * q + 1087)))) = 20736 * q + 5507 := by
  rw [step3_m4096_1087 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 3671) + 1 = 2 ^ 1 * (20736 * q + 5507) := by ring
  have h_odd : (20736 * q + 5507) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 3671) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 5507) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 5507) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 5507) (by positivity)]

theorem step5_m4096_1087 (q : ℕ) : step (step (step (step (step (4096 * q + 1087))))) = 31104 * q + 8261 := by
  rw [step4_m4096_1087 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 5507) + 1 = 2 ^ 1 * (31104 * q + 8261) := by ring
  have h_odd : (31104 * q + 8261) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 5507) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 8261) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 8261) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 8261) (by positivity)]

theorem step6_m4096_1087 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1087)))))) = 5832 * q + 1549 := by
  rw [step5_m4096_1087 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 8261) + 1 = 2 ^ 4 * (5832 * q + 1549) := by ring
  have h_odd : (5832 * q + 1549) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 8261) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (5832 * q + 1549) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (5832 * q + 1549) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 1549) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1087 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1087 (q : ℕ) (hq : 4096 * q + 1087 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1087))))))) < 4096 * q + 1087 := by
  rw [step6_m4096_1087 q]
  have h_bound : step (5832 * q + 1549) ≤ 2187 * q + 581 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 1549) + 1 = 2 ^ 3 * (2187 * q + 581) := by ring
    have hne : (2187 * q + 581) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 1549) + 1) = 3 + ν₂ (2187 * q + 581) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 581) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 581) (2 ^ ν₂ (2187 * q + 581)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1231 (q : ℕ) : step (4096 * q + 1231) = 6144 * q + 1847 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1231) + 1 = 2 ^ 1 * (6144 * q + 1847) := by ring
  have h_odd : (6144 * q + 1847) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1231) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 1847) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 1847) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 1847) (by positivity)]

theorem step2_m4096_1231 (q : ℕ) : step (step (4096 * q + 1231)) = 9216 * q + 2771 := by
  rw [step_m4096_1231 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 1847) + 1 = 2 ^ 1 * (9216 * q + 2771) := by ring
  have h_odd : (9216 * q + 2771) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 1847) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 2771) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 2771) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 2771) (by positivity)]

theorem step3_m4096_1231 (q : ℕ) : step (step (step (4096 * q + 1231))) = 13824 * q + 4157 := by
  rw [step2_m4096_1231 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 2771) + 1 = 2 ^ 1 * (13824 * q + 4157) := by ring
  have h_odd : (13824 * q + 4157) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 2771) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 4157) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 4157) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 4157) (by positivity)]

theorem step4_m4096_1231 (q : ℕ) : step (step (step (step (4096 * q + 1231)))) = 5184 * q + 1559 := by
  rw [step3_m4096_1231 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 4157) + 1 = 2 ^ 3 * (5184 * q + 1559) := by ring
  have h_odd : (5184 * q + 1559) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 4157) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (5184 * q + 1559) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (5184 * q + 1559) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 1559) (by positivity)]

theorem step5_m4096_1231 (q : ℕ) : step (step (step (step (step (4096 * q + 1231))))) = 7776 * q + 2339 := by
  rw [step4_m4096_1231 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 1559) + 1 = 2 ^ 1 * (7776 * q + 2339) := by ring
  have h_odd : (7776 * q + 2339) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 1559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 2339) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 2339) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 2339) (by positivity)]

theorem step6_m4096_1231 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1231)))))) = 11664 * q + 3509 := by
  rw [step5_m4096_1231 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 2339) + 1 = 2 ^ 1 * (11664 * q + 3509) := by ring
  have h_odd : (11664 * q + 3509) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 2339) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 3509) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 3509) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 3509) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1231 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1231 (q : ℕ) (hq : 4096 * q + 1231 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1231))))))) < 4096 * q + 1231 := by
  rw [step6_m4096_1231 q]
  have h_bound : step (11664 * q + 3509) ≤ 2187 * q + 658 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 3509) + 1 = 2 ^ 4 * (2187 * q + 658) := by ring
    have hne : (2187 * q + 658) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 3509) + 1) = 4 + ν₂ (2187 * q + 658) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 658) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 658) (2 ^ ν₂ (2187 * q + 658)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1435 (q : ℕ) : step (4096 * q + 1435) = 6144 * q + 2153 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1435) + 1 = 2 ^ 1 * (6144 * q + 2153) := by ring
  have h_odd : (6144 * q + 2153) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1435) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 2153) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 2153) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2153) (by positivity)]

theorem step2_m4096_1435 (q : ℕ) : step (step (4096 * q + 1435)) = 4608 * q + 1615 := by
  rw [step_m4096_1435 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2153) + 1 = 2 ^ 2 * (4608 * q + 1615) := by ring
  have h_odd : (4608 * q + 1615) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2153) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 1615) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 1615) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 1615) (by positivity)]

theorem step3_m4096_1435 (q : ℕ) : step (step (step (4096 * q + 1435))) = 6912 * q + 2423 := by
  rw [step2_m4096_1435 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 1615) + 1 = 2 ^ 1 * (6912 * q + 2423) := by ring
  have h_odd : (6912 * q + 2423) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 1615) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 2423) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 2423) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 2423) (by positivity)]

theorem step4_m4096_1435 (q : ℕ) : step (step (step (step (4096 * q + 1435)))) = 10368 * q + 3635 := by
  rw [step3_m4096_1435 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 2423) + 1 = 2 ^ 1 * (10368 * q + 3635) := by ring
  have h_odd : (10368 * q + 3635) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 2423) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 3635) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 3635) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 3635) (by positivity)]

theorem step5_m4096_1435 (q : ℕ) : step (step (step (step (step (4096 * q + 1435))))) = 15552 * q + 5453 := by
  rw [step4_m4096_1435 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 3635) + 1 = 2 ^ 1 * (15552 * q + 5453) := by ring
  have h_odd : (15552 * q + 5453) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 3635) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 5453) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 5453) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 5453) (by positivity)]

theorem step6_m4096_1435 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1435)))))) = 5832 * q + 2045 := by
  rw [step5_m4096_1435 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 5453) + 1 = 2 ^ 3 * (5832 * q + 2045) := by ring
  have h_odd : (5832 * q + 2045) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 5453) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (5832 * q + 2045) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (5832 * q + 2045) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 2045) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1435 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1435 (q : ℕ) (hq : 4096 * q + 1435 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1435))))))) < 4096 * q + 1435 := by
  rw [step6_m4096_1435 q]
  have h_bound : step (5832 * q + 2045) ≤ 2187 * q + 767 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 2045) + 1 = 2 ^ 3 * (2187 * q + 767) := by ring
    have hne : (2187 * q + 767) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 2045) + 1) = 3 + ν₂ (2187 * q + 767) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 767) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 767) (2 ^ ν₂ (2187 * q + 767)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1647 (q : ℕ) : step (4096 * q + 1647) = 6144 * q + 2471 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1647) + 1 = 2 ^ 1 * (6144 * q + 2471) := by ring
  have h_odd : (6144 * q + 2471) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1647) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 2471) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 2471) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2471) (by positivity)]

theorem step2_m4096_1647 (q : ℕ) : step (step (4096 * q + 1647)) = 9216 * q + 3707 := by
  rw [step_m4096_1647 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2471) + 1 = 2 ^ 1 * (9216 * q + 3707) := by ring
  have h_odd : (9216 * q + 3707) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2471) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 3707) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 3707) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 3707) (by positivity)]

theorem step3_m4096_1647 (q : ℕ) : step (step (step (4096 * q + 1647))) = 13824 * q + 5561 := by
  rw [step2_m4096_1647 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 3707) + 1 = 2 ^ 1 * (13824 * q + 5561) := by ring
  have h_odd : (13824 * q + 5561) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 3707) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 5561) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 5561) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 5561) (by positivity)]

theorem step4_m4096_1647 (q : ℕ) : step (step (step (step (4096 * q + 1647)))) = 10368 * q + 4171 := by
  rw [step3_m4096_1647 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 5561) + 1 = 2 ^ 2 * (10368 * q + 4171) := by ring
  have h_odd : (10368 * q + 4171) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 5561) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 4171) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 4171) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 4171) (by positivity)]

theorem step5_m4096_1647 (q : ℕ) : step (step (step (step (step (4096 * q + 1647))))) = 15552 * q + 6257 := by
  rw [step4_m4096_1647 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 4171) + 1 = 2 ^ 1 * (15552 * q + 6257) := by ring
  have h_odd : (15552 * q + 6257) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 4171) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 6257) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 6257) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 6257) (by positivity)]

theorem step6_m4096_1647 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1647)))))) = 11664 * q + 4693 := by
  rw [step5_m4096_1647 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 6257) + 1 = 2 ^ 2 * (11664 * q + 4693) := by ring
  have h_odd : (11664 * q + 4693) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 6257) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 4693) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 4693) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 4693) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1647 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1647 (q : ℕ) (hq : 4096 * q + 1647 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1647))))))) < 4096 * q + 1647 := by
  rw [step6_m4096_1647 q]
  have h_bound : step (11664 * q + 4693) ≤ 2187 * q + 880 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 4693) + 1 = 2 ^ 4 * (2187 * q + 880) := by ring
    have hne : (2187 * q + 880) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 4693) + 1) = 4 + ν₂ (2187 * q + 880) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 880) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 880) (2 ^ ν₂ (2187 * q + 880)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1703 (q : ℕ) : step (4096 * q + 1703) = 6144 * q + 2555 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1703) + 1 = 2 ^ 1 * (6144 * q + 2555) := by ring
  have h_odd : (6144 * q + 2555) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1703) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 2555) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 2555) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2555) (by positivity)]

theorem step2_m4096_1703 (q : ℕ) : step (step (4096 * q + 1703)) = 9216 * q + 3833 := by
  rw [step_m4096_1703 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2555) + 1 = 2 ^ 1 * (9216 * q + 3833) := by ring
  have h_odd : (9216 * q + 3833) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2555) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 3833) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 3833) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 3833) (by positivity)]

theorem step3_m4096_1703 (q : ℕ) : step (step (step (4096 * q + 1703))) = 6912 * q + 2875 := by
  rw [step2_m4096_1703 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 3833) + 1 = 2 ^ 2 * (6912 * q + 2875) := by ring
  have h_odd : (6912 * q + 2875) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 3833) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 2875) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 2875) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 2875) (by positivity)]

theorem step4_m4096_1703 (q : ℕ) : step (step (step (step (4096 * q + 1703)))) = 10368 * q + 4313 := by
  rw [step3_m4096_1703 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 2875) + 1 = 2 ^ 1 * (10368 * q + 4313) := by ring
  have h_odd : (10368 * q + 4313) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 2875) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 4313) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 4313) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 4313) (by positivity)]

theorem step5_m4096_1703 (q : ℕ) : step (step (step (step (step (4096 * q + 1703))))) = 7776 * q + 3235 := by
  rw [step4_m4096_1703 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 4313) + 1 = 2 ^ 2 * (7776 * q + 3235) := by ring
  have h_odd : (7776 * q + 3235) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 4313) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 3235) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 3235) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 3235) (by positivity)]

theorem step6_m4096_1703 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1703)))))) = 11664 * q + 4853 := by
  rw [step5_m4096_1703 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 3235) + 1 = 2 ^ 1 * (11664 * q + 4853) := by ring
  have h_odd : (11664 * q + 4853) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 3235) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 4853) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 4853) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 4853) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1703 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1703 (q : ℕ) (hq : 4096 * q + 1703 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1703))))))) < 4096 * q + 1703 := by
  rw [step6_m4096_1703 q]
  have h_bound : step (11664 * q + 4853) ≤ 2187 * q + 910 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 4853) + 1 = 2 ^ 4 * (2187 * q + 910) := by ring
    have hne : (2187 * q + 910) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 4853) + 1) = 4 + ν₂ (2187 * q + 910) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 910) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 910) (2 ^ ν₂ (2187 * q + 910)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1787 (q : ℕ) : step (4096 * q + 1787) = 6144 * q + 2681 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1787) + 1 = 2 ^ 1 * (6144 * q + 2681) := by ring
  have h_odd : (6144 * q + 2681) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1787) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 2681) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 2681) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2681) (by positivity)]

theorem step2_m4096_1787 (q : ℕ) : step (step (4096 * q + 1787)) = 4608 * q + 2011 := by
  rw [step_m4096_1787 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2681) + 1 = 2 ^ 2 * (4608 * q + 2011) := by ring
  have h_odd : (4608 * q + 2011) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2681) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 2011) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 2011) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 2011) (by positivity)]

theorem step3_m4096_1787 (q : ℕ) : step (step (step (4096 * q + 1787))) = 6912 * q + 3017 := by
  rw [step2_m4096_1787 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 2011) + 1 = 2 ^ 1 * (6912 * q + 3017) := by ring
  have h_odd : (6912 * q + 3017) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 2011) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 3017) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 3017) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 3017) (by positivity)]

theorem step4_m4096_1787 (q : ℕ) : step (step (step (step (4096 * q + 1787)))) = 5184 * q + 2263 := by
  rw [step3_m4096_1787 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 3017) + 1 = 2 ^ 2 * (5184 * q + 2263) := by ring
  have h_odd : (5184 * q + 2263) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 3017) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 2263) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 2263) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 2263) (by positivity)]

theorem step5_m4096_1787 (q : ℕ) : step (step (step (step (step (4096 * q + 1787))))) = 7776 * q + 3395 := by
  rw [step4_m4096_1787 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 2263) + 1 = 2 ^ 1 * (7776 * q + 3395) := by ring
  have h_odd : (7776 * q + 3395) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 2263) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 3395) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 3395) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 3395) (by positivity)]

theorem step6_m4096_1787 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1787)))))) = 11664 * q + 5093 := by
  rw [step5_m4096_1787 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 3395) + 1 = 2 ^ 1 * (11664 * q + 5093) := by ring
  have h_odd : (11664 * q + 5093) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 3395) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 5093) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 5093) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 5093) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1787 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1787 (q : ℕ) (hq : 4096 * q + 1787 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1787))))))) < 4096 * q + 1787 := by
  rw [step6_m4096_1787 q]
  have h_bound : step (11664 * q + 5093) ≤ 2187 * q + 955 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 5093) + 1 = 2 ^ 4 * (2187 * q + 955) := by ring
    have hne : (2187 * q + 955) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 5093) + 1) = 4 + ν₂ (2187 * q + 955) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 955) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 955) (2 ^ ν₂ (2187 * q + 955)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1823 (q : ℕ) : step (4096 * q + 1823) = 6144 * q + 2735 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1823) + 1 = 2 ^ 1 * (6144 * q + 2735) := by ring
  have h_odd : (6144 * q + 2735) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1823) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 2735) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 2735) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2735) (by positivity)]

theorem step2_m4096_1823 (q : ℕ) : step (step (4096 * q + 1823)) = 9216 * q + 4103 := by
  rw [step_m4096_1823 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2735) + 1 = 2 ^ 1 * (9216 * q + 4103) := by ring
  have h_odd : (9216 * q + 4103) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2735) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 4103) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 4103) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4103) (by positivity)]

theorem step3_m4096_1823 (q : ℕ) : step (step (step (4096 * q + 1823))) = 13824 * q + 6155 := by
  rw [step2_m4096_1823 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4103) + 1 = 2 ^ 1 * (13824 * q + 6155) := by ring
  have h_odd : (13824 * q + 6155) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4103) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 6155) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 6155) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 6155) (by positivity)]

theorem step4_m4096_1823 (q : ℕ) : step (step (step (step (4096 * q + 1823)))) = 20736 * q + 9233 := by
  rw [step3_m4096_1823 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 6155) + 1 = 2 ^ 1 * (20736 * q + 9233) := by ring
  have h_odd : (20736 * q + 9233) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 6155) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 9233) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 9233) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 9233) (by positivity)]

theorem step5_m4096_1823 (q : ℕ) : step (step (step (step (step (4096 * q + 1823))))) = 15552 * q + 6925 := by
  rw [step4_m4096_1823 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 9233) + 1 = 2 ^ 2 * (15552 * q + 6925) := by ring
  have h_odd : (15552 * q + 6925) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 9233) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 6925) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 6925) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 6925) (by positivity)]

theorem step6_m4096_1823 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1823)))))) = 5832 * q + 2597 := by
  rw [step5_m4096_1823 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 6925) + 1 = 2 ^ 3 * (5832 * q + 2597) := by ring
  have h_odd : (5832 * q + 2597) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 6925) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (5832 * q + 2597) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (5832 * q + 2597) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 2597) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1823 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1823 (q : ℕ) (hq : 4096 * q + 1823 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1823))))))) < 4096 * q + 1823 := by
  rw [step6_m4096_1823 q]
  have h_bound : step (5832 * q + 2597) ≤ 2187 * q + 974 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 2597) + 1 = 2 ^ 3 * (2187 * q + 974) := by ring
    have hne : (2187 * q + 974) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 2597) + 1) = 3 + ν₂ (2187 * q + 974) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 974) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 974) (2 ^ ν₂ (2187 * q + 974)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1855 (q : ℕ) : step (4096 * q + 1855) = 6144 * q + 2783 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1855) + 1 = 2 ^ 1 * (6144 * q + 2783) := by ring
  have h_odd : (6144 * q + 2783) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1855) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 2783) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 2783) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2783) (by positivity)]

theorem step2_m4096_1855 (q : ℕ) : step (step (4096 * q + 1855)) = 9216 * q + 4175 := by
  rw [step_m4096_1855 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2783) + 1 = 2 ^ 1 * (9216 * q + 4175) := by ring
  have h_odd : (9216 * q + 4175) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2783) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 4175) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 4175) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4175) (by positivity)]

theorem step3_m4096_1855 (q : ℕ) : step (step (step (4096 * q + 1855))) = 13824 * q + 6263 := by
  rw [step2_m4096_1855 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4175) + 1 = 2 ^ 1 * (13824 * q + 6263) := by ring
  have h_odd : (13824 * q + 6263) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4175) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 6263) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 6263) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 6263) (by positivity)]

theorem step4_m4096_1855 (q : ℕ) : step (step (step (step (4096 * q + 1855)))) = 20736 * q + 9395 := by
  rw [step3_m4096_1855 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 6263) + 1 = 2 ^ 1 * (20736 * q + 9395) := by ring
  have h_odd : (20736 * q + 9395) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 6263) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 9395) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 9395) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 9395) (by positivity)]

theorem step5_m4096_1855 (q : ℕ) : step (step (step (step (step (4096 * q + 1855))))) = 31104 * q + 14093 := by
  rw [step4_m4096_1855 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 9395) + 1 = 2 ^ 1 * (31104 * q + 14093) := by ring
  have h_odd : (31104 * q + 14093) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 9395) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 14093) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 14093) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 14093) (by positivity)]

theorem step6_m4096_1855 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1855)))))) = 11664 * q + 5285 := by
  rw [step5_m4096_1855 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 14093) + 1 = 2 ^ 3 * (11664 * q + 5285) := by ring
  have h_odd : (11664 * q + 5285) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 14093) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 5285) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 5285) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 5285) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1855 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1855 (q : ℕ) (hq : 4096 * q + 1855 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1855))))))) < 4096 * q + 1855 := by
  rw [step6_m4096_1855 q]
  have h_bound : step (11664 * q + 5285) ≤ 2187 * q + 991 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 5285) + 1 = 2 ^ 4 * (2187 * q + 991) := by ring
    have hne : (2187 * q + 991) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 5285) + 1) = 4 + ν₂ (2187 * q + 991) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 991) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 991) (2 ^ ν₂ (2187 * q + 991)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_1929 (q : ℕ) : step (4096 * q + 1929) = 3072 * q + 1447 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 1929) + 1 = 2 ^ 2 * (3072 * q + 1447) := by ring
  have h_odd : (3072 * q + 1447) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 1929) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 1447) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 1447) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 1447) (by positivity)]

theorem step2_m4096_1929 (q : ℕ) : step (step (4096 * q + 1929)) = 4608 * q + 2171 := by
  rw [step_m4096_1929 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 1447) + 1 = 2 ^ 1 * (4608 * q + 2171) := by ring
  have h_odd : (4608 * q + 2171) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 1447) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 2171) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 2171) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 2171) (by positivity)]

theorem step3_m4096_1929 (q : ℕ) : step (step (step (4096 * q + 1929))) = 6912 * q + 3257 := by
  rw [step2_m4096_1929 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 2171) + 1 = 2 ^ 1 * (6912 * q + 3257) := by ring
  have h_odd : (6912 * q + 3257) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 2171) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 3257) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 3257) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 3257) (by positivity)]

theorem step4_m4096_1929 (q : ℕ) : step (step (step (step (4096 * q + 1929)))) = 5184 * q + 2443 := by
  rw [step3_m4096_1929 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 3257) + 1 = 2 ^ 2 * (5184 * q + 2443) := by ring
  have h_odd : (5184 * q + 2443) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 3257) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 2443) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 2443) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 2443) (by positivity)]

theorem step5_m4096_1929 (q : ℕ) : step (step (step (step (step (4096 * q + 1929))))) = 7776 * q + 3665 := by
  rw [step4_m4096_1929 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 2443) + 1 = 2 ^ 1 * (7776 * q + 3665) := by ring
  have h_odd : (7776 * q + 3665) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 2443) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 3665) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 3665) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 3665) (by positivity)]

theorem step6_m4096_1929 (q : ℕ) : step (step (step (step (step (step (4096 * q + 1929)))))) = 5832 * q + 2749 := by
  rw [step5_m4096_1929 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 3665) + 1 = 2 ^ 2 * (5832 * q + 2749) := by ring
  have h_odd : (5832 * q + 2749) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 3665) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 2749) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 2749) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 2749) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1929 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_1929 (q : ℕ) (hq : 4096 * q + 1929 > 1) :
    step (step (step (step (step (step (step (4096 * q + 1929))))))) < 4096 * q + 1929 := by
  rw [step6_m4096_1929 q]
  have h_bound : step (5832 * q + 2749) ≤ 2187 * q + 1031 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 2749) + 1 = 2 ^ 3 * (2187 * q + 1031) := by ring
    have hne : (2187 * q + 1031) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 2749) + 1) = 3 + ν₂ (2187 * q + 1031) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1031) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1031) (2 ^ ν₂ (2187 * q + 1031)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2031 (q : ℕ) : step (4096 * q + 2031) = 6144 * q + 3047 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2031) + 1 = 2 ^ 1 * (6144 * q + 3047) := by ring
  have h_odd : (6144 * q + 3047) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2031) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 3047) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 3047) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3047) (by positivity)]

theorem step2_m4096_2031 (q : ℕ) : step (step (4096 * q + 2031)) = 9216 * q + 4571 := by
  rw [step_m4096_2031 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3047) + 1 = 2 ^ 1 * (9216 * q + 4571) := by ring
  have h_odd : (9216 * q + 4571) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3047) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 4571) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 4571) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4571) (by positivity)]

theorem step3_m4096_2031 (q : ℕ) : step (step (step (4096 * q + 2031))) = 13824 * q + 6857 := by
  rw [step2_m4096_2031 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4571) + 1 = 2 ^ 1 * (13824 * q + 6857) := by ring
  have h_odd : (13824 * q + 6857) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4571) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 6857) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 6857) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 6857) (by positivity)]

theorem step4_m4096_2031 (q : ℕ) : step (step (step (step (4096 * q + 2031)))) = 10368 * q + 5143 := by
  rw [step3_m4096_2031 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 6857) + 1 = 2 ^ 2 * (10368 * q + 5143) := by ring
  have h_odd : (10368 * q + 5143) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 6857) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 5143) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 5143) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 5143) (by positivity)]

theorem step5_m4096_2031 (q : ℕ) : step (step (step (step (step (4096 * q + 2031))))) = 15552 * q + 7715 := by
  rw [step4_m4096_2031 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 5143) + 1 = 2 ^ 1 * (15552 * q + 7715) := by ring
  have h_odd : (15552 * q + 7715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 5143) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 7715) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 7715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 7715) (by positivity)]

theorem step6_m4096_2031 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2031)))))) = 23328 * q + 11573 := by
  rw [step5_m4096_2031 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 7715) + 1 = 2 ^ 1 * (23328 * q + 11573) := by ring
  have h_odd : (23328 * q + 11573) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 7715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 11573) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 11573) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 11573) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2031 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2031 (q : ℕ) (hq : 4096 * q + 2031 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2031))))))) < 4096 * q + 2031 := by
  rw [step6_m4096_2031 q]
  have h_bound : step (23328 * q + 11573) ≤ 2187 * q + 1085 := by
    unfold step
    have h3n1 : 3 * (23328 * q + 11573) + 1 = 2 ^ 5 * (2187 * q + 1085) := by ring
    have hne : (2187 * q + 1085) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (23328 * q + 11573) + 1) = 5 + ν₂ (2187 * q + 1085) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (2187 * q + 1085) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1085) (2 ^ ν₂ (2187 * q + 1085)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2049 (q : ℕ) : step (4096 * q + 2049) = 3072 * q + 1537 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2049) + 1 = 2 ^ 2 * (3072 * q + 1537) := by ring
  have h_odd : (3072 * q + 1537) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2049) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 1537) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 1537) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 1537) (by positivity)]

theorem step2_m4096_2049 (q : ℕ) : step (step (4096 * q + 2049)) = 2304 * q + 1153 := by
  rw [step_m4096_2049 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 1537) + 1 = 2 ^ 2 * (2304 * q + 1153) := by ring
  have h_odd : (2304 * q + 1153) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 1537) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (2304 * q + 1153) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (2304 * q + 1153) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 1153) (by positivity)]

theorem step3_m4096_2049 (q : ℕ) : step (step (step (4096 * q + 2049))) = 1728 * q + 865 := by
  rw [step2_m4096_2049 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 1153) + 1 = 2 ^ 2 * (1728 * q + 865) := by ring
  have h_odd : (1728 * q + 865) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 1153) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1728 * q + 865) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1728 * q + 865) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1728 * q + 865) (by positivity)]

theorem step4_m4096_2049 (q : ℕ) : step (step (step (step (4096 * q + 2049)))) = 1296 * q + 649 := by
  rw [step3_m4096_2049 q]
  unfold step
  have h3n1 : 3 * (1728 * q + 865) + 1 = 2 ^ 2 * (1296 * q + 649) := by ring
  have h_odd : (1296 * q + 649) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1728 * q + 865) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1296 * q + 649) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1296 * q + 649) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1296 * q + 649) (by positivity)]

theorem step5_m4096_2049 (q : ℕ) : step (step (step (step (step (4096 * q + 2049))))) = 972 * q + 487 := by
  rw [step4_m4096_2049 q]
  unfold step
  have h3n1 : 3 * (1296 * q + 649) + 1 = 2 ^ 2 * (972 * q + 487) := by ring
  have h_odd : (972 * q + 487) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (1296 * q + 649) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (972 * q + 487) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (972 * q + 487) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (972 * q + 487) (by positivity)]

theorem step6_m4096_2049 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2049)))))) = 1458 * q + 731 := by
  rw [step5_m4096_2049 q]
  unfold step
  have h3n1 : 3 * (972 * q + 487) + 1 = 2 ^ 1 * (1458 * q + 731) := by ring
  have h_odd : (1458 * q + 731) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (972 * q + 487) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (1458 * q + 731) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (1458 * q + 731) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1458 * q + 731) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2049 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2049 (q : ℕ) (hq : 4096 * q + 2049 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2049))))))) < 4096 * q + 2049 := by
  rw [step6_m4096_2049 q]
  have h_bound : step (1458 * q + 731) ≤ 2187 * q + 1097 := by
    unfold step
    have h3n1 : 3 * (1458 * q + 731) + 1 = 2 ^ 1 * (2187 * q + 1097) := by ring
    have hne : (2187 * q + 1097) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1458 * q + 731) + 1) = 1 + ν₂ (2187 * q + 1097) := by
      rw [h3n1, ν₂_mul (2 ^ 1) (2187 * q + 1097) (by positivity) hne, ν₂_pow_two' 1]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1097) (2 ^ ν₂ (2187 * q + 1097)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2203 (q : ℕ) : step (4096 * q + 2203) = 6144 * q + 3305 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2203) + 1 = 2 ^ 1 * (6144 * q + 3305) := by ring
  have h_odd : (6144 * q + 3305) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2203) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 3305) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 3305) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3305) (by positivity)]

theorem step2_m4096_2203 (q : ℕ) : step (step (4096 * q + 2203)) = 4608 * q + 2479 := by
  rw [step_m4096_2203 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3305) + 1 = 2 ^ 2 * (4608 * q + 2479) := by ring
  have h_odd : (4608 * q + 2479) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3305) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 2479) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 2479) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 2479) (by positivity)]

theorem step3_m4096_2203 (q : ℕ) : step (step (step (4096 * q + 2203))) = 6912 * q + 3719 := by
  rw [step2_m4096_2203 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 2479) + 1 = 2 ^ 1 * (6912 * q + 3719) := by ring
  have h_odd : (6912 * q + 3719) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 2479) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 3719) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 3719) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 3719) (by positivity)]

theorem step4_m4096_2203 (q : ℕ) : step (step (step (step (4096 * q + 2203)))) = 10368 * q + 5579 := by
  rw [step3_m4096_2203 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 3719) + 1 = 2 ^ 1 * (10368 * q + 5579) := by ring
  have h_odd : (10368 * q + 5579) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 3719) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 5579) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 5579) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 5579) (by positivity)]

theorem step5_m4096_2203 (q : ℕ) : step (step (step (step (step (4096 * q + 2203))))) = 15552 * q + 8369 := by
  rw [step4_m4096_2203 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 5579) + 1 = 2 ^ 1 * (15552 * q + 8369) := by ring
  have h_odd : (15552 * q + 8369) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 5579) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 8369) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 8369) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 8369) (by positivity)]

theorem step6_m4096_2203 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2203)))))) = 11664 * q + 6277 := by
  rw [step5_m4096_2203 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 8369) + 1 = 2 ^ 2 * (11664 * q + 6277) := by ring
  have h_odd : (11664 * q + 6277) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 8369) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 6277) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 6277) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 6277) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2203 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2203 (q : ℕ) (hq : 4096 * q + 2203 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2203))))))) < 4096 * q + 2203 := by
  rw [step6_m4096_2203 q]
  have h_bound : step (11664 * q + 6277) ≤ 2187 * q + 1177 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 6277) + 1 = 2 ^ 4 * (2187 * q + 1177) := by ring
    have hne : (2187 * q + 1177) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 6277) + 1) = 4 + ν₂ (2187 * q + 1177) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 1177) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1177) (2 ^ ν₂ (2187 * q + 1177)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2239 (q : ℕ) : step (4096 * q + 2239) = 6144 * q + 3359 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2239) + 1 = 2 ^ 1 * (6144 * q + 3359) := by ring
  have h_odd : (6144 * q + 3359) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2239) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 3359) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 3359) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3359) (by positivity)]

theorem step2_m4096_2239 (q : ℕ) : step (step (4096 * q + 2239)) = 9216 * q + 5039 := by
  rw [step_m4096_2239 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3359) + 1 = 2 ^ 1 * (9216 * q + 5039) := by ring
  have h_odd : (9216 * q + 5039) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3359) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 5039) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 5039) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5039) (by positivity)]

theorem step3_m4096_2239 (q : ℕ) : step (step (step (4096 * q + 2239))) = 13824 * q + 7559 := by
  rw [step2_m4096_2239 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5039) + 1 = 2 ^ 1 * (13824 * q + 7559) := by ring
  have h_odd : (13824 * q + 7559) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5039) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 7559) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 7559) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 7559) (by positivity)]

theorem step4_m4096_2239 (q : ℕ) : step (step (step (step (4096 * q + 2239)))) = 20736 * q + 11339 := by
  rw [step3_m4096_2239 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 7559) + 1 = 2 ^ 1 * (20736 * q + 11339) := by ring
  have h_odd : (20736 * q + 11339) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 7559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 11339) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 11339) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 11339) (by positivity)]

theorem step5_m4096_2239 (q : ℕ) : step (step (step (step (step (4096 * q + 2239))))) = 31104 * q + 17009 := by
  rw [step4_m4096_2239 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 11339) + 1 = 2 ^ 1 * (31104 * q + 17009) := by ring
  have h_odd : (31104 * q + 17009) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 11339) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 17009) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 17009) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 17009) (by positivity)]

theorem step6_m4096_2239 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2239)))))) = 23328 * q + 12757 := by
  rw [step5_m4096_2239 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 17009) + 1 = 2 ^ 2 * (23328 * q + 12757) := by ring
  have h_odd : (23328 * q + 12757) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 17009) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 12757) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 12757) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 12757) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2239 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2239 (q : ℕ) (hq : 4096 * q + 2239 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2239))))))) < 4096 * q + 2239 := by
  rw [step6_m4096_2239 q]
  have h_bound : step (23328 * q + 12757) ≤ 2187 * q + 1196 := by
    unfold step
    have h3n1 : 3 * (23328 * q + 12757) + 1 = 2 ^ 5 * (2187 * q + 1196) := by ring
    have hne : (2187 * q + 1196) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (23328 * q + 12757) + 1) = 5 + ν₂ (2187 * q + 1196) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (2187 * q + 1196) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1196) (2 ^ ν₂ (2187 * q + 1196)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2345 (q : ℕ) : step (4096 * q + 2345) = 3072 * q + 1759 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2345) + 1 = 2 ^ 2 * (3072 * q + 1759) := by ring
  have h_odd : (3072 * q + 1759) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2345) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 1759) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 1759) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 1759) (by positivity)]

theorem step2_m4096_2345 (q : ℕ) : step (step (4096 * q + 2345)) = 4608 * q + 2639 := by
  rw [step_m4096_2345 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 1759) + 1 = 2 ^ 1 * (4608 * q + 2639) := by ring
  have h_odd : (4608 * q + 2639) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 1759) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 2639) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 2639) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 2639) (by positivity)]

theorem step3_m4096_2345 (q : ℕ) : step (step (step (4096 * q + 2345))) = 6912 * q + 3959 := by
  rw [step2_m4096_2345 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 2639) + 1 = 2 ^ 1 * (6912 * q + 3959) := by ring
  have h_odd : (6912 * q + 3959) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 2639) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 3959) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 3959) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 3959) (by positivity)]

theorem step4_m4096_2345 (q : ℕ) : step (step (step (step (4096 * q + 2345)))) = 10368 * q + 5939 := by
  rw [step3_m4096_2345 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 3959) + 1 = 2 ^ 1 * (10368 * q + 5939) := by ring
  have h_odd : (10368 * q + 5939) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 3959) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 5939) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 5939) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 5939) (by positivity)]

theorem step5_m4096_2345 (q : ℕ) : step (step (step (step (step (4096 * q + 2345))))) = 15552 * q + 8909 := by
  rw [step4_m4096_2345 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 5939) + 1 = 2 ^ 1 * (15552 * q + 8909) := by ring
  have h_odd : (15552 * q + 8909) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 5939) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 8909) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 8909) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 8909) (by positivity)]

theorem step6_m4096_2345 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2345)))))) = 5832 * q + 3341 := by
  rw [step5_m4096_2345 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 8909) + 1 = 2 ^ 3 * (5832 * q + 3341) := by ring
  have h_odd : (5832 * q + 3341) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 8909) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (5832 * q + 3341) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (5832 * q + 3341) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 3341) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2345 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2345 (q : ℕ) (hq : 4096 * q + 2345 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2345))))))) < 4096 * q + 2345 := by
  rw [step6_m4096_2345 q]
  have h_bound : step (5832 * q + 3341) ≤ 2187 * q + 1253 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 3341) + 1 = 2 ^ 3 * (2187 * q + 1253) := by ring
    have hne : (2187 * q + 1253) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 3341) + 1) = 3 + ν₂ (2187 * q + 1253) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1253) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1253) (2 ^ ν₂ (2187 * q + 1253)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2351 (q : ℕ) : step (4096 * q + 2351) = 6144 * q + 3527 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2351) + 1 = 2 ^ 1 * (6144 * q + 3527) := by ring
  have h_odd : (6144 * q + 3527) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2351) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 3527) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 3527) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3527) (by positivity)]

theorem step2_m4096_2351 (q : ℕ) : step (step (4096 * q + 2351)) = 9216 * q + 5291 := by
  rw [step_m4096_2351 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3527) + 1 = 2 ^ 1 * (9216 * q + 5291) := by ring
  have h_odd : (9216 * q + 5291) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3527) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 5291) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 5291) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5291) (by positivity)]

theorem step3_m4096_2351 (q : ℕ) : step (step (step (4096 * q + 2351))) = 13824 * q + 7937 := by
  rw [step2_m4096_2351 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5291) + 1 = 2 ^ 1 * (13824 * q + 7937) := by ring
  have h_odd : (13824 * q + 7937) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5291) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 7937) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 7937) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 7937) (by positivity)]

theorem step4_m4096_2351 (q : ℕ) : step (step (step (step (4096 * q + 2351)))) = 10368 * q + 5953 := by
  rw [step3_m4096_2351 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 7937) + 1 = 2 ^ 2 * (10368 * q + 5953) := by ring
  have h_odd : (10368 * q + 5953) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 7937) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 5953) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 5953) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 5953) (by positivity)]

theorem step5_m4096_2351 (q : ℕ) : step (step (step (step (step (4096 * q + 2351))))) = 7776 * q + 4465 := by
  rw [step4_m4096_2351 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 5953) + 1 = 2 ^ 2 * (7776 * q + 4465) := by ring
  have h_odd : (7776 * q + 4465) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 5953) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 4465) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 4465) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 4465) (by positivity)]

theorem step6_m4096_2351 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2351)))))) = 5832 * q + 3349 := by
  rw [step5_m4096_2351 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 4465) + 1 = 2 ^ 2 * (5832 * q + 3349) := by ring
  have h_odd : (5832 * q + 3349) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 4465) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 3349) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 3349) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 3349) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2351 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2351 (q : ℕ) (hq : 4096 * q + 2351 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2351))))))) < 4096 * q + 2351 := by
  rw [step6_m4096_2351 q]
  have h_bound : step (5832 * q + 3349) ≤ 2187 * q + 1256 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 3349) + 1 = 2 ^ 3 * (2187 * q + 1256) := by ring
    have hne : (2187 * q + 1256) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 3349) + 1) = 3 + ν₂ (2187 * q + 1256) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1256) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1256) (2 ^ ν₂ (2187 * q + 1256)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2587 (q : ℕ) : step (4096 * q + 2587) = 6144 * q + 3881 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2587) + 1 = 2 ^ 1 * (6144 * q + 3881) := by ring
  have h_odd : (6144 * q + 3881) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2587) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 3881) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 3881) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3881) (by positivity)]

theorem step2_m4096_2587 (q : ℕ) : step (step (4096 * q + 2587)) = 4608 * q + 2911 := by
  rw [step_m4096_2587 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3881) + 1 = 2 ^ 2 * (4608 * q + 2911) := by ring
  have h_odd : (4608 * q + 2911) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3881) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 2911) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 2911) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 2911) (by positivity)]

theorem step3_m4096_2587 (q : ℕ) : step (step (step (4096 * q + 2587))) = 6912 * q + 4367 := by
  rw [step2_m4096_2587 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 2911) + 1 = 2 ^ 1 * (6912 * q + 4367) := by ring
  have h_odd : (6912 * q + 4367) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 2911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 4367) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 4367) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 4367) (by positivity)]

theorem step4_m4096_2587 (q : ℕ) : step (step (step (step (4096 * q + 2587)))) = 10368 * q + 6551 := by
  rw [step3_m4096_2587 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 4367) + 1 = 2 ^ 1 * (10368 * q + 6551) := by ring
  have h_odd : (10368 * q + 6551) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 4367) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 6551) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 6551) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 6551) (by positivity)]

theorem step5_m4096_2587 (q : ℕ) : step (step (step (step (step (4096 * q + 2587))))) = 15552 * q + 9827 := by
  rw [step4_m4096_2587 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 6551) + 1 = 2 ^ 1 * (15552 * q + 9827) := by ring
  have h_odd : (15552 * q + 9827) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 6551) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 9827) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 9827) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9827) (by positivity)]

theorem step6_m4096_2587 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2587)))))) = 23328 * q + 14741 := by
  rw [step5_m4096_2587 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9827) + 1 = 2 ^ 1 * (23328 * q + 14741) := by ring
  have h_odd : (23328 * q + 14741) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9827) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 14741) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 14741) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 14741) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2587 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2587 (q : ℕ) (hq : 4096 * q + 2587 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2587))))))) < 4096 * q + 2587 := by
  rw [step6_m4096_2587 q]
  have h_bound : step (23328 * q + 14741) ≤ 2187 * q + 1382 := by
    unfold step
    have h3n1 : 3 * (23328 * q + 14741) + 1 = 2 ^ 5 * (2187 * q + 1382) := by ring
    have hne : (2187 * q + 1382) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (23328 * q + 14741) + 1) = 5 + ν₂ (2187 * q + 1382) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (2187 * q + 1382) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1382) (2 ^ ν₂ (2187 * q + 1382)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2591 (q : ℕ) : step (4096 * q + 2591) = 6144 * q + 3887 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2591) + 1 = 2 ^ 1 * (6144 * q + 3887) := by ring
  have h_odd : (6144 * q + 3887) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2591) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 3887) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 3887) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3887) (by positivity)]

theorem step2_m4096_2591 (q : ℕ) : step (step (4096 * q + 2591)) = 9216 * q + 5831 := by
  rw [step_m4096_2591 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3887) + 1 = 2 ^ 1 * (9216 * q + 5831) := by ring
  have h_odd : (9216 * q + 5831) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3887) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 5831) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 5831) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5831) (by positivity)]

theorem step3_m4096_2591 (q : ℕ) : step (step (step (4096 * q + 2591))) = 13824 * q + 8747 := by
  rw [step2_m4096_2591 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5831) + 1 = 2 ^ 1 * (13824 * q + 8747) := by ring
  have h_odd : (13824 * q + 8747) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5831) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 8747) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 8747) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8747) (by positivity)]

theorem step4_m4096_2591 (q : ℕ) : step (step (step (step (4096 * q + 2591)))) = 20736 * q + 13121 := by
  rw [step3_m4096_2591 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8747) + 1 = 2 ^ 1 * (20736 * q + 13121) := by ring
  have h_odd : (20736 * q + 13121) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8747) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 13121) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 13121) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 13121) (by positivity)]

theorem step5_m4096_2591 (q : ℕ) : step (step (step (step (step (4096 * q + 2591))))) = 15552 * q + 9841 := by
  rw [step4_m4096_2591 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 13121) + 1 = 2 ^ 2 * (15552 * q + 9841) := by ring
  have h_odd : (15552 * q + 9841) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 13121) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 9841) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 9841) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9841) (by positivity)]

theorem step6_m4096_2591 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2591)))))) = 11664 * q + 7381 := by
  rw [step5_m4096_2591 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9841) + 1 = 2 ^ 2 * (11664 * q + 7381) := by ring
  have h_odd : (11664 * q + 7381) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9841) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 7381) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 7381) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7381) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2591 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2591 (q : ℕ) (hq : 4096 * q + 2591 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2591))))))) < 4096 * q + 2591 := by
  rw [step6_m4096_2591 q]
  have h_bound : step (11664 * q + 7381) ≤ 2187 * q + 1384 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 7381) + 1 = 2 ^ 4 * (2187 * q + 1384) := by ring
    have hne : (2187 * q + 1384) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 7381) + 1) = 4 + ν₂ (2187 * q + 1384) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 1384) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1384) (2 ^ ν₂ (2187 * q + 1384)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2697 (q : ℕ) : step (4096 * q + 2697) = 3072 * q + 2023 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2697) + 1 = 2 ^ 2 * (3072 * q + 2023) := by ring
  have h_odd : (3072 * q + 2023) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2697) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 2023) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 2023) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 2023) (by positivity)]

theorem step2_m4096_2697 (q : ℕ) : step (step (4096 * q + 2697)) = 4608 * q + 3035 := by
  rw [step_m4096_2697 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 2023) + 1 = 2 ^ 1 * (4608 * q + 3035) := by ring
  have h_odd : (4608 * q + 3035) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 2023) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 3035) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 3035) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 3035) (by positivity)]

theorem step3_m4096_2697 (q : ℕ) : step (step (step (4096 * q + 2697))) = 6912 * q + 4553 := by
  rw [step2_m4096_2697 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 3035) + 1 = 2 ^ 1 * (6912 * q + 4553) := by ring
  have h_odd : (6912 * q + 4553) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 3035) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 4553) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 4553) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 4553) (by positivity)]

theorem step4_m4096_2697 (q : ℕ) : step (step (step (step (4096 * q + 2697)))) = 5184 * q + 3415 := by
  rw [step3_m4096_2697 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 4553) + 1 = 2 ^ 2 * (5184 * q + 3415) := by ring
  have h_odd : (5184 * q + 3415) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 4553) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 3415) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 3415) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 3415) (by positivity)]

theorem step5_m4096_2697 (q : ℕ) : step (step (step (step (step (4096 * q + 2697))))) = 7776 * q + 5123 := by
  rw [step4_m4096_2697 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 3415) + 1 = 2 ^ 1 * (7776 * q + 5123) := by ring
  have h_odd : (7776 * q + 5123) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 3415) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 5123) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 5123) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 5123) (by positivity)]

theorem step6_m4096_2697 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2697)))))) = 11664 * q + 7685 := by
  rw [step5_m4096_2697 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 5123) + 1 = 2 ^ 1 * (11664 * q + 7685) := by ring
  have h_odd : (11664 * q + 7685) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 5123) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 7685) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 7685) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7685) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2697 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2697 (q : ℕ) (hq : 4096 * q + 2697 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2697))))))) < 4096 * q + 2697 := by
  rw [step6_m4096_2697 q]
  have h_bound : step (11664 * q + 7685) ≤ 2187 * q + 1441 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 7685) + 1 = 2 ^ 4 * (2187 * q + 1441) := by ring
    have hne : (2187 * q + 1441) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 7685) + 1) = 4 + ν₂ (2187 * q + 1441) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 1441) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1441) (2 ^ ν₂ (2187 * q + 1441)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2907 (q : ℕ) : step (4096 * q + 2907) = 6144 * q + 4361 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2907) + 1 = 2 ^ 1 * (6144 * q + 4361) := by ring
  have h_odd : (6144 * q + 4361) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2907) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 4361) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 4361) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4361) (by positivity)]

theorem step2_m4096_2907 (q : ℕ) : step (step (4096 * q + 2907)) = 4608 * q + 3271 := by
  rw [step_m4096_2907 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4361) + 1 = 2 ^ 2 * (4608 * q + 3271) := by ring
  have h_odd : (4608 * q + 3271) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4361) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 3271) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 3271) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 3271) (by positivity)]

theorem step3_m4096_2907 (q : ℕ) : step (step (step (4096 * q + 2907))) = 6912 * q + 4907 := by
  rw [step2_m4096_2907 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 3271) + 1 = 2 ^ 1 * (6912 * q + 4907) := by ring
  have h_odd : (6912 * q + 4907) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 3271) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 4907) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 4907) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 4907) (by positivity)]

theorem step4_m4096_2907 (q : ℕ) : step (step (step (step (4096 * q + 2907)))) = 10368 * q + 7361 := by
  rw [step3_m4096_2907 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 4907) + 1 = 2 ^ 1 * (10368 * q + 7361) := by ring
  have h_odd : (10368 * q + 7361) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 4907) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 7361) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 7361) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7361) (by positivity)]

theorem step5_m4096_2907 (q : ℕ) : step (step (step (step (step (4096 * q + 2907))))) = 7776 * q + 5521 := by
  rw [step4_m4096_2907 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7361) + 1 = 2 ^ 2 * (7776 * q + 5521) := by ring
  have h_odd : (7776 * q + 5521) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7361) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 5521) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 5521) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 5521) (by positivity)]

theorem step6_m4096_2907 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2907)))))) = 5832 * q + 4141 := by
  rw [step5_m4096_2907 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 5521) + 1 = 2 ^ 2 * (5832 * q + 4141) := by ring
  have h_odd : (5832 * q + 4141) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 5521) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 4141) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 4141) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 4141) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2907 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2907 (q : ℕ) (hq : 4096 * q + 2907 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2907))))))) < 4096 * q + 2907 := by
  rw [step6_m4096_2907 q]
  have h_bound : step (5832 * q + 4141) ≤ 2187 * q + 1553 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 4141) + 1 = 2 ^ 3 * (2187 * q + 1553) := by ring
    have hne : (2187 * q + 1553) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 4141) + 1) = 3 + ν₂ (2187 * q + 1553) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1553) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1553) (2 ^ ν₂ (2187 * q + 1553)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_2975 (q : ℕ) : step (4096 * q + 2975) = 6144 * q + 4463 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 2975) + 1 = 2 ^ 1 * (6144 * q + 4463) := by ring
  have h_odd : (6144 * q + 4463) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 2975) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 4463) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 4463) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4463) (by positivity)]

theorem step2_m4096_2975 (q : ℕ) : step (step (4096 * q + 2975)) = 9216 * q + 6695 := by
  rw [step_m4096_2975 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4463) + 1 = 2 ^ 1 * (9216 * q + 6695) := by ring
  have h_odd : (9216 * q + 6695) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4463) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 6695) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 6695) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6695) (by positivity)]

theorem step3_m4096_2975 (q : ℕ) : step (step (step (4096 * q + 2975))) = 13824 * q + 10043 := by
  rw [step2_m4096_2975 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6695) + 1 = 2 ^ 1 * (13824 * q + 10043) := by ring
  have h_odd : (13824 * q + 10043) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6695) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 10043) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 10043) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10043) (by positivity)]

theorem step4_m4096_2975 (q : ℕ) : step (step (step (step (4096 * q + 2975)))) = 20736 * q + 15065 := by
  rw [step3_m4096_2975 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10043) + 1 = 2 ^ 1 * (20736 * q + 15065) := by ring
  have h_odd : (20736 * q + 15065) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10043) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 15065) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 15065) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 15065) (by positivity)]

theorem step5_m4096_2975 (q : ℕ) : step (step (step (step (step (4096 * q + 2975))))) = 15552 * q + 11299 := by
  rw [step4_m4096_2975 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 15065) + 1 = 2 ^ 2 * (15552 * q + 11299) := by ring
  have h_odd : (15552 * q + 11299) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 15065) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 11299) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 11299) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11299) (by positivity)]

theorem step6_m4096_2975 (q : ℕ) : step (step (step (step (step (step (4096 * q + 2975)))))) = 23328 * q + 16949 := by
  rw [step5_m4096_2975 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11299) + 1 = 2 ^ 1 * (23328 * q + 16949) := by ring
  have h_odd : (23328 * q + 16949) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11299) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 16949) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 16949) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 16949) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2975 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_2975 (q : ℕ) (hq : 4096 * q + 2975 > 1) :
    step (step (step (step (step (step (step (4096 * q + 2975))))))) < 4096 * q + 2975 := by
  rw [step6_m4096_2975 q]
  have h_bound : step (23328 * q + 16949) ≤ 2187 * q + 1589 := by
    unfold step
    have h3n1 : 3 * (23328 * q + 16949) + 1 = 2 ^ 5 * (2187 * q + 1589) := by ring
    have hne : (2187 * q + 1589) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (23328 * q + 16949) + 1) = 5 + ν₂ (2187 * q + 1589) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (2187 * q + 1589) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1589) (2 ^ ν₂ (2187 * q + 1589)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3041 (q : ℕ) : step (4096 * q + 3041) = 3072 * q + 2281 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3041) + 1 = 2 ^ 2 * (3072 * q + 2281) := by ring
  have h_odd : (3072 * q + 2281) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3041) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 2281) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 2281) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 2281) (by positivity)]

theorem step2_m4096_3041 (q : ℕ) : step (step (4096 * q + 3041)) = 2304 * q + 1711 := by
  rw [step_m4096_3041 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 2281) + 1 = 2 ^ 2 * (2304 * q + 1711) := by ring
  have h_odd : (2304 * q + 1711) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 2281) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (2304 * q + 1711) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (2304 * q + 1711) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 1711) (by positivity)]

theorem step3_m4096_3041 (q : ℕ) : step (step (step (4096 * q + 3041))) = 3456 * q + 2567 := by
  rw [step2_m4096_3041 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 1711) + 1 = 2 ^ 1 * (3456 * q + 2567) := by ring
  have h_odd : (3456 * q + 2567) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 1711) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 2567) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 2567) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 2567) (by positivity)]

theorem step4_m4096_3041 (q : ℕ) : step (step (step (step (4096 * q + 3041)))) = 5184 * q + 3851 := by
  rw [step3_m4096_3041 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 2567) + 1 = 2 ^ 1 * (5184 * q + 3851) := by ring
  have h_odd : (5184 * q + 3851) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 2567) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (5184 * q + 3851) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (5184 * q + 3851) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 3851) (by positivity)]

theorem step5_m4096_3041 (q : ℕ) : step (step (step (step (step (4096 * q + 3041))))) = 7776 * q + 5777 := by
  rw [step4_m4096_3041 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 3851) + 1 = 2 ^ 1 * (7776 * q + 5777) := by ring
  have h_odd : (7776 * q + 5777) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 3851) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 5777) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 5777) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 5777) (by positivity)]

theorem step6_m4096_3041 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3041)))))) = 5832 * q + 4333 := by
  rw [step5_m4096_3041 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 5777) + 1 = 2 ^ 2 * (5832 * q + 4333) := by ring
  have h_odd : (5832 * q + 4333) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 5777) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 4333) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 4333) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 4333) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3041 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3041 (q : ℕ) (hq : 4096 * q + 3041 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3041))))))) < 4096 * q + 3041 := by
  rw [step6_m4096_3041 q]
  have h_bound : step (5832 * q + 4333) ≤ 2187 * q + 1625 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 4333) + 1 = 2 ^ 3 * (2187 * q + 1625) := by ring
    have hne : (2187 * q + 1625) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 4333) + 1) = 3 + ν₂ (2187 * q + 1625) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1625) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1625) (2 ^ ν₂ (2187 * q + 1625)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3113 (q : ℕ) : step (4096 * q + 3113) = 3072 * q + 2335 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3113) + 1 = 2 ^ 2 * (3072 * q + 2335) := by ring
  have h_odd : (3072 * q + 2335) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3113) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 2335) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 2335) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 2335) (by positivity)]

theorem step2_m4096_3113 (q : ℕ) : step (step (4096 * q + 3113)) = 4608 * q + 3503 := by
  rw [step_m4096_3113 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 2335) + 1 = 2 ^ 1 * (4608 * q + 3503) := by ring
  have h_odd : (4608 * q + 3503) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 2335) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 3503) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 3503) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 3503) (by positivity)]

theorem step3_m4096_3113 (q : ℕ) : step (step (step (4096 * q + 3113))) = 6912 * q + 5255 := by
  rw [step2_m4096_3113 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 3503) + 1 = 2 ^ 1 * (6912 * q + 5255) := by ring
  have h_odd : (6912 * q + 5255) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 3503) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 5255) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 5255) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 5255) (by positivity)]

theorem step4_m4096_3113 (q : ℕ) : step (step (step (step (4096 * q + 3113)))) = 10368 * q + 7883 := by
  rw [step3_m4096_3113 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 5255) + 1 = 2 ^ 1 * (10368 * q + 7883) := by ring
  have h_odd : (10368 * q + 7883) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 5255) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 7883) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 7883) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7883) (by positivity)]

theorem step5_m4096_3113 (q : ℕ) : step (step (step (step (step (4096 * q + 3113))))) = 15552 * q + 11825 := by
  rw [step4_m4096_3113 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7883) + 1 = 2 ^ 1 * (15552 * q + 11825) := by ring
  have h_odd : (15552 * q + 11825) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7883) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 11825) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 11825) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11825) (by positivity)]

theorem step6_m4096_3113 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3113)))))) = 11664 * q + 8869 := by
  rw [step5_m4096_3113 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11825) + 1 = 2 ^ 2 * (11664 * q + 8869) := by ring
  have h_odd : (11664 * q + 8869) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11825) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 8869) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 8869) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 8869) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3113 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3113 (q : ℕ) (hq : 4096 * q + 3113 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3113))))))) < 4096 * q + 3113 := by
  rw [step6_m4096_3113 q]
  have h_bound : step (11664 * q + 8869) ≤ 2187 * q + 1663 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 8869) + 1 = 2 ^ 4 * (2187 * q + 1663) := by ring
    have hne : (2187 * q + 1663) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 8869) + 1) = 4 + ν₂ (2187 * q + 1663) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 1663) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1663) (2 ^ ν₂ (2187 * q + 1663)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3119 (q : ℕ) : step (4096 * q + 3119) = 6144 * q + 4679 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3119) + 1 = 2 ^ 1 * (6144 * q + 4679) := by ring
  have h_odd : (6144 * q + 4679) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3119) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 4679) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 4679) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4679) (by positivity)]

theorem step2_m4096_3119 (q : ℕ) : step (step (4096 * q + 3119)) = 9216 * q + 7019 := by
  rw [step_m4096_3119 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4679) + 1 = 2 ^ 1 * (9216 * q + 7019) := by ring
  have h_odd : (9216 * q + 7019) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4679) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7019) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7019) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7019) (by positivity)]

theorem step3_m4096_3119 (q : ℕ) : step (step (step (4096 * q + 3119))) = 13824 * q + 10529 := by
  rw [step2_m4096_3119 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7019) + 1 = 2 ^ 1 * (13824 * q + 10529) := by ring
  have h_odd : (13824 * q + 10529) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7019) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 10529) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 10529) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10529) (by positivity)]

theorem step4_m4096_3119 (q : ℕ) : step (step (step (step (4096 * q + 3119)))) = 10368 * q + 7897 := by
  rw [step3_m4096_3119 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10529) + 1 = 2 ^ 2 * (10368 * q + 7897) := by ring
  have h_odd : (10368 * q + 7897) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10529) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 7897) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 7897) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7897) (by positivity)]

theorem step5_m4096_3119 (q : ℕ) : step (step (step (step (step (4096 * q + 3119))))) = 7776 * q + 5923 := by
  rw [step4_m4096_3119 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7897) + 1 = 2 ^ 2 * (7776 * q + 5923) := by ring
  have h_odd : (7776 * q + 5923) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7897) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 5923) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 5923) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 5923) (by positivity)]

theorem step6_m4096_3119 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3119)))))) = 11664 * q + 8885 := by
  rw [step5_m4096_3119 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 5923) + 1 = 2 ^ 1 * (11664 * q + 8885) := by ring
  have h_odd : (11664 * q + 8885) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 5923) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 8885) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 8885) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 8885) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3119 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3119 (q : ℕ) (hq : 4096 * q + 3119 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3119))))))) < 4096 * q + 3119 := by
  rw [step6_m4096_3119 q]
  have h_bound : step (11664 * q + 8885) ≤ 2187 * q + 1666 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 8885) + 1 = 2 ^ 4 * (2187 * q + 1666) := by ring
    have hne : (2187 * q + 1666) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 8885) + 1) = 4 + ν₂ (2187 * q + 1666) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 1666) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1666) (2 ^ ν₂ (2187 * q + 1666)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3143 (q : ℕ) : step (4096 * q + 3143) = 6144 * q + 4715 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3143) + 1 = 2 ^ 1 * (6144 * q + 4715) := by ring
  have h_odd : (6144 * q + 4715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3143) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 4715) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 4715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4715) (by positivity)]

theorem step2_m4096_3143 (q : ℕ) : step (step (4096 * q + 3143)) = 9216 * q + 7073 := by
  rw [step_m4096_3143 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4715) + 1 = 2 ^ 1 * (9216 * q + 7073) := by ring
  have h_odd : (9216 * q + 7073) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7073) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7073) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7073) (by positivity)]

theorem step3_m4096_3143 (q : ℕ) : step (step (step (4096 * q + 3143))) = 6912 * q + 5305 := by
  rw [step2_m4096_3143 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7073) + 1 = 2 ^ 2 * (6912 * q + 5305) := by ring
  have h_odd : (6912 * q + 5305) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7073) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 5305) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 5305) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 5305) (by positivity)]

theorem step4_m4096_3143 (q : ℕ) : step (step (step (step (4096 * q + 3143)))) = 5184 * q + 3979 := by
  rw [step3_m4096_3143 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 5305) + 1 = 2 ^ 2 * (5184 * q + 3979) := by ring
  have h_odd : (5184 * q + 3979) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 5305) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 3979) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 3979) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 3979) (by positivity)]

theorem step5_m4096_3143 (q : ℕ) : step (step (step (step (step (4096 * q + 3143))))) = 7776 * q + 5969 := by
  rw [step4_m4096_3143 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 3979) + 1 = 2 ^ 1 * (7776 * q + 5969) := by ring
  have h_odd : (7776 * q + 5969) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 3979) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 5969) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 5969) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 5969) (by positivity)]

theorem step6_m4096_3143 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3143)))))) = 5832 * q + 4477 := by
  rw [step5_m4096_3143 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 5969) + 1 = 2 ^ 2 * (5832 * q + 4477) := by ring
  have h_odd : (5832 * q + 4477) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 5969) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 4477) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 4477) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 4477) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3143 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3143 (q : ℕ) (hq : 4096 * q + 3143 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3143))))))) < 4096 * q + 3143 := by
  rw [step6_m4096_3143 q]
  have h_bound : step (5832 * q + 4477) ≤ 2187 * q + 1679 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 4477) + 1 = 2 ^ 3 * (2187 * q + 1679) := by ring
    have hne : (2187 * q + 1679) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 4477) + 1) = 3 + ν₂ (2187 * q + 1679) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1679) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1679) (2 ^ ν₂ (2187 * q + 1679)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3295 (q : ℕ) : step (4096 * q + 3295) = 6144 * q + 4943 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3295) + 1 = 2 ^ 1 * (6144 * q + 4943) := by ring
  have h_odd : (6144 * q + 4943) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 4943) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 4943) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4943) (by positivity)]

theorem step2_m4096_3295 (q : ℕ) : step (step (4096 * q + 3295)) = 9216 * q + 7415 := by
  rw [step_m4096_3295 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4943) + 1 = 2 ^ 1 * (9216 * q + 7415) := by ring
  have h_odd : (9216 * q + 7415) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4943) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7415) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7415) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7415) (by positivity)]

theorem step3_m4096_3295 (q : ℕ) : step (step (step (4096 * q + 3295))) = 13824 * q + 11123 := by
  rw [step2_m4096_3295 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7415) + 1 = 2 ^ 1 * (13824 * q + 11123) := by ring
  have h_odd : (13824 * q + 11123) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7415) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 11123) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 11123) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11123) (by positivity)]

theorem step4_m4096_3295 (q : ℕ) : step (step (step (step (4096 * q + 3295)))) = 20736 * q + 16685 := by
  rw [step3_m4096_3295 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11123) + 1 = 2 ^ 1 * (20736 * q + 16685) := by ring
  have h_odd : (20736 * q + 16685) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11123) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 16685) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 16685) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 16685) (by positivity)]

theorem step5_m4096_3295 (q : ℕ) : step (step (step (step (step (4096 * q + 3295))))) = 7776 * q + 6257 := by
  rw [step4_m4096_3295 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 16685) + 1 = 2 ^ 3 * (7776 * q + 6257) := by ring
  have h_odd : (7776 * q + 6257) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 16685) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (7776 * q + 6257) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (7776 * q + 6257) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 6257) (by positivity)]

theorem step6_m4096_3295 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3295)))))) = 5832 * q + 4693 := by
  rw [step5_m4096_3295 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 6257) + 1 = 2 ^ 2 * (5832 * q + 4693) := by ring
  have h_odd : (5832 * q + 4693) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 6257) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 4693) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 4693) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 4693) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3295 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3295 (q : ℕ) (hq : 4096 * q + 3295 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3295))))))) < 4096 * q + 3295 := by
  rw [step6_m4096_3295 q]
  have h_bound : step (5832 * q + 4693) ≤ 2187 * q + 1760 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 4693) + 1 = 2 ^ 3 * (2187 * q + 1760) := by ring
    have hne : (2187 * q + 1760) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 4693) + 1) = 3 + ν₂ (2187 * q + 1760) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1760) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1760) (2 ^ ν₂ (2187 * q + 1760)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3497 (q : ℕ) : step (4096 * q + 3497) = 3072 * q + 2623 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3497) + 1 = 2 ^ 2 * (3072 * q + 2623) := by ring
  have h_odd : (3072 * q + 2623) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3497) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 2623) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 2623) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 2623) (by positivity)]

theorem step2_m4096_3497 (q : ℕ) : step (step (4096 * q + 3497)) = 4608 * q + 3935 := by
  rw [step_m4096_3497 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 2623) + 1 = 2 ^ 1 * (4608 * q + 3935) := by ring
  have h_odd : (4608 * q + 3935) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 2623) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 3935) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 3935) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 3935) (by positivity)]

theorem step3_m4096_3497 (q : ℕ) : step (step (step (4096 * q + 3497))) = 6912 * q + 5903 := by
  rw [step2_m4096_3497 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 3935) + 1 = 2 ^ 1 * (6912 * q + 5903) := by ring
  have h_odd : (6912 * q + 5903) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 3935) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 5903) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 5903) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 5903) (by positivity)]

theorem step4_m4096_3497 (q : ℕ) : step (step (step (step (4096 * q + 3497)))) = 10368 * q + 8855 := by
  rw [step3_m4096_3497 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 5903) + 1 = 2 ^ 1 * (10368 * q + 8855) := by ring
  have h_odd : (10368 * q + 8855) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 5903) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 8855) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 8855) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 8855) (by positivity)]

theorem step5_m4096_3497 (q : ℕ) : step (step (step (step (step (4096 * q + 3497))))) = 15552 * q + 13283 := by
  rw [step4_m4096_3497 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 8855) + 1 = 2 ^ 1 * (15552 * q + 13283) := by ring
  have h_odd : (15552 * q + 13283) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 8855) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 13283) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 13283) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 13283) (by positivity)]

theorem step6_m4096_3497 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3497)))))) = 23328 * q + 19925 := by
  rw [step5_m4096_3497 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 13283) + 1 = 2 ^ 1 * (23328 * q + 19925) := by ring
  have h_odd : (23328 * q + 19925) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 13283) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 19925) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 19925) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 19925) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3497 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3497 (q : ℕ) (hq : 4096 * q + 3497 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3497))))))) < 4096 * q + 3497 := by
  rw [step6_m4096_3497 q]
  have h_bound : step (23328 * q + 19925) ≤ 2187 * q + 1868 := by
    unfold step
    have h3n1 : 3 * (23328 * q + 19925) + 1 = 2 ^ 5 * (2187 * q + 1868) := by ring
    have hne : (2187 * q + 1868) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (23328 * q + 19925) + 1) = 5 + ν₂ (2187 * q + 1868) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (2187 * q + 1868) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1868) (2 ^ ν₂ (2187 * q + 1868)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3559 (q : ℕ) : step (4096 * q + 3559) = 6144 * q + 5339 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3559) + 1 = 2 ^ 1 * (6144 * q + 5339) := by ring
  have h_odd : (6144 * q + 5339) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 5339) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 5339) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5339) (by positivity)]

theorem step2_m4096_3559 (q : ℕ) : step (step (4096 * q + 3559)) = 9216 * q + 8009 := by
  rw [step_m4096_3559 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5339) + 1 = 2 ^ 1 * (9216 * q + 8009) := by ring
  have h_odd : (9216 * q + 8009) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5339) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 8009) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 8009) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 8009) (by positivity)]

theorem step3_m4096_3559 (q : ℕ) : step (step (step (4096 * q + 3559))) = 6912 * q + 6007 := by
  rw [step2_m4096_3559 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 8009) + 1 = 2 ^ 2 * (6912 * q + 6007) := by ring
  have h_odd : (6912 * q + 6007) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 8009) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 6007) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 6007) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 6007) (by positivity)]

theorem step4_m4096_3559 (q : ℕ) : step (step (step (step (4096 * q + 3559)))) = 10368 * q + 9011 := by
  rw [step3_m4096_3559 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 6007) + 1 = 2 ^ 1 * (10368 * q + 9011) := by ring
  have h_odd : (10368 * q + 9011) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 6007) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 9011) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 9011) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 9011) (by positivity)]

theorem step5_m4096_3559 (q : ℕ) : step (step (step (step (step (4096 * q + 3559))))) = 15552 * q + 13517 := by
  rw [step4_m4096_3559 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 9011) + 1 = 2 ^ 1 * (15552 * q + 13517) := by ring
  have h_odd : (15552 * q + 13517) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 9011) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 13517) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 13517) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 13517) (by positivity)]

theorem step6_m4096_3559 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3559)))))) = 5832 * q + 5069 := by
  rw [step5_m4096_3559 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 13517) + 1 = 2 ^ 3 * (5832 * q + 5069) := by ring
  have h_odd : (5832 * q + 5069) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 13517) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (5832 * q + 5069) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (5832 * q + 5069) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 5069) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3559 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3559 (q : ℕ) (hq : 4096 * q + 3559 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3559))))))) < 4096 * q + 3559 := by
  rw [step6_m4096_3559 q]
  have h_bound : step (5832 * q + 5069) ≤ 2187 * q + 1901 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 5069) + 1 = 2 ^ 3 * (2187 * q + 1901) := by ring
    have hne : (2187 * q + 1901) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 5069) + 1) = 3 + ν₂ (2187 * q + 1901) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 1901) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1901) (2 ^ ν₂ (2187 * q + 1901)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3675 (q : ℕ) : step (4096 * q + 3675) = 6144 * q + 5513 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3675) + 1 = 2 ^ 1 * (6144 * q + 5513) := by ring
  have h_odd : (6144 * q + 5513) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3675) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 5513) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 5513) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5513) (by positivity)]

theorem step2_m4096_3675 (q : ℕ) : step (step (4096 * q + 3675)) = 4608 * q + 4135 := by
  rw [step_m4096_3675 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5513) + 1 = 2 ^ 2 * (4608 * q + 4135) := by ring
  have h_odd : (4608 * q + 4135) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5513) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 4135) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 4135) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 4135) (by positivity)]

theorem step3_m4096_3675 (q : ℕ) : step (step (step (4096 * q + 3675))) = 6912 * q + 6203 := by
  rw [step2_m4096_3675 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 4135) + 1 = 2 ^ 1 * (6912 * q + 6203) := by ring
  have h_odd : (6912 * q + 6203) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 4135) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 6203) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 6203) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 6203) (by positivity)]

theorem step4_m4096_3675 (q : ℕ) : step (step (step (step (4096 * q + 3675)))) = 10368 * q + 9305 := by
  rw [step3_m4096_3675 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 6203) + 1 = 2 ^ 1 * (10368 * q + 9305) := by ring
  have h_odd : (10368 * q + 9305) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 6203) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 9305) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 9305) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 9305) (by positivity)]

theorem step5_m4096_3675 (q : ℕ) : step (step (step (step (step (4096 * q + 3675))))) = 7776 * q + 6979 := by
  rw [step4_m4096_3675 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 9305) + 1 = 2 ^ 2 * (7776 * q + 6979) := by ring
  have h_odd : (7776 * q + 6979) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 9305) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 6979) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 6979) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 6979) (by positivity)]

theorem step6_m4096_3675 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3675)))))) = 11664 * q + 10469 := by
  rw [step5_m4096_3675 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 6979) + 1 = 2 ^ 1 * (11664 * q + 10469) := by ring
  have h_odd : (11664 * q + 10469) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 6979) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 10469) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 10469) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 10469) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3675 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3675 (q : ℕ) (hq : 4096 * q + 3675 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3675))))))) < 4096 * q + 3675 := by
  rw [step6_m4096_3675 q]
  have h_bound : step (11664 * q + 10469) ≤ 2187 * q + 1963 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 10469) + 1 = 2 ^ 4 * (2187 * q + 1963) := by ring
    have hne : (2187 * q + 1963) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 10469) + 1) = 4 + ν₂ (2187 * q + 1963) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 1963) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 1963) (2 ^ ν₂ (2187 * q + 1963)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3809 (q : ℕ) : step (4096 * q + 3809) = 3072 * q + 2857 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3809) + 1 = 2 ^ 2 * (3072 * q + 2857) := by ring
  have h_odd : (3072 * q + 2857) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3809) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 2857) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 2857) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 2857) (by positivity)]

theorem step2_m4096_3809 (q : ℕ) : step (step (4096 * q + 3809)) = 2304 * q + 2143 := by
  rw [step_m4096_3809 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 2857) + 1 = 2 ^ 2 * (2304 * q + 2143) := by ring
  have h_odd : (2304 * q + 2143) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 2857) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (2304 * q + 2143) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (2304 * q + 2143) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2304 * q + 2143) (by positivity)]

theorem step3_m4096_3809 (q : ℕ) : step (step (step (4096 * q + 3809))) = 3456 * q + 3215 := by
  rw [step2_m4096_3809 q]
  unfold step
  have h3n1 : 3 * (2304 * q + 2143) + 1 = 2 ^ 1 * (3456 * q + 3215) := by ring
  have h_odd : (3456 * q + 3215) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2304 * q + 2143) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (3456 * q + 3215) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (3456 * q + 3215) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 3215) (by positivity)]

theorem step4_m4096_3809 (q : ℕ) : step (step (step (step (4096 * q + 3809)))) = 5184 * q + 4823 := by
  rw [step3_m4096_3809 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 3215) + 1 = 2 ^ 1 * (5184 * q + 4823) := by ring
  have h_odd : (5184 * q + 4823) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 3215) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (5184 * q + 4823) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (5184 * q + 4823) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 4823) (by positivity)]

theorem step5_m4096_3809 (q : ℕ) : step (step (step (step (step (4096 * q + 3809))))) = 7776 * q + 7235 := by
  rw [step4_m4096_3809 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 4823) + 1 = 2 ^ 1 * (7776 * q + 7235) := by ring
  have h_odd : (7776 * q + 7235) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 4823) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 7235) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 7235) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 7235) (by positivity)]

theorem step6_m4096_3809 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3809)))))) = 11664 * q + 10853 := by
  rw [step5_m4096_3809 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 7235) + 1 = 2 ^ 1 * (11664 * q + 10853) := by ring
  have h_odd : (11664 * q + 10853) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 7235) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 10853) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 10853) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 10853) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3809 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3809 (q : ℕ) (hq : 4096 * q + 3809 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3809))))))) < 4096 * q + 3809 := by
  rw [step6_m4096_3809 q]
  have h_bound : step (11664 * q + 10853) ≤ 2187 * q + 2035 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 10853) + 1 = 2 ^ 4 * (2187 * q + 2035) := by ring
    have hne : (2187 * q + 2035) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 10853) + 1) = 4 + ν₂ (2187 * q + 2035) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 2035) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 2035) (2 ^ ν₂ (2187 * q + 2035)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3817 (q : ℕ) : step (4096 * q + 3817) = 3072 * q + 2863 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3817) + 1 = 2 ^ 2 * (3072 * q + 2863) := by ring
  have h_odd : (3072 * q + 2863) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3817) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3072 * q + 2863) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3072 * q + 2863) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3072 * q + 2863) (by positivity)]

theorem step2_m4096_3817 (q : ℕ) : step (step (4096 * q + 3817)) = 4608 * q + 4295 := by
  rw [step_m4096_3817 q]
  unfold step
  have h3n1 : 3 * (3072 * q + 2863) + 1 = 2 ^ 1 * (4608 * q + 4295) := by ring
  have h_odd : (4608 * q + 4295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3072 * q + 2863) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4608 * q + 4295) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4608 * q + 4295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 4295) (by positivity)]

theorem step3_m4096_3817 (q : ℕ) : step (step (step (4096 * q + 3817))) = 6912 * q + 6443 := by
  rw [step2_m4096_3817 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 4295) + 1 = 2 ^ 1 * (6912 * q + 6443) := by ring
  have h_odd : (6912 * q + 6443) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 4295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 6443) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 6443) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 6443) (by positivity)]

theorem step4_m4096_3817 (q : ℕ) : step (step (step (step (4096 * q + 3817)))) = 10368 * q + 9665 := by
  rw [step3_m4096_3817 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 6443) + 1 = 2 ^ 1 * (10368 * q + 9665) := by ring
  have h_odd : (10368 * q + 9665) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 6443) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 9665) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 9665) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 9665) (by positivity)]

theorem step5_m4096_3817 (q : ℕ) : step (step (step (step (step (4096 * q + 3817))))) = 7776 * q + 7249 := by
  rw [step4_m4096_3817 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 9665) + 1 = 2 ^ 2 * (7776 * q + 7249) := by ring
  have h_odd : (7776 * q + 7249) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 9665) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 7249) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 7249) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 7249) (by positivity)]

theorem step6_m4096_3817 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3817)))))) = 5832 * q + 5437 := by
  rw [step5_m4096_3817 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 7249) + 1 = 2 ^ 2 * (5832 * q + 5437) := by ring
  have h_odd : (5832 * q + 5437) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 7249) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5832 * q + 5437) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5832 * q + 5437) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5832 * q + 5437) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3817 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3817 (q : ℕ) (hq : 4096 * q + 3817 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3817))))))) < 4096 * q + 3817 := by
  rw [step6_m4096_3817 q]
  have h_bound : step (5832 * q + 5437) ≤ 2187 * q + 2039 := by
    unfold step
    have h3n1 : 3 * (5832 * q + 5437) + 1 = 2 ^ 3 * (2187 * q + 2039) := by ring
    have hne : (2187 * q + 2039) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (5832 * q + 5437) + 1) = 3 + ν₂ (2187 * q + 2039) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (2187 * q + 2039) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 2039) (2 ^ ν₂ (2187 * q + 2039)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_3911 (q : ℕ) : step (4096 * q + 3911) = 6144 * q + 5867 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 3911) + 1 = 2 ^ 1 * (6144 * q + 5867) := by ring
  have h_odd : (6144 * q + 5867) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 3911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 5867) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 5867) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5867) (by positivity)]

theorem step2_m4096_3911 (q : ℕ) : step (step (4096 * q + 3911)) = 9216 * q + 8801 := by
  rw [step_m4096_3911 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5867) + 1 = 2 ^ 1 * (9216 * q + 8801) := by ring
  have h_odd : (9216 * q + 8801) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5867) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 8801) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 8801) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 8801) (by positivity)]

theorem step3_m4096_3911 (q : ℕ) : step (step (step (4096 * q + 3911))) = 6912 * q + 6601 := by
  rw [step2_m4096_3911 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 8801) + 1 = 2 ^ 2 * (6912 * q + 6601) := by ring
  have h_odd : (6912 * q + 6601) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 8801) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 6601) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 6601) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 6601) (by positivity)]

theorem step4_m4096_3911 (q : ℕ) : step (step (step (step (4096 * q + 3911)))) = 5184 * q + 4951 := by
  rw [step3_m4096_3911 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 6601) + 1 = 2 ^ 2 * (5184 * q + 4951) := by ring
  have h_odd : (5184 * q + 4951) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 6601) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 4951) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 4951) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 4951) (by positivity)]

theorem step5_m4096_3911 (q : ℕ) : step (step (step (step (step (4096 * q + 3911))))) = 7776 * q + 7427 := by
  rw [step4_m4096_3911 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 4951) + 1 = 2 ^ 1 * (7776 * q + 7427) := by ring
  have h_odd : (7776 * q + 7427) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 4951) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (7776 * q + 7427) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (7776 * q + 7427) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 7427) (by positivity)]

theorem step6_m4096_3911 (q : ℕ) : step (step (step (step (step (step (4096 * q + 3911)))))) = 11664 * q + 11141 := by
  rw [step5_m4096_3911 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 7427) + 1 = 2 ^ 1 * (11664 * q + 11141) := by ring
  have h_odd : (11664 * q + 11141) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 7427) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 11141) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 11141) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 11141) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3911 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_3911 (q : ℕ) (hq : 4096 * q + 3911 > 1) :
    step (step (step (step (step (step (step (4096 * q + 3911))))))) < 4096 * q + 3911 := by
  rw [step6_m4096_3911 q]
  have h_bound : step (11664 * q + 11141) ≤ 2187 * q + 2089 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 11141) + 1 = 2 ^ 4 * (2187 * q + 2089) := by ring
    have hne : (2187 * q + 2089) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 11141) + 1) = 4 + ν₂ (2187 * q + 2089) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 2089) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 2089) (2 ^ ν₂ (2187 * q + 2089)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m4096_4063 (q : ℕ) : step (4096 * q + 4063) = 6144 * q + 6095 := by
  unfold step
  have h3n1 : 3 * (4096 * q + 4063) + 1 = 2 ^ 1 * (6144 * q + 6095) := by ring
  have h_odd : (6144 * q + 6095) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4096 * q + 4063) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6144 * q + 6095) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6144 * q + 6095) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 6095) (by positivity)]

theorem step2_m4096_4063 (q : ℕ) : step (step (4096 * q + 4063)) = 9216 * q + 9143 := by
  rw [step_m4096_4063 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 6095) + 1 = 2 ^ 1 * (9216 * q + 9143) := by ring
  have h_odd : (9216 * q + 9143) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 6095) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 9143) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 9143) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 9143) (by positivity)]

theorem step3_m4096_4063 (q : ℕ) : step (step (step (4096 * q + 4063))) = 13824 * q + 13715 := by
  rw [step2_m4096_4063 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 9143) + 1 = 2 ^ 1 * (13824 * q + 13715) := by ring
  have h_odd : (13824 * q + 13715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 9143) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 13715) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 13715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 13715) (by positivity)]

theorem step4_m4096_4063 (q : ℕ) : step (step (step (step (4096 * q + 4063)))) = 20736 * q + 20573 := by
  rw [step3_m4096_4063 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 13715) + 1 = 2 ^ 1 * (20736 * q + 20573) := by ring
  have h_odd : (20736 * q + 20573) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 13715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 20573) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 20573) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 20573) (by positivity)]

theorem step5_m4096_4063 (q : ℕ) : step (step (step (step (step (4096 * q + 4063))))) = 7776 * q + 7715 := by
  rw [step4_m4096_4063 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 20573) + 1 = 2 ^ 3 * (7776 * q + 7715) := by ring
  have h_odd : (7776 * q + 7715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 20573) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (7776 * q + 7715) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (7776 * q + 7715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 7715) (by positivity)]

theorem step6_m4096_4063 (q : ℕ) : step (step (step (step (step (step (4096 * q + 4063)))))) = 11664 * q + 11573 := by
  rw [step5_m4096_4063 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 7715) + 1 = 2 ^ 1 * (11664 * q + 11573) := by ring
  have h_odd : (11664 * q + 11573) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 7715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 11573) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 11573) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 11573) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4063 (mod 4096) ⇒ step^7(n) < n. -/
theorem descent_m4096_4063 (q : ℕ) (hq : 4096 * q + 4063 > 1) :
    step (step (step (step (step (step (step (4096 * q + 4063))))))) < 4096 * q + 4063 := by
  rw [step6_m4096_4063 q]
  have h_bound : step (11664 * q + 11573) ≤ 2187 * q + 2170 := by
    unfold step
    have h3n1 : 3 * (11664 * q + 11573) + 1 = 2 ^ 4 * (2187 * q + 2170) := by ring
    have hne : (2187 * q + 2170) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (11664 * q + 11573) + 1) = 4 + ν₂ (2187 * q + 2170) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (2187 * q + 2170) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (2187 * q + 2170) (2 ^ ν₂ (2187 * q + 2170)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_191 (q : ℕ) : step (8192 * q + 191) = 12288 * q + 287 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 191) + 1 = 2 ^ 1 * (12288 * q + 287) := by ring
  have h_odd : (12288 * q + 287) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 191) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 287) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 287) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 287) (by positivity)]

theorem step2_m8192_191 (q : ℕ) : step (step (8192 * q + 191)) = 18432 * q + 431 := by
  rw [step_m8192_191 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 287) + 1 = 2 ^ 1 * (18432 * q + 431) := by ring
  have h_odd : (18432 * q + 431) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 287) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 431) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 431) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 431) (by positivity)]

theorem step3_m8192_191 (q : ℕ) : step (step (step (8192 * q + 191))) = 27648 * q + 647 := by
  rw [step2_m8192_191 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 431) + 1 = 2 ^ 1 * (27648 * q + 647) := by ring
  have h_odd : (27648 * q + 647) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 431) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 647) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 647) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 647) (by positivity)]

theorem step4_m8192_191 (q : ℕ) : step (step (step (step (8192 * q + 191)))) = 41472 * q + 971 := by
  rw [step3_m8192_191 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 647) + 1 = 2 ^ 1 * (41472 * q + 971) := by ring
  have h_odd : (41472 * q + 971) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 647) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 971) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 971) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 971) (by positivity)]

theorem step5_m8192_191 (q : ℕ) : step (step (step (step (step (8192 * q + 191))))) = 62208 * q + 1457 := by
  rw [step4_m8192_191 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 971) + 1 = 2 ^ 1 * (62208 * q + 1457) := by ring
  have h_odd : (62208 * q + 1457) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 971) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 1457) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 1457) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 1457) (by positivity)]

theorem step6_m8192_191 (q : ℕ) : step (step (step (step (step (step (8192 * q + 191)))))) = 46656 * q + 1093 := by
  rw [step5_m8192_191 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 1457) + 1 = 2 ^ 2 * (46656 * q + 1093) := by ring
  have h_odd : (46656 * q + 1093) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 1457) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (46656 * q + 1093) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (46656 * q + 1093) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 1093) (by positivity)]

theorem step7_m8192_191 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 191))))))) = 8748 * q + 205 := by
  rw [step6_m8192_191 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 1093) + 1 = 2 ^ 4 * (8748 * q + 205) := by ring
  have h_odd : (8748 * q + 205) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 1093) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (8748 * q + 205) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (8748 * q + 205) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 205) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 191 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_191 (q : ℕ) (hq : 8192 * q + 191 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 191)))))))) < 8192 * q + 191 := by
  rw [step7_m8192_191 q]
  have h_bound : step (8748 * q + 205) ≤ 6561 * q + 154 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 205) + 1 = 2 ^ 2 * (6561 * q + 154) := by ring
    have hne : (6561 * q + 154) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 205) + 1) = 2 + ν₂ (6561 * q + 154) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 154) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 154) (2 ^ ν₂ (6561 * q + 154)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_207 (q : ℕ) : step (8192 * q + 207) = 12288 * q + 311 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 207) + 1 = 2 ^ 1 * (12288 * q + 311) := by ring
  have h_odd : (12288 * q + 311) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 207) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 311) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 311) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 311) (by positivity)]

theorem step2_m8192_207 (q : ℕ) : step (step (8192 * q + 207)) = 18432 * q + 467 := by
  rw [step_m8192_207 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 311) + 1 = 2 ^ 1 * (18432 * q + 467) := by ring
  have h_odd : (18432 * q + 467) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 311) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 467) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 467) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 467) (by positivity)]

theorem step3_m8192_207 (q : ℕ) : step (step (step (8192 * q + 207))) = 27648 * q + 701 := by
  rw [step2_m8192_207 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 467) + 1 = 2 ^ 1 * (27648 * q + 701) := by ring
  have h_odd : (27648 * q + 701) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 467) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 701) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 701) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 701) (by positivity)]

theorem step4_m8192_207 (q : ℕ) : step (step (step (step (8192 * q + 207)))) = 10368 * q + 263 := by
  rw [step3_m8192_207 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 701) + 1 = 2 ^ 3 * (10368 * q + 263) := by ring
  have h_odd : (10368 * q + 263) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 701) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (10368 * q + 263) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (10368 * q + 263) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 263) (by positivity)]

theorem step5_m8192_207 (q : ℕ) : step (step (step (step (step (8192 * q + 207))))) = 15552 * q + 395 := by
  rw [step4_m8192_207 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 263) + 1 = 2 ^ 1 * (15552 * q + 395) := by ring
  have h_odd : (15552 * q + 395) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 263) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 395) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 395) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 395) (by positivity)]

theorem step6_m8192_207 (q : ℕ) : step (step (step (step (step (step (8192 * q + 207)))))) = 23328 * q + 593 := by
  rw [step5_m8192_207 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 395) + 1 = 2 ^ 1 * (23328 * q + 593) := by ring
  have h_odd : (23328 * q + 593) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 395) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 593) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 593) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 593) (by positivity)]

theorem step7_m8192_207 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 207))))))) = 17496 * q + 445 := by
  rw [step6_m8192_207 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 593) + 1 = 2 ^ 2 * (17496 * q + 445) := by ring
  have h_odd : (17496 * q + 445) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 593) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 445) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 445) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 445) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 207 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_207 (q : ℕ) (hq : 8192 * q + 207 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 207)))))))) < 8192 * q + 207 := by
  rw [step7_m8192_207 q]
  have h_bound : step (17496 * q + 445) ≤ 6561 * q + 167 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 445) + 1 = 2 ^ 3 * (6561 * q + 167) := by ring
    have hne : (6561 * q + 167) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 445) + 1) = 3 + ν₂ (6561 * q + 167) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 167) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 167) (2 ^ ν₂ (6561 * q + 167)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_255 (q : ℕ) : step (8192 * q + 255) = 12288 * q + 383 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 255) + 1 = 2 ^ 1 * (12288 * q + 383) := by ring
  have h_odd : (12288 * q + 383) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 255) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 383) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 383) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 383) (by positivity)]

theorem step2_m8192_255 (q : ℕ) : step (step (8192 * q + 255)) = 18432 * q + 575 := by
  rw [step_m8192_255 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 383) + 1 = 2 ^ 1 * (18432 * q + 575) := by ring
  have h_odd : (18432 * q + 575) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 383) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 575) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 575) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 575) (by positivity)]

theorem step3_m8192_255 (q : ℕ) : step (step (step (8192 * q + 255))) = 27648 * q + 863 := by
  rw [step2_m8192_255 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 575) + 1 = 2 ^ 1 * (27648 * q + 863) := by ring
  have h_odd : (27648 * q + 863) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 575) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 863) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 863) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 863) (by positivity)]

theorem step4_m8192_255 (q : ℕ) : step (step (step (step (8192 * q + 255)))) = 41472 * q + 1295 := by
  rw [step3_m8192_255 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 863) + 1 = 2 ^ 1 * (41472 * q + 1295) := by ring
  have h_odd : (41472 * q + 1295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 863) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 1295) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 1295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 1295) (by positivity)]

theorem step5_m8192_255 (q : ℕ) : step (step (step (step (step (8192 * q + 255))))) = 62208 * q + 1943 := by
  rw [step4_m8192_255 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 1295) + 1 = 2 ^ 1 * (62208 * q + 1943) := by ring
  have h_odd : (62208 * q + 1943) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 1295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 1943) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 1943) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 1943) (by positivity)]

theorem step6_m8192_255 (q : ℕ) : step (step (step (step (step (step (8192 * q + 255)))))) = 93312 * q + 2915 := by
  rw [step5_m8192_255 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 1943) + 1 = 2 ^ 1 * (93312 * q + 2915) := by ring
  have h_odd : (93312 * q + 2915) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 1943) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (93312 * q + 2915) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (93312 * q + 2915) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (93312 * q + 2915) (by positivity)]

theorem step7_m8192_255 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 255))))))) = 139968 * q + 4373 := by
  rw [step6_m8192_255 q]
  unfold step
  have h3n1 : 3 * (93312 * q + 2915) + 1 = 2 ^ 1 * (139968 * q + 4373) := by ring
  have h_odd : (139968 * q + 4373) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (93312 * q + 2915) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (139968 * q + 4373) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (139968 * q + 4373) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (139968 * q + 4373) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 255 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_255 (q : ℕ) (hq : 8192 * q + 255 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 255)))))))) < 8192 * q + 255 := by
  rw [step7_m8192_255 q]
  have h_bound : step (139968 * q + 4373) ≤ 6561 * q + 205 := by
    unfold step
    have h3n1 : 3 * (139968 * q + 4373) + 1 = 2 ^ 6 * (6561 * q + 205) := by ring
    have hne : (6561 * q + 205) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (139968 * q + 4373) + 1) = 6 + ν₂ (6561 * q + 205) := by
      rw [h3n1, ν₂_mul (2 ^ 6) (6561 * q + 205) (by positivity) hne, ν₂_pow_two' 6]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 205) (2 ^ ν₂ (6561 * q + 205)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_303 (q : ℕ) : step (8192 * q + 303) = 12288 * q + 455 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 303) + 1 = 2 ^ 1 * (12288 * q + 455) := by ring
  have h_odd : (12288 * q + 455) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 303) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 455) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 455) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 455) (by positivity)]

theorem step2_m8192_303 (q : ℕ) : step (step (8192 * q + 303)) = 18432 * q + 683 := by
  rw [step_m8192_303 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 455) + 1 = 2 ^ 1 * (18432 * q + 683) := by ring
  have h_odd : (18432 * q + 683) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 455) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 683) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 683) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 683) (by positivity)]

theorem step3_m8192_303 (q : ℕ) : step (step (step (8192 * q + 303))) = 27648 * q + 1025 := by
  rw [step2_m8192_303 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 683) + 1 = 2 ^ 1 * (27648 * q + 1025) := by ring
  have h_odd : (27648 * q + 1025) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 683) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 1025) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 1025) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 1025) (by positivity)]

theorem step4_m8192_303 (q : ℕ) : step (step (step (step (8192 * q + 303)))) = 20736 * q + 769 := by
  rw [step3_m8192_303 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 1025) + 1 = 2 ^ 2 * (20736 * q + 769) := by ring
  have h_odd : (20736 * q + 769) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 1025) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 769) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 769) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 769) (by positivity)]

theorem step5_m8192_303 (q : ℕ) : step (step (step (step (step (8192 * q + 303))))) = 15552 * q + 577 := by
  rw [step4_m8192_303 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 769) + 1 = 2 ^ 2 * (15552 * q + 577) := by ring
  have h_odd : (15552 * q + 577) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 769) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 577) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 577) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 577) (by positivity)]

theorem step6_m8192_303 (q : ℕ) : step (step (step (step (step (step (8192 * q + 303)))))) = 11664 * q + 433 := by
  rw [step5_m8192_303 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 577) + 1 = 2 ^ 2 * (11664 * q + 433) := by ring
  have h_odd : (11664 * q + 433) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 577) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 433) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 433) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 433) (by positivity)]

theorem step7_m8192_303 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 303))))))) = 8748 * q + 325 := by
  rw [step6_m8192_303 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 433) + 1 = 2 ^ 2 * (8748 * q + 325) := by ring
  have h_odd : (8748 * q + 325) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 433) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 325) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 325) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 325) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 303 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_303 (q : ℕ) (hq : 8192 * q + 303 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 303)))))))) < 8192 * q + 303 := by
  rw [step7_m8192_303 q]
  have h_bound : step (8748 * q + 325) ≤ 6561 * q + 244 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 325) + 1 = 2 ^ 2 * (6561 * q + 244) := by ring
    have hne : (6561 * q + 244) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 325) + 1) = 2 + ν₂ (6561 * q + 244) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 244) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 244) (2 ^ ν₂ (6561 * q + 244)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_539 (q : ℕ) : step (8192 * q + 539) = 12288 * q + 809 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 539) + 1 = 2 ^ 1 * (12288 * q + 809) := by ring
  have h_odd : (12288 * q + 809) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 539) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 809) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 809) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 809) (by positivity)]

theorem step2_m8192_539 (q : ℕ) : step (step (8192 * q + 539)) = 9216 * q + 607 := by
  rw [step_m8192_539 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 809) + 1 = 2 ^ 2 * (9216 * q + 607) := by ring
  have h_odd : (9216 * q + 607) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 809) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 607) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 607) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 607) (by positivity)]

theorem step3_m8192_539 (q : ℕ) : step (step (step (8192 * q + 539))) = 13824 * q + 911 := by
  rw [step2_m8192_539 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 607) + 1 = 2 ^ 1 * (13824 * q + 911) := by ring
  have h_odd : (13824 * q + 911) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 911) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 911) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 911) (by positivity)]

theorem step4_m8192_539 (q : ℕ) : step (step (step (step (8192 * q + 539)))) = 20736 * q + 1367 := by
  rw [step3_m8192_539 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 911) + 1 = 2 ^ 1 * (20736 * q + 1367) := by ring
  have h_odd : (20736 * q + 1367) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 1367) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 1367) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 1367) (by positivity)]

theorem step5_m8192_539 (q : ℕ) : step (step (step (step (step (8192 * q + 539))))) = 31104 * q + 2051 := by
  rw [step4_m8192_539 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 1367) + 1 = 2 ^ 1 * (31104 * q + 2051) := by ring
  have h_odd : (31104 * q + 2051) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 1367) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 2051) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 2051) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 2051) (by positivity)]

theorem step6_m8192_539 (q : ℕ) : step (step (step (step (step (step (8192 * q + 539)))))) = 46656 * q + 3077 := by
  rw [step5_m8192_539 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 2051) + 1 = 2 ^ 1 * (46656 * q + 3077) := by ring
  have h_odd : (46656 * q + 3077) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 2051) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 3077) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 3077) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 3077) (by positivity)]

theorem step7_m8192_539 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 539))))))) = 8748 * q + 577 := by
  rw [step6_m8192_539 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 3077) + 1 = 2 ^ 4 * (8748 * q + 577) := by ring
  have h_odd : (8748 * q + 577) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 3077) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (8748 * q + 577) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (8748 * q + 577) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 577) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 539 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_539 (q : ℕ) (hq : 8192 * q + 539 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 539)))))))) < 8192 * q + 539 := by
  rw [step7_m8192_539 q]
  have h_bound : step (8748 * q + 577) ≤ 6561 * q + 433 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 577) + 1 = 2 ^ 2 * (6561 * q + 433) := by ring
    have hne : (6561 * q + 433) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 577) + 1) = 2 + ν₂ (6561 * q + 433) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 433) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 433) (2 ^ ν₂ (6561 * q + 433)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_543 (q : ℕ) : step (8192 * q + 543) = 12288 * q + 815 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 543) + 1 = 2 ^ 1 * (12288 * q + 815) := by ring
  have h_odd : (12288 * q + 815) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 543) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 815) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 815) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 815) (by positivity)]

theorem step2_m8192_543 (q : ℕ) : step (step (8192 * q + 543)) = 18432 * q + 1223 := by
  rw [step_m8192_543 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 815) + 1 = 2 ^ 1 * (18432 * q + 1223) := by ring
  have h_odd : (18432 * q + 1223) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 815) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 1223) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 1223) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 1223) (by positivity)]

theorem step3_m8192_543 (q : ℕ) : step (step (step (8192 * q + 543))) = 27648 * q + 1835 := by
  rw [step2_m8192_543 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 1223) + 1 = 2 ^ 1 * (27648 * q + 1835) := by ring
  have h_odd : (27648 * q + 1835) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 1223) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 1835) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 1835) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 1835) (by positivity)]

theorem step4_m8192_543 (q : ℕ) : step (step (step (step (8192 * q + 543)))) = 41472 * q + 2753 := by
  rw [step3_m8192_543 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 1835) + 1 = 2 ^ 1 * (41472 * q + 2753) := by ring
  have h_odd : (41472 * q + 2753) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 1835) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 2753) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 2753) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 2753) (by positivity)]

theorem step5_m8192_543 (q : ℕ) : step (step (step (step (step (8192 * q + 543))))) = 31104 * q + 2065 := by
  rw [step4_m8192_543 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 2753) + 1 = 2 ^ 2 * (31104 * q + 2065) := by ring
  have h_odd : (31104 * q + 2065) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 2753) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 2065) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 2065) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 2065) (by positivity)]

theorem step6_m8192_543 (q : ℕ) : step (step (step (step (step (step (8192 * q + 543)))))) = 23328 * q + 1549 := by
  rw [step5_m8192_543 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 2065) + 1 = 2 ^ 2 * (23328 * q + 1549) := by ring
  have h_odd : (23328 * q + 1549) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 2065) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 1549) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 1549) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 1549) (by positivity)]

theorem step7_m8192_543 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 543))))))) = 8748 * q + 581 := by
  rw [step6_m8192_543 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 1549) + 1 = 2 ^ 3 * (8748 * q + 581) := by ring
  have h_odd : (8748 * q + 581) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 1549) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 581) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 581) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 581) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 543 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_543 (q : ℕ) (hq : 8192 * q + 543 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 543)))))))) < 8192 * q + 543 := by
  rw [step7_m8192_543 q]
  have h_bound : step (8748 * q + 581) ≤ 6561 * q + 436 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 581) + 1 = 2 ^ 2 * (6561 * q + 436) := by ring
    have hne : (6561 * q + 436) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 581) + 1) = 2 + ν₂ (6561 * q + 436) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 436) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 436) (2 ^ ν₂ (6561 * q + 436)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_623 (q : ℕ) : step (8192 * q + 623) = 12288 * q + 935 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 623) + 1 = 2 ^ 1 * (12288 * q + 935) := by ring
  have h_odd : (12288 * q + 935) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 623) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 935) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 935) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 935) (by positivity)]

theorem step2_m8192_623 (q : ℕ) : step (step (8192 * q + 623)) = 18432 * q + 1403 := by
  rw [step_m8192_623 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 935) + 1 = 2 ^ 1 * (18432 * q + 1403) := by ring
  have h_odd : (18432 * q + 1403) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 935) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 1403) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 1403) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 1403) (by positivity)]

theorem step3_m8192_623 (q : ℕ) : step (step (step (8192 * q + 623))) = 27648 * q + 2105 := by
  rw [step2_m8192_623 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 1403) + 1 = 2 ^ 1 * (27648 * q + 2105) := by ring
  have h_odd : (27648 * q + 2105) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 1403) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 2105) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 2105) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 2105) (by positivity)]

theorem step4_m8192_623 (q : ℕ) : step (step (step (step (8192 * q + 623)))) = 20736 * q + 1579 := by
  rw [step3_m8192_623 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 2105) + 1 = 2 ^ 2 * (20736 * q + 1579) := by ring
  have h_odd : (20736 * q + 1579) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 2105) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 1579) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 1579) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 1579) (by positivity)]

theorem step5_m8192_623 (q : ℕ) : step (step (step (step (step (8192 * q + 623))))) = 31104 * q + 2369 := by
  rw [step4_m8192_623 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 1579) + 1 = 2 ^ 1 * (31104 * q + 2369) := by ring
  have h_odd : (31104 * q + 2369) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 1579) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 2369) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 2369) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 2369) (by positivity)]

theorem step6_m8192_623 (q : ℕ) : step (step (step (step (step (step (8192 * q + 623)))))) = 23328 * q + 1777 := by
  rw [step5_m8192_623 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 2369) + 1 = 2 ^ 2 * (23328 * q + 1777) := by ring
  have h_odd : (23328 * q + 1777) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 2369) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 1777) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 1777) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 1777) (by positivity)]

theorem step7_m8192_623 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 623))))))) = 17496 * q + 1333 := by
  rw [step6_m8192_623 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 1777) + 1 = 2 ^ 2 * (17496 * q + 1333) := by ring
  have h_odd : (17496 * q + 1333) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 1777) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 1333) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 1333) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 1333) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 623 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_623 (q : ℕ) (hq : 8192 * q + 623 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 623)))))))) < 8192 * q + 623 := by
  rw [step7_m8192_623 q]
  have h_bound : step (17496 * q + 1333) ≤ 6561 * q + 500 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 1333) + 1 = 2 ^ 3 * (6561 * q + 500) := by ring
    have hne : (6561 * q + 500) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 1333) + 1) = 3 + ν₂ (6561 * q + 500) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 500) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 500) (2 ^ ν₂ (6561 * q + 500)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_679 (q : ℕ) : step (8192 * q + 679) = 12288 * q + 1019 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 679) + 1 = 2 ^ 1 * (12288 * q + 1019) := by ring
  have h_odd : (12288 * q + 1019) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 679) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1019) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1019) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1019) (by positivity)]

theorem step2_m8192_679 (q : ℕ) : step (step (8192 * q + 679)) = 18432 * q + 1529 := by
  rw [step_m8192_679 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1019) + 1 = 2 ^ 1 * (18432 * q + 1529) := by ring
  have h_odd : (18432 * q + 1529) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1019) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 1529) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 1529) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 1529) (by positivity)]

theorem step3_m8192_679 (q : ℕ) : step (step (step (8192 * q + 679))) = 13824 * q + 1147 := by
  rw [step2_m8192_679 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 1529) + 1 = 2 ^ 2 * (13824 * q + 1147) := by ring
  have h_odd : (13824 * q + 1147) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 1529) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 1147) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 1147) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 1147) (by positivity)]

theorem step4_m8192_679 (q : ℕ) : step (step (step (step (8192 * q + 679)))) = 20736 * q + 1721 := by
  rw [step3_m8192_679 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 1147) + 1 = 2 ^ 1 * (20736 * q + 1721) := by ring
  have h_odd : (20736 * q + 1721) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 1147) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 1721) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 1721) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 1721) (by positivity)]

theorem step5_m8192_679 (q : ℕ) : step (step (step (step (step (8192 * q + 679))))) = 15552 * q + 1291 := by
  rw [step4_m8192_679 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 1721) + 1 = 2 ^ 2 * (15552 * q + 1291) := by ring
  have h_odd : (15552 * q + 1291) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 1721) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 1291) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 1291) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 1291) (by positivity)]

theorem step6_m8192_679 (q : ℕ) : step (step (step (step (step (step (8192 * q + 679)))))) = 23328 * q + 1937 := by
  rw [step5_m8192_679 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 1291) + 1 = 2 ^ 1 * (23328 * q + 1937) := by ring
  have h_odd : (23328 * q + 1937) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 1291) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 1937) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 1937) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 1937) (by positivity)]

theorem step7_m8192_679 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 679))))))) = 17496 * q + 1453 := by
  rw [step6_m8192_679 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 1937) + 1 = 2 ^ 2 * (17496 * q + 1453) := by ring
  have h_odd : (17496 * q + 1453) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 1937) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 1453) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 1453) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 1453) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 679 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_679 (q : ℕ) (hq : 8192 * q + 679 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 679)))))))) < 8192 * q + 679 := by
  rw [step7_m8192_679 q]
  have h_bound : step (17496 * q + 1453) ≤ 6561 * q + 545 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 1453) + 1 = 2 ^ 3 * (6561 * q + 545) := by ring
    have hne : (6561 * q + 545) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 1453) + 1) = 3 + ν₂ (6561 * q + 545) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 545) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 545) (2 ^ ν₂ (6561 * q + 545)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_719 (q : ℕ) : step (8192 * q + 719) = 12288 * q + 1079 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 719) + 1 = 2 ^ 1 * (12288 * q + 1079) := by ring
  have h_odd : (12288 * q + 1079) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 719) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1079) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1079) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1079) (by positivity)]

theorem step2_m8192_719 (q : ℕ) : step (step (8192 * q + 719)) = 18432 * q + 1619 := by
  rw [step_m8192_719 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1079) + 1 = 2 ^ 1 * (18432 * q + 1619) := by ring
  have h_odd : (18432 * q + 1619) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1079) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 1619) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 1619) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 1619) (by positivity)]

theorem step3_m8192_719 (q : ℕ) : step (step (step (8192 * q + 719))) = 27648 * q + 2429 := by
  rw [step2_m8192_719 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 1619) + 1 = 2 ^ 1 * (27648 * q + 2429) := by ring
  have h_odd : (27648 * q + 2429) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 1619) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 2429) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 2429) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 2429) (by positivity)]

theorem step4_m8192_719 (q : ℕ) : step (step (step (step (8192 * q + 719)))) = 10368 * q + 911 := by
  rw [step3_m8192_719 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 2429) + 1 = 2 ^ 3 * (10368 * q + 911) := by ring
  have h_odd : (10368 * q + 911) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 2429) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (10368 * q + 911) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (10368 * q + 911) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 911) (by positivity)]

theorem step5_m8192_719 (q : ℕ) : step (step (step (step (step (8192 * q + 719))))) = 15552 * q + 1367 := by
  rw [step4_m8192_719 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 911) + 1 = 2 ^ 1 * (15552 * q + 1367) := by ring
  have h_odd : (15552 * q + 1367) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 1367) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 1367) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 1367) (by positivity)]

theorem step6_m8192_719 (q : ℕ) : step (step (step (step (step (step (8192 * q + 719)))))) = 23328 * q + 2051 := by
  rw [step5_m8192_719 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 1367) + 1 = 2 ^ 1 * (23328 * q + 2051) := by ring
  have h_odd : (23328 * q + 2051) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 1367) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 2051) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 2051) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 2051) (by positivity)]

theorem step7_m8192_719 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 719))))))) = 34992 * q + 3077 := by
  rw [step6_m8192_719 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 2051) + 1 = 2 ^ 1 * (34992 * q + 3077) := by ring
  have h_odd : (34992 * q + 3077) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 2051) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 3077) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 3077) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 3077) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 719 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_719 (q : ℕ) (hq : 8192 * q + 719 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 719)))))))) < 8192 * q + 719 := by
  rw [step7_m8192_719 q]
  have h_bound : step (34992 * q + 3077) ≤ 6561 * q + 577 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 3077) + 1 = 2 ^ 4 * (6561 * q + 577) := by ring
    have hne : (6561 * q + 577) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 3077) + 1) = 4 + ν₂ (6561 * q + 577) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 577) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 577) (2 ^ ν₂ (6561 * q + 577)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_799 (q : ℕ) : step (8192 * q + 799) = 12288 * q + 1199 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 799) + 1 = 2 ^ 1 * (12288 * q + 1199) := by ring
  have h_odd : (12288 * q + 1199) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 799) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1199) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1199) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1199) (by positivity)]

theorem step2_m8192_799 (q : ℕ) : step (step (8192 * q + 799)) = 18432 * q + 1799 := by
  rw [step_m8192_799 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1199) + 1 = 2 ^ 1 * (18432 * q + 1799) := by ring
  have h_odd : (18432 * q + 1799) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1199) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 1799) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 1799) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 1799) (by positivity)]

theorem step3_m8192_799 (q : ℕ) : step (step (step (8192 * q + 799))) = 27648 * q + 2699 := by
  rw [step2_m8192_799 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 1799) + 1 = 2 ^ 1 * (27648 * q + 2699) := by ring
  have h_odd : (27648 * q + 2699) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 1799) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 2699) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 2699) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 2699) (by positivity)]

theorem step4_m8192_799 (q : ℕ) : step (step (step (step (8192 * q + 799)))) = 41472 * q + 4049 := by
  rw [step3_m8192_799 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 2699) + 1 = 2 ^ 1 * (41472 * q + 4049) := by ring
  have h_odd : (41472 * q + 4049) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 2699) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 4049) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 4049) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 4049) (by positivity)]

theorem step5_m8192_799 (q : ℕ) : step (step (step (step (step (8192 * q + 799))))) = 31104 * q + 3037 := by
  rw [step4_m8192_799 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 4049) + 1 = 2 ^ 2 * (31104 * q + 3037) := by ring
  have h_odd : (31104 * q + 3037) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 4049) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 3037) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 3037) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 3037) (by positivity)]

theorem step6_m8192_799 (q : ℕ) : step (step (step (step (step (step (8192 * q + 799)))))) = 11664 * q + 1139 := by
  rw [step5_m8192_799 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 3037) + 1 = 2 ^ 3 * (11664 * q + 1139) := by ring
  have h_odd : (11664 * q + 1139) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 3037) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 1139) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 1139) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 1139) (by positivity)]

theorem step7_m8192_799 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 799))))))) = 17496 * q + 1709 := by
  rw [step6_m8192_799 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 1139) + 1 = 2 ^ 1 * (17496 * q + 1709) := by ring
  have h_odd : (17496 * q + 1709) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 1139) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 1709) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 1709) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 1709) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 799 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_799 (q : ℕ) (hq : 8192 * q + 799 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 799)))))))) < 8192 * q + 799 := by
  rw [step7_m8192_799 q]
  have h_bound : step (17496 * q + 1709) ≤ 6561 * q + 641 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 1709) + 1 = 2 ^ 3 * (6561 * q + 641) := by ring
    have hne : (6561 * q + 641) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 1709) + 1) = 3 + ν₂ (6561 * q + 641) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 641) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 641) (2 ^ ν₂ (6561 * q + 641)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1071 (q : ℕ) : step (8192 * q + 1071) = 12288 * q + 1607 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1071) + 1 = 2 ^ 1 * (12288 * q + 1607) := by ring
  have h_odd : (12288 * q + 1607) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1071) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1607) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1607) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1607) (by positivity)]

theorem step2_m8192_1071 (q : ℕ) : step (step (8192 * q + 1071)) = 18432 * q + 2411 := by
  rw [step_m8192_1071 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1607) + 1 = 2 ^ 1 * (18432 * q + 2411) := by ring
  have h_odd : (18432 * q + 2411) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 2411) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 2411) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 2411) (by positivity)]

theorem step3_m8192_1071 (q : ℕ) : step (step (step (8192 * q + 1071))) = 27648 * q + 3617 := by
  rw [step2_m8192_1071 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 2411) + 1 = 2 ^ 1 * (27648 * q + 3617) := by ring
  have h_odd : (27648 * q + 3617) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 2411) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 3617) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 3617) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 3617) (by positivity)]

theorem step4_m8192_1071 (q : ℕ) : step (step (step (step (8192 * q + 1071)))) = 20736 * q + 2713 := by
  rw [step3_m8192_1071 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 3617) + 1 = 2 ^ 2 * (20736 * q + 2713) := by ring
  have h_odd : (20736 * q + 2713) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 3617) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 2713) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 2713) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 2713) (by positivity)]

theorem step5_m8192_1071 (q : ℕ) : step (step (step (step (step (8192 * q + 1071))))) = 15552 * q + 2035 := by
  rw [step4_m8192_1071 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 2713) + 1 = 2 ^ 2 * (15552 * q + 2035) := by ring
  have h_odd : (15552 * q + 2035) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 2713) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 2035) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 2035) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 2035) (by positivity)]

theorem step6_m8192_1071 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1071)))))) = 23328 * q + 3053 := by
  rw [step5_m8192_1071 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 2035) + 1 = 2 ^ 1 * (23328 * q + 3053) := by ring
  have h_odd : (23328 * q + 3053) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 2035) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 3053) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 3053) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 3053) (by positivity)]

theorem step7_m8192_1071 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1071))))))) = 8748 * q + 1145 := by
  rw [step6_m8192_1071 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 3053) + 1 = 2 ^ 3 * (8748 * q + 1145) := by ring
  have h_odd : (8748 * q + 1145) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 3053) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 1145) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 1145) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 1145) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1071 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1071 (q : ℕ) (hq : 8192 * q + 1071 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1071)))))))) < 8192 * q + 1071 := by
  rw [step7_m8192_1071 q]
  have h_bound : step (8748 * q + 1145) ≤ 6561 * q + 859 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 1145) + 1 = 2 ^ 2 * (6561 * q + 859) := by ring
    have hne : (6561 * q + 859) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 1145) + 1) = 2 + ν₂ (6561 * q + 859) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 859) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 859) (2 ^ ν₂ (6561 * q + 859)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1135 (q : ℕ) : step (8192 * q + 1135) = 12288 * q + 1703 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1135) + 1 = 2 ^ 1 * (12288 * q + 1703) := by ring
  have h_odd : (12288 * q + 1703) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1135) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1703) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1703) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1703) (by positivity)]

theorem step2_m8192_1135 (q : ℕ) : step (step (8192 * q + 1135)) = 18432 * q + 2555 := by
  rw [step_m8192_1135 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1703) + 1 = 2 ^ 1 * (18432 * q + 2555) := by ring
  have h_odd : (18432 * q + 2555) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1703) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 2555) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 2555) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 2555) (by positivity)]

theorem step3_m8192_1135 (q : ℕ) : step (step (step (8192 * q + 1135))) = 27648 * q + 3833 := by
  rw [step2_m8192_1135 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 2555) + 1 = 2 ^ 1 * (27648 * q + 3833) := by ring
  have h_odd : (27648 * q + 3833) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 2555) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 3833) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 3833) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 3833) (by positivity)]

theorem step4_m8192_1135 (q : ℕ) : step (step (step (step (8192 * q + 1135)))) = 20736 * q + 2875 := by
  rw [step3_m8192_1135 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 3833) + 1 = 2 ^ 2 * (20736 * q + 2875) := by ring
  have h_odd : (20736 * q + 2875) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 3833) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 2875) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 2875) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 2875) (by positivity)]

theorem step5_m8192_1135 (q : ℕ) : step (step (step (step (step (8192 * q + 1135))))) = 31104 * q + 4313 := by
  rw [step4_m8192_1135 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 2875) + 1 = 2 ^ 1 * (31104 * q + 4313) := by ring
  have h_odd : (31104 * q + 4313) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 2875) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 4313) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 4313) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 4313) (by positivity)]

theorem step6_m8192_1135 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1135)))))) = 23328 * q + 3235 := by
  rw [step5_m8192_1135 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 4313) + 1 = 2 ^ 2 * (23328 * q + 3235) := by ring
  have h_odd : (23328 * q + 3235) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 4313) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 3235) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 3235) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 3235) (by positivity)]

theorem step7_m8192_1135 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1135))))))) = 34992 * q + 4853 := by
  rw [step6_m8192_1135 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 3235) + 1 = 2 ^ 1 * (34992 * q + 4853) := by ring
  have h_odd : (34992 * q + 4853) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 3235) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 4853) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 4853) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 4853) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1135 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1135 (q : ℕ) (hq : 8192 * q + 1135 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1135)))))))) < 8192 * q + 1135 := by
  rw [step7_m8192_1135 q]
  have h_bound : step (34992 * q + 4853) ≤ 6561 * q + 910 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 4853) + 1 = 2 ^ 4 * (6561 * q + 910) := by ring
    have hne : (6561 * q + 910) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 4853) + 1) = 4 + ν₂ (6561 * q + 910) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 910) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 910) (2 ^ ν₂ (6561 * q + 910)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1191 (q : ℕ) : step (8192 * q + 1191) = 12288 * q + 1787 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1191) + 1 = 2 ^ 1 * (12288 * q + 1787) := by ring
  have h_odd : (12288 * q + 1787) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1191) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1787) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1787) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1787) (by positivity)]

theorem step2_m8192_1191 (q : ℕ) : step (step (8192 * q + 1191)) = 18432 * q + 2681 := by
  rw [step_m8192_1191 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1787) + 1 = 2 ^ 1 * (18432 * q + 2681) := by ring
  have h_odd : (18432 * q + 2681) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1787) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 2681) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 2681) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 2681) (by positivity)]

theorem step3_m8192_1191 (q : ℕ) : step (step (step (8192 * q + 1191))) = 13824 * q + 2011 := by
  rw [step2_m8192_1191 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 2681) + 1 = 2 ^ 2 * (13824 * q + 2011) := by ring
  have h_odd : (13824 * q + 2011) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 2681) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 2011) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 2011) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 2011) (by positivity)]

theorem step4_m8192_1191 (q : ℕ) : step (step (step (step (8192 * q + 1191)))) = 20736 * q + 3017 := by
  rw [step3_m8192_1191 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 2011) + 1 = 2 ^ 1 * (20736 * q + 3017) := by ring
  have h_odd : (20736 * q + 3017) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 2011) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 3017) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 3017) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 3017) (by positivity)]

theorem step5_m8192_1191 (q : ℕ) : step (step (step (step (step (8192 * q + 1191))))) = 15552 * q + 2263 := by
  rw [step4_m8192_1191 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 3017) + 1 = 2 ^ 2 * (15552 * q + 2263) := by ring
  have h_odd : (15552 * q + 2263) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 3017) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 2263) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 2263) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 2263) (by positivity)]

theorem step6_m8192_1191 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1191)))))) = 23328 * q + 3395 := by
  rw [step5_m8192_1191 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 2263) + 1 = 2 ^ 1 * (23328 * q + 3395) := by ring
  have h_odd : (23328 * q + 3395) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 2263) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 3395) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 3395) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 3395) (by positivity)]

theorem step7_m8192_1191 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1191))))))) = 34992 * q + 5093 := by
  rw [step6_m8192_1191 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 3395) + 1 = 2 ^ 1 * (34992 * q + 5093) := by ring
  have h_odd : (34992 * q + 5093) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 3395) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 5093) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 5093) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 5093) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1191 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1191 (q : ℕ) (hq : 8192 * q + 1191 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1191)))))))) < 8192 * q + 1191 := by
  rw [step7_m8192_1191 q]
  have h_bound : step (34992 * q + 5093) ≤ 6561 * q + 955 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 5093) + 1 = 2 ^ 4 * (6561 * q + 955) := by ring
    have hne : (6561 * q + 955) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 5093) + 1) = 4 + ν₂ (6561 * q + 955) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 955) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 955) (2 ^ ν₂ (6561 * q + 955)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1215 (q : ℕ) : step (8192 * q + 1215) = 12288 * q + 1823 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1215) + 1 = 2 ^ 1 * (12288 * q + 1823) := by ring
  have h_odd : (12288 * q + 1823) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1215) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1823) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1823) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1823) (by positivity)]

theorem step2_m8192_1215 (q : ℕ) : step (step (8192 * q + 1215)) = 18432 * q + 2735 := by
  rw [step_m8192_1215 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1823) + 1 = 2 ^ 1 * (18432 * q + 2735) := by ring
  have h_odd : (18432 * q + 2735) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1823) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 2735) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 2735) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 2735) (by positivity)]

theorem step3_m8192_1215 (q : ℕ) : step (step (step (8192 * q + 1215))) = 27648 * q + 4103 := by
  rw [step2_m8192_1215 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 2735) + 1 = 2 ^ 1 * (27648 * q + 4103) := by ring
  have h_odd : (27648 * q + 4103) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 2735) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 4103) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 4103) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 4103) (by positivity)]

theorem step4_m8192_1215 (q : ℕ) : step (step (step (step (8192 * q + 1215)))) = 41472 * q + 6155 := by
  rw [step3_m8192_1215 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 4103) + 1 = 2 ^ 1 * (41472 * q + 6155) := by ring
  have h_odd : (41472 * q + 6155) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 4103) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 6155) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 6155) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 6155) (by positivity)]

theorem step5_m8192_1215 (q : ℕ) : step (step (step (step (step (8192 * q + 1215))))) = 62208 * q + 9233 := by
  rw [step4_m8192_1215 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 6155) + 1 = 2 ^ 1 * (62208 * q + 9233) := by ring
  have h_odd : (62208 * q + 9233) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 6155) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 9233) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 9233) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 9233) (by positivity)]

theorem step6_m8192_1215 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1215)))))) = 46656 * q + 6925 := by
  rw [step5_m8192_1215 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 9233) + 1 = 2 ^ 2 * (46656 * q + 6925) := by ring
  have h_odd : (46656 * q + 6925) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 9233) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (46656 * q + 6925) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (46656 * q + 6925) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 6925) (by positivity)]

theorem step7_m8192_1215 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1215))))))) = 17496 * q + 2597 := by
  rw [step6_m8192_1215 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 6925) + 1 = 2 ^ 3 * (17496 * q + 2597) := by ring
  have h_odd : (17496 * q + 2597) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 6925) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (17496 * q + 2597) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (17496 * q + 2597) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 2597) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1215 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1215 (q : ℕ) (hq : 8192 * q + 1215 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1215)))))))) < 8192 * q + 1215 := by
  rw [step7_m8192_1215 q]
  have h_bound : step (17496 * q + 2597) ≤ 6561 * q + 974 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 2597) + 1 = 2 ^ 3 * (6561 * q + 974) := by ring
    have hne : (6561 * q + 974) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 2597) + 1) = 3 + ν₂ (6561 * q + 974) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 974) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 974) (2 ^ ν₂ (6561 * q + 974)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1247 (q : ℕ) : step (8192 * q + 1247) = 12288 * q + 1871 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1247) + 1 = 2 ^ 1 * (12288 * q + 1871) := by ring
  have h_odd : (12288 * q + 1871) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1247) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1871) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1871) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1871) (by positivity)]

theorem step2_m8192_1247 (q : ℕ) : step (step (8192 * q + 1247)) = 18432 * q + 2807 := by
  rw [step_m8192_1247 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1871) + 1 = 2 ^ 1 * (18432 * q + 2807) := by ring
  have h_odd : (18432 * q + 2807) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1871) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 2807) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 2807) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 2807) (by positivity)]

theorem step3_m8192_1247 (q : ℕ) : step (step (step (8192 * q + 1247))) = 27648 * q + 4211 := by
  rw [step2_m8192_1247 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 2807) + 1 = 2 ^ 1 * (27648 * q + 4211) := by ring
  have h_odd : (27648 * q + 4211) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 2807) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 4211) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 4211) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 4211) (by positivity)]

theorem step4_m8192_1247 (q : ℕ) : step (step (step (step (8192 * q + 1247)))) = 41472 * q + 6317 := by
  rw [step3_m8192_1247 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 4211) + 1 = 2 ^ 1 * (41472 * q + 6317) := by ring
  have h_odd : (41472 * q + 6317) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 4211) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 6317) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 6317) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 6317) (by positivity)]

theorem step5_m8192_1247 (q : ℕ) : step (step (step (step (step (8192 * q + 1247))))) = 15552 * q + 2369 := by
  rw [step4_m8192_1247 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 6317) + 1 = 2 ^ 3 * (15552 * q + 2369) := by ring
  have h_odd : (15552 * q + 2369) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 6317) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (15552 * q + 2369) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (15552 * q + 2369) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 2369) (by positivity)]

theorem step6_m8192_1247 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1247)))))) = 11664 * q + 1777 := by
  rw [step5_m8192_1247 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 2369) + 1 = 2 ^ 2 * (11664 * q + 1777) := by ring
  have h_odd : (11664 * q + 1777) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 2369) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 1777) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 1777) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 1777) (by positivity)]

theorem step7_m8192_1247 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1247))))))) = 8748 * q + 1333 := by
  rw [step6_m8192_1247 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 1777) + 1 = 2 ^ 2 * (8748 * q + 1333) := by ring
  have h_odd : (8748 * q + 1333) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 1777) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 1333) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 1333) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 1333) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1247 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1247 (q : ℕ) (hq : 8192 * q + 1247 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1247)))))))) < 8192 * q + 1247 := by
  rw [step7_m8192_1247 q]
  have h_bound : step (8748 * q + 1333) ≤ 6561 * q + 1000 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 1333) + 1 = 2 ^ 2 * (6561 * q + 1000) := by ring
    have hne : (6561 * q + 1000) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 1333) + 1) = 2 + ν₂ (6561 * q + 1000) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 1000) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1000) (2 ^ ν₂ (6561 * q + 1000)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1327 (q : ℕ) : step (8192 * q + 1327) = 12288 * q + 1991 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1327) + 1 = 2 ^ 1 * (12288 * q + 1991) := by ring
  have h_odd : (12288 * q + 1991) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1327) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 1991) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 1991) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 1991) (by positivity)]

theorem step2_m8192_1327 (q : ℕ) : step (step (8192 * q + 1327)) = 18432 * q + 2987 := by
  rw [step_m8192_1327 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 1991) + 1 = 2 ^ 1 * (18432 * q + 2987) := by ring
  have h_odd : (18432 * q + 2987) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 1991) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 2987) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 2987) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 2987) (by positivity)]

theorem step3_m8192_1327 (q : ℕ) : step (step (step (8192 * q + 1327))) = 27648 * q + 4481 := by
  rw [step2_m8192_1327 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 2987) + 1 = 2 ^ 1 * (27648 * q + 4481) := by ring
  have h_odd : (27648 * q + 4481) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 2987) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 4481) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 4481) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 4481) (by positivity)]

theorem step4_m8192_1327 (q : ℕ) : step (step (step (step (8192 * q + 1327)))) = 20736 * q + 3361 := by
  rw [step3_m8192_1327 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 4481) + 1 = 2 ^ 2 * (20736 * q + 3361) := by ring
  have h_odd : (20736 * q + 3361) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 4481) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 3361) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 3361) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 3361) (by positivity)]

theorem step5_m8192_1327 (q : ℕ) : step (step (step (step (step (8192 * q + 1327))))) = 15552 * q + 2521 := by
  rw [step4_m8192_1327 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 3361) + 1 = 2 ^ 2 * (15552 * q + 2521) := by ring
  have h_odd : (15552 * q + 2521) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 3361) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 2521) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 2521) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 2521) (by positivity)]

theorem step6_m8192_1327 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1327)))))) = 11664 * q + 1891 := by
  rw [step5_m8192_1327 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 2521) + 1 = 2 ^ 2 * (11664 * q + 1891) := by ring
  have h_odd : (11664 * q + 1891) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 2521) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 1891) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 1891) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 1891) (by positivity)]

theorem step7_m8192_1327 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1327))))))) = 17496 * q + 2837 := by
  rw [step6_m8192_1327 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 1891) + 1 = 2 ^ 1 * (17496 * q + 2837) := by ring
  have h_odd : (17496 * q + 2837) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 1891) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 2837) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 2837) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 2837) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1327 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1327 (q : ℕ) (hq : 8192 * q + 1327 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1327)))))))) < 8192 * q + 1327 := by
  rw [step7_m8192_1327 q]
  have h_bound : step (17496 * q + 2837) ≤ 6561 * q + 1064 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 2837) + 1 = 2 ^ 3 * (6561 * q + 1064) := by ring
    have hne : (6561 * q + 1064) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 2837) + 1) = 3 + ν₂ (6561 * q + 1064) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 1064) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1064) (2 ^ ν₂ (6561 * q + 1064)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1449 (q : ℕ) : step (8192 * q + 1449) = 6144 * q + 1087 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1449) + 1 = 2 ^ 2 * (6144 * q + 1087) := by ring
  have h_odd : (6144 * q + 1087) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1449) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 1087) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 1087) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 1087) (by positivity)]

theorem step2_m8192_1449 (q : ℕ) : step (step (8192 * q + 1449)) = 9216 * q + 1631 := by
  rw [step_m8192_1449 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 1087) + 1 = 2 ^ 1 * (9216 * q + 1631) := by ring
  have h_odd : (9216 * q + 1631) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 1087) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 1631) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 1631) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 1631) (by positivity)]

theorem step3_m8192_1449 (q : ℕ) : step (step (step (8192 * q + 1449))) = 13824 * q + 2447 := by
  rw [step2_m8192_1449 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 1631) + 1 = 2 ^ 1 * (13824 * q + 2447) := by ring
  have h_odd : (13824 * q + 2447) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 1631) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 2447) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 2447) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 2447) (by positivity)]

theorem step4_m8192_1449 (q : ℕ) : step (step (step (step (8192 * q + 1449)))) = 20736 * q + 3671 := by
  rw [step3_m8192_1449 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 2447) + 1 = 2 ^ 1 * (20736 * q + 3671) := by ring
  have h_odd : (20736 * q + 3671) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 2447) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 3671) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 3671) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 3671) (by positivity)]

theorem step5_m8192_1449 (q : ℕ) : step (step (step (step (step (8192 * q + 1449))))) = 31104 * q + 5507 := by
  rw [step4_m8192_1449 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 3671) + 1 = 2 ^ 1 * (31104 * q + 5507) := by ring
  have h_odd : (31104 * q + 5507) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 3671) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 5507) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 5507) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 5507) (by positivity)]

theorem step6_m8192_1449 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1449)))))) = 46656 * q + 8261 := by
  rw [step5_m8192_1449 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 5507) + 1 = 2 ^ 1 * (46656 * q + 8261) := by ring
  have h_odd : (46656 * q + 8261) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 5507) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 8261) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 8261) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 8261) (by positivity)]

theorem step7_m8192_1449 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1449))))))) = 8748 * q + 1549 := by
  rw [step6_m8192_1449 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 8261) + 1 = 2 ^ 4 * (8748 * q + 1549) := by ring
  have h_odd : (8748 * q + 1549) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 8261) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (8748 * q + 1549) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (8748 * q + 1549) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 1549) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1449 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1449 (q : ℕ) (hq : 8192 * q + 1449 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1449)))))))) < 8192 * q + 1449 := by
  rw [step7_m8192_1449 q]
  have h_bound : step (8748 * q + 1549) ≤ 6561 * q + 1162 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 1549) + 1 = 2 ^ 2 * (6561 * q + 1162) := by ring
    have hne : (6561 * q + 1162) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 1549) + 1) = 2 + ν₂ (6561 * q + 1162) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 1162) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1162) (2 ^ ν₂ (6561 * q + 1162)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1563 (q : ℕ) : step (8192 * q + 1563) = 12288 * q + 2345 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1563) + 1 = 2 ^ 1 * (12288 * q + 2345) := by ring
  have h_odd : (12288 * q + 2345) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1563) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 2345) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 2345) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 2345) (by positivity)]

theorem step2_m8192_1563 (q : ℕ) : step (step (8192 * q + 1563)) = 9216 * q + 1759 := by
  rw [step_m8192_1563 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 2345) + 1 = 2 ^ 2 * (9216 * q + 1759) := by ring
  have h_odd : (9216 * q + 1759) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 2345) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 1759) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 1759) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 1759) (by positivity)]

theorem step3_m8192_1563 (q : ℕ) : step (step (step (8192 * q + 1563))) = 13824 * q + 2639 := by
  rw [step2_m8192_1563 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 1759) + 1 = 2 ^ 1 * (13824 * q + 2639) := by ring
  have h_odd : (13824 * q + 2639) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 1759) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 2639) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 2639) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 2639) (by positivity)]

theorem step4_m8192_1563 (q : ℕ) : step (step (step (step (8192 * q + 1563)))) = 20736 * q + 3959 := by
  rw [step3_m8192_1563 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 2639) + 1 = 2 ^ 1 * (20736 * q + 3959) := by ring
  have h_odd : (20736 * q + 3959) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 2639) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 3959) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 3959) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 3959) (by positivity)]

theorem step5_m8192_1563 (q : ℕ) : step (step (step (step (step (8192 * q + 1563))))) = 31104 * q + 5939 := by
  rw [step4_m8192_1563 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 3959) + 1 = 2 ^ 1 * (31104 * q + 5939) := by ring
  have h_odd : (31104 * q + 5939) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 3959) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 5939) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 5939) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 5939) (by positivity)]

theorem step6_m8192_1563 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1563)))))) = 46656 * q + 8909 := by
  rw [step5_m8192_1563 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 5939) + 1 = 2 ^ 1 * (46656 * q + 8909) := by ring
  have h_odd : (46656 * q + 8909) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 5939) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 8909) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 8909) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 8909) (by positivity)]

theorem step7_m8192_1563 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1563))))))) = 17496 * q + 3341 := by
  rw [step6_m8192_1563 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 8909) + 1 = 2 ^ 3 * (17496 * q + 3341) := by ring
  have h_odd : (17496 * q + 3341) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 8909) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (17496 * q + 3341) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (17496 * q + 3341) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 3341) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1563 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1563 (q : ℕ) (hq : 8192 * q + 1563 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1563)))))))) < 8192 * q + 1563 := by
  rw [step7_m8192_1563 q]
  have h_bound : step (17496 * q + 3341) ≤ 6561 * q + 1253 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 3341) + 1 = 2 ^ 3 * (6561 * q + 1253) := by ring
    have hne : (6561 * q + 1253) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 3341) + 1) = 3 + ν₂ (6561 * q + 1253) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 1253) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1253) (2 ^ ν₂ (6561 * q + 1253)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1567 (q : ℕ) : step (8192 * q + 1567) = 12288 * q + 2351 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1567) + 1 = 2 ^ 1 * (12288 * q + 2351) := by ring
  have h_odd : (12288 * q + 2351) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1567) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 2351) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 2351) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 2351) (by positivity)]

theorem step2_m8192_1567 (q : ℕ) : step (step (8192 * q + 1567)) = 18432 * q + 3527 := by
  rw [step_m8192_1567 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 2351) + 1 = 2 ^ 1 * (18432 * q + 3527) := by ring
  have h_odd : (18432 * q + 3527) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 2351) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 3527) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 3527) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 3527) (by positivity)]

theorem step3_m8192_1567 (q : ℕ) : step (step (step (8192 * q + 1567))) = 27648 * q + 5291 := by
  rw [step2_m8192_1567 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 3527) + 1 = 2 ^ 1 * (27648 * q + 5291) := by ring
  have h_odd : (27648 * q + 5291) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 3527) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 5291) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 5291) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 5291) (by positivity)]

theorem step4_m8192_1567 (q : ℕ) : step (step (step (step (8192 * q + 1567)))) = 41472 * q + 7937 := by
  rw [step3_m8192_1567 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 5291) + 1 = 2 ^ 1 * (41472 * q + 7937) := by ring
  have h_odd : (41472 * q + 7937) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 5291) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 7937) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 7937) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 7937) (by positivity)]

theorem step5_m8192_1567 (q : ℕ) : step (step (step (step (step (8192 * q + 1567))))) = 31104 * q + 5953 := by
  rw [step4_m8192_1567 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 7937) + 1 = 2 ^ 2 * (31104 * q + 5953) := by ring
  have h_odd : (31104 * q + 5953) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 7937) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 5953) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 5953) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 5953) (by positivity)]

theorem step6_m8192_1567 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1567)))))) = 23328 * q + 4465 := by
  rw [step5_m8192_1567 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 5953) + 1 = 2 ^ 2 * (23328 * q + 4465) := by ring
  have h_odd : (23328 * q + 4465) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 5953) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 4465) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 4465) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 4465) (by positivity)]

theorem step7_m8192_1567 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1567))))))) = 17496 * q + 3349 := by
  rw [step6_m8192_1567 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 4465) + 1 = 2 ^ 2 * (17496 * q + 3349) := by ring
  have h_odd : (17496 * q + 3349) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 4465) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 3349) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 3349) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 3349) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1567 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1567 (q : ℕ) (hq : 8192 * q + 1567 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1567)))))))) < 8192 * q + 1567 := by
  rw [step7_m8192_1567 q]
  have h_bound : step (17496 * q + 3349) ≤ 6561 * q + 1256 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 3349) + 1 = 2 ^ 3 * (6561 * q + 1256) := by ring
    have hne : (6561 * q + 1256) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 3349) + 1) = 3 + ν₂ (6561 * q + 1256) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 1256) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1256) (2 ^ ν₂ (6561 * q + 1256)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1727 (q : ℕ) : step (8192 * q + 1727) = 12288 * q + 2591 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1727) + 1 = 2 ^ 1 * (12288 * q + 2591) := by ring
  have h_odd : (12288 * q + 2591) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1727) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 2591) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 2591) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 2591) (by positivity)]

theorem step2_m8192_1727 (q : ℕ) : step (step (8192 * q + 1727)) = 18432 * q + 3887 := by
  rw [step_m8192_1727 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 2591) + 1 = 2 ^ 1 * (18432 * q + 3887) := by ring
  have h_odd : (18432 * q + 3887) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 2591) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 3887) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 3887) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 3887) (by positivity)]

theorem step3_m8192_1727 (q : ℕ) : step (step (step (8192 * q + 1727))) = 27648 * q + 5831 := by
  rw [step2_m8192_1727 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 3887) + 1 = 2 ^ 1 * (27648 * q + 5831) := by ring
  have h_odd : (27648 * q + 5831) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 3887) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 5831) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 5831) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 5831) (by positivity)]

theorem step4_m8192_1727 (q : ℕ) : step (step (step (step (8192 * q + 1727)))) = 41472 * q + 8747 := by
  rw [step3_m8192_1727 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 5831) + 1 = 2 ^ 1 * (41472 * q + 8747) := by ring
  have h_odd : (41472 * q + 8747) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 5831) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 8747) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 8747) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 8747) (by positivity)]

theorem step5_m8192_1727 (q : ℕ) : step (step (step (step (step (8192 * q + 1727))))) = 62208 * q + 13121 := by
  rw [step4_m8192_1727 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 8747) + 1 = 2 ^ 1 * (62208 * q + 13121) := by ring
  have h_odd : (62208 * q + 13121) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 8747) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 13121) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 13121) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 13121) (by positivity)]

theorem step6_m8192_1727 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1727)))))) = 46656 * q + 9841 := by
  rw [step5_m8192_1727 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 13121) + 1 = 2 ^ 2 * (46656 * q + 9841) := by ring
  have h_odd : (46656 * q + 9841) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 13121) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (46656 * q + 9841) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (46656 * q + 9841) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 9841) (by positivity)]

theorem step7_m8192_1727 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1727))))))) = 34992 * q + 7381 := by
  rw [step6_m8192_1727 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 9841) + 1 = 2 ^ 2 * (34992 * q + 7381) := by ring
  have h_odd : (34992 * q + 7381) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 9841) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (34992 * q + 7381) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (34992 * q + 7381) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 7381) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1727 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1727 (q : ℕ) (hq : 8192 * q + 1727 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1727)))))))) < 8192 * q + 1727 := by
  rw [step7_m8192_1727 q]
  have h_bound : step (34992 * q + 7381) ≤ 6561 * q + 1384 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 7381) + 1 = 2 ^ 4 * (6561 * q + 1384) := by ring
    have hne : (6561 * q + 1384) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 7381) + 1) = 4 + ν₂ (6561 * q + 1384) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 1384) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1384) (2 ^ ν₂ (6561 * q + 1384)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_1983 (q : ℕ) : step (8192 * q + 1983) = 12288 * q + 2975 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 1983) + 1 = 2 ^ 1 * (12288 * q + 2975) := by ring
  have h_odd : (12288 * q + 2975) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 1983) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 2975) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 2975) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 2975) (by positivity)]

theorem step2_m8192_1983 (q : ℕ) : step (step (8192 * q + 1983)) = 18432 * q + 4463 := by
  rw [step_m8192_1983 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 2975) + 1 = 2 ^ 1 * (18432 * q + 4463) := by ring
  have h_odd : (18432 * q + 4463) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 2975) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 4463) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 4463) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 4463) (by positivity)]

theorem step3_m8192_1983 (q : ℕ) : step (step (step (8192 * q + 1983))) = 27648 * q + 6695 := by
  rw [step2_m8192_1983 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 4463) + 1 = 2 ^ 1 * (27648 * q + 6695) := by ring
  have h_odd : (27648 * q + 6695) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 4463) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 6695) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 6695) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 6695) (by positivity)]

theorem step4_m8192_1983 (q : ℕ) : step (step (step (step (8192 * q + 1983)))) = 41472 * q + 10043 := by
  rw [step3_m8192_1983 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 6695) + 1 = 2 ^ 1 * (41472 * q + 10043) := by ring
  have h_odd : (41472 * q + 10043) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 6695) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 10043) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 10043) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 10043) (by positivity)]

theorem step5_m8192_1983 (q : ℕ) : step (step (step (step (step (8192 * q + 1983))))) = 62208 * q + 15065 := by
  rw [step4_m8192_1983 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 10043) + 1 = 2 ^ 1 * (62208 * q + 15065) := by ring
  have h_odd : (62208 * q + 15065) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 10043) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 15065) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 15065) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 15065) (by positivity)]

theorem step6_m8192_1983 (q : ℕ) : step (step (step (step (step (step (8192 * q + 1983)))))) = 46656 * q + 11299 := by
  rw [step5_m8192_1983 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 15065) + 1 = 2 ^ 2 * (46656 * q + 11299) := by ring
  have h_odd : (46656 * q + 11299) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 15065) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (46656 * q + 11299) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (46656 * q + 11299) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 11299) (by positivity)]

theorem step7_m8192_1983 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 1983))))))) = 69984 * q + 16949 := by
  rw [step6_m8192_1983 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 11299) + 1 = 2 ^ 1 * (69984 * q + 16949) := by ring
  have h_odd : (69984 * q + 16949) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 11299) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (69984 * q + 16949) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (69984 * q + 16949) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (69984 * q + 16949) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 1983 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_1983 (q : ℕ) (hq : 8192 * q + 1983 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 1983)))))))) < 8192 * q + 1983 := by
  rw [step7_m8192_1983 q]
  have h_bound : step (69984 * q + 16949) ≤ 6561 * q + 1589 := by
    unfold step
    have h3n1 : 3 * (69984 * q + 16949) + 1 = 2 ^ 5 * (6561 * q + 1589) := by ring
    have hne : (6561 * q + 1589) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (69984 * q + 16949) + 1) = 5 + ν₂ (6561 * q + 1589) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (6561 * q + 1589) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1589) (2 ^ ν₂ (6561 * q + 1589)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2015 (q : ℕ) : step (8192 * q + 2015) = 12288 * q + 3023 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2015) + 1 = 2 ^ 1 * (12288 * q + 3023) := by ring
  have h_odd : (12288 * q + 3023) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2015) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3023) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3023) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3023) (by positivity)]

theorem step2_m8192_2015 (q : ℕ) : step (step (8192 * q + 2015)) = 18432 * q + 4535 := by
  rw [step_m8192_2015 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3023) + 1 = 2 ^ 1 * (18432 * q + 4535) := by ring
  have h_odd : (18432 * q + 4535) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3023) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 4535) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 4535) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 4535) (by positivity)]

theorem step3_m8192_2015 (q : ℕ) : step (step (step (8192 * q + 2015))) = 27648 * q + 6803 := by
  rw [step2_m8192_2015 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 4535) + 1 = 2 ^ 1 * (27648 * q + 6803) := by ring
  have h_odd : (27648 * q + 6803) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 4535) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 6803) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 6803) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 6803) (by positivity)]

theorem step4_m8192_2015 (q : ℕ) : step (step (step (step (8192 * q + 2015)))) = 41472 * q + 10205 := by
  rw [step3_m8192_2015 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 6803) + 1 = 2 ^ 1 * (41472 * q + 10205) := by ring
  have h_odd : (41472 * q + 10205) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 6803) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 10205) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 10205) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 10205) (by positivity)]

theorem step5_m8192_2015 (q : ℕ) : step (step (step (step (step (8192 * q + 2015))))) = 15552 * q + 3827 := by
  rw [step4_m8192_2015 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 10205) + 1 = 2 ^ 3 * (15552 * q + 3827) := by ring
  have h_odd : (15552 * q + 3827) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 10205) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (15552 * q + 3827) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (15552 * q + 3827) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 3827) (by positivity)]

theorem step6_m8192_2015 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2015)))))) = 23328 * q + 5741 := by
  rw [step5_m8192_2015 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 3827) + 1 = 2 ^ 1 * (23328 * q + 5741) := by ring
  have h_odd : (23328 * q + 5741) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 3827) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 5741) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 5741) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 5741) (by positivity)]

theorem step7_m8192_2015 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2015))))))) = 8748 * q + 2153 := by
  rw [step6_m8192_2015 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 5741) + 1 = 2 ^ 3 * (8748 * q + 2153) := by ring
  have h_odd : (8748 * q + 2153) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 5741) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 2153) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 2153) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 2153) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2015 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2015 (q : ℕ) (hq : 8192 * q + 2015 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2015)))))))) < 8192 * q + 2015 := by
  rw [step7_m8192_2015 q]
  have h_bound : step (8748 * q + 2153) ≤ 6561 * q + 1615 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 2153) + 1 = 2 ^ 2 * (6561 * q + 1615) := by ring
    have hne : (6561 * q + 1615) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 2153) + 1) = 2 + ν₂ (6561 * q + 1615) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 1615) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1615) (2 ^ ν₂ (6561 * q + 1615)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2075 (q : ℕ) : step (8192 * q + 2075) = 12288 * q + 3113 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2075) + 1 = 2 ^ 1 * (12288 * q + 3113) := by ring
  have h_odd : (12288 * q + 3113) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2075) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3113) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3113) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3113) (by positivity)]

theorem step2_m8192_2075 (q : ℕ) : step (step (8192 * q + 2075)) = 9216 * q + 2335 := by
  rw [step_m8192_2075 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3113) + 1 = 2 ^ 2 * (9216 * q + 2335) := by ring
  have h_odd : (9216 * q + 2335) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3113) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 2335) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 2335) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 2335) (by positivity)]

theorem step3_m8192_2075 (q : ℕ) : step (step (step (8192 * q + 2075))) = 13824 * q + 3503 := by
  rw [step2_m8192_2075 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 2335) + 1 = 2 ^ 1 * (13824 * q + 3503) := by ring
  have h_odd : (13824 * q + 3503) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 2335) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 3503) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 3503) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 3503) (by positivity)]

theorem step4_m8192_2075 (q : ℕ) : step (step (step (step (8192 * q + 2075)))) = 20736 * q + 5255 := by
  rw [step3_m8192_2075 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 3503) + 1 = 2 ^ 1 * (20736 * q + 5255) := by ring
  have h_odd : (20736 * q + 5255) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 3503) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 5255) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 5255) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 5255) (by positivity)]

theorem step5_m8192_2075 (q : ℕ) : step (step (step (step (step (8192 * q + 2075))))) = 31104 * q + 7883 := by
  rw [step4_m8192_2075 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 5255) + 1 = 2 ^ 1 * (31104 * q + 7883) := by ring
  have h_odd : (31104 * q + 7883) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 5255) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 7883) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 7883) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 7883) (by positivity)]

theorem step6_m8192_2075 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2075)))))) = 46656 * q + 11825 := by
  rw [step5_m8192_2075 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 7883) + 1 = 2 ^ 1 * (46656 * q + 11825) := by ring
  have h_odd : (46656 * q + 11825) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 7883) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 11825) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 11825) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 11825) (by positivity)]

theorem step7_m8192_2075 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2075))))))) = 34992 * q + 8869 := by
  rw [step6_m8192_2075 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 11825) + 1 = 2 ^ 2 * (34992 * q + 8869) := by ring
  have h_odd : (34992 * q + 8869) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 11825) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (34992 * q + 8869) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (34992 * q + 8869) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 8869) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2075 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2075 (q : ℕ) (hq : 8192 * q + 2075 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2075)))))))) < 8192 * q + 2075 := by
  rw [step7_m8192_2075 q]
  have h_bound : step (34992 * q + 8869) ≤ 6561 * q + 1663 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 8869) + 1 = 2 ^ 4 * (6561 * q + 1663) := by ring
    have hne : (6561 * q + 1663) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 8869) + 1) = 4 + ν₂ (6561 * q + 1663) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 1663) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1663) (2 ^ ν₂ (6561 * q + 1663)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2079 (q : ℕ) : step (8192 * q + 2079) = 12288 * q + 3119 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2079) + 1 = 2 ^ 1 * (12288 * q + 3119) := by ring
  have h_odd : (12288 * q + 3119) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2079) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3119) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3119) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3119) (by positivity)]

theorem step2_m8192_2079 (q : ℕ) : step (step (8192 * q + 2079)) = 18432 * q + 4679 := by
  rw [step_m8192_2079 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3119) + 1 = 2 ^ 1 * (18432 * q + 4679) := by ring
  have h_odd : (18432 * q + 4679) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3119) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 4679) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 4679) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 4679) (by positivity)]

theorem step3_m8192_2079 (q : ℕ) : step (step (step (8192 * q + 2079))) = 27648 * q + 7019 := by
  rw [step2_m8192_2079 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 4679) + 1 = 2 ^ 1 * (27648 * q + 7019) := by ring
  have h_odd : (27648 * q + 7019) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 4679) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 7019) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 7019) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 7019) (by positivity)]

theorem step4_m8192_2079 (q : ℕ) : step (step (step (step (8192 * q + 2079)))) = 41472 * q + 10529 := by
  rw [step3_m8192_2079 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 7019) + 1 = 2 ^ 1 * (41472 * q + 10529) := by ring
  have h_odd : (41472 * q + 10529) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 7019) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 10529) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 10529) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 10529) (by positivity)]

theorem step5_m8192_2079 (q : ℕ) : step (step (step (step (step (8192 * q + 2079))))) = 31104 * q + 7897 := by
  rw [step4_m8192_2079 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 10529) + 1 = 2 ^ 2 * (31104 * q + 7897) := by ring
  have h_odd : (31104 * q + 7897) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 10529) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 7897) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 7897) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 7897) (by positivity)]

theorem step6_m8192_2079 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2079)))))) = 23328 * q + 5923 := by
  rw [step5_m8192_2079 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 7897) + 1 = 2 ^ 2 * (23328 * q + 5923) := by ring
  have h_odd : (23328 * q + 5923) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 7897) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 5923) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 5923) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 5923) (by positivity)]

theorem step7_m8192_2079 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2079))))))) = 34992 * q + 8885 := by
  rw [step6_m8192_2079 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 5923) + 1 = 2 ^ 1 * (34992 * q + 8885) := by ring
  have h_odd : (34992 * q + 8885) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 5923) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 8885) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 8885) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 8885) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2079 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2079 (q : ℕ) (hq : 8192 * q + 2079 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2079)))))))) < 8192 * q + 2079 := by
  rw [step7_m8192_2079 q]
  have h_bound : step (34992 * q + 8885) ≤ 6561 * q + 1666 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 8885) + 1 = 2 ^ 4 * (6561 * q + 1666) := by ring
    have hne : (6561 * q + 1666) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 8885) + 1) = 4 + ν₂ (6561 * q + 1666) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 1666) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1666) (2 ^ ν₂ (6561 * q + 1666)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2095 (q : ℕ) : step (8192 * q + 2095) = 12288 * q + 3143 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2095) + 1 = 2 ^ 1 * (12288 * q + 3143) := by ring
  have h_odd : (12288 * q + 3143) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2095) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3143) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3143) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3143) (by positivity)]

theorem step2_m8192_2095 (q : ℕ) : step (step (8192 * q + 2095)) = 18432 * q + 4715 := by
  rw [step_m8192_2095 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3143) + 1 = 2 ^ 1 * (18432 * q + 4715) := by ring
  have h_odd : (18432 * q + 4715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3143) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 4715) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 4715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 4715) (by positivity)]

theorem step3_m8192_2095 (q : ℕ) : step (step (step (8192 * q + 2095))) = 27648 * q + 7073 := by
  rw [step2_m8192_2095 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 4715) + 1 = 2 ^ 1 * (27648 * q + 7073) := by ring
  have h_odd : (27648 * q + 7073) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 4715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 7073) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 7073) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 7073) (by positivity)]

theorem step4_m8192_2095 (q : ℕ) : step (step (step (step (8192 * q + 2095)))) = 20736 * q + 5305 := by
  rw [step3_m8192_2095 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 7073) + 1 = 2 ^ 2 * (20736 * q + 5305) := by ring
  have h_odd : (20736 * q + 5305) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 7073) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 5305) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 5305) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 5305) (by positivity)]

theorem step5_m8192_2095 (q : ℕ) : step (step (step (step (step (8192 * q + 2095))))) = 15552 * q + 3979 := by
  rw [step4_m8192_2095 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 5305) + 1 = 2 ^ 2 * (15552 * q + 3979) := by ring
  have h_odd : (15552 * q + 3979) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 5305) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 3979) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 3979) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 3979) (by positivity)]

theorem step6_m8192_2095 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2095)))))) = 23328 * q + 5969 := by
  rw [step5_m8192_2095 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 3979) + 1 = 2 ^ 1 * (23328 * q + 5969) := by ring
  have h_odd : (23328 * q + 5969) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 3979) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 5969) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 5969) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 5969) (by positivity)]

theorem step7_m8192_2095 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2095))))))) = 17496 * q + 4477 := by
  rw [step6_m8192_2095 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 5969) + 1 = 2 ^ 2 * (17496 * q + 4477) := by ring
  have h_odd : (17496 * q + 4477) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 5969) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 4477) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 4477) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 4477) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2095 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2095 (q : ℕ) (hq : 8192 * q + 2095 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2095)))))))) < 8192 * q + 2095 := by
  rw [step7_m8192_2095 q]
  have h_bound : step (17496 * q + 4477) ≤ 6561 * q + 1679 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 4477) + 1 = 2 ^ 3 * (6561 * q + 1679) := by ring
    have hne : (6561 * q + 1679) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 4477) + 1) = 3 + ν₂ (6561 * q + 1679) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 1679) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1679) (2 ^ ν₂ (6561 * q + 1679)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2271 (q : ℕ) : step (8192 * q + 2271) = 12288 * q + 3407 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2271) + 1 = 2 ^ 1 * (12288 * q + 3407) := by ring
  have h_odd : (12288 * q + 3407) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2271) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3407) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3407) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3407) (by positivity)]

theorem step2_m8192_2271 (q : ℕ) : step (step (8192 * q + 2271)) = 18432 * q + 5111 := by
  rw [step_m8192_2271 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3407) + 1 = 2 ^ 1 * (18432 * q + 5111) := by ring
  have h_odd : (18432 * q + 5111) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3407) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 5111) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 5111) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 5111) (by positivity)]

theorem step3_m8192_2271 (q : ℕ) : step (step (step (8192 * q + 2271))) = 27648 * q + 7667 := by
  rw [step2_m8192_2271 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 5111) + 1 = 2 ^ 1 * (27648 * q + 7667) := by ring
  have h_odd : (27648 * q + 7667) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 5111) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 7667) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 7667) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 7667) (by positivity)]

theorem step4_m8192_2271 (q : ℕ) : step (step (step (step (8192 * q + 2271)))) = 41472 * q + 11501 := by
  rw [step3_m8192_2271 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 7667) + 1 = 2 ^ 1 * (41472 * q + 11501) := by ring
  have h_odd : (41472 * q + 11501) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 7667) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 11501) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 11501) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 11501) (by positivity)]

theorem step5_m8192_2271 (q : ℕ) : step (step (step (step (step (8192 * q + 2271))))) = 15552 * q + 4313 := by
  rw [step4_m8192_2271 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 11501) + 1 = 2 ^ 3 * (15552 * q + 4313) := by ring
  have h_odd : (15552 * q + 4313) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 11501) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (15552 * q + 4313) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (15552 * q + 4313) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 4313) (by positivity)]

theorem step6_m8192_2271 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2271)))))) = 11664 * q + 3235 := by
  rw [step5_m8192_2271 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 4313) + 1 = 2 ^ 2 * (11664 * q + 3235) := by ring
  have h_odd : (11664 * q + 3235) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 4313) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 3235) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 3235) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 3235) (by positivity)]

theorem step7_m8192_2271 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2271))))))) = 17496 * q + 4853 := by
  rw [step6_m8192_2271 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 3235) + 1 = 2 ^ 1 * (17496 * q + 4853) := by ring
  have h_odd : (17496 * q + 4853) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 3235) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 4853) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 4853) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 4853) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2271 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2271 (q : ℕ) (hq : 8192 * q + 2271 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2271)))))))) < 8192 * q + 2271 := by
  rw [step7_m8192_2271 q]
  have h_bound : step (17496 * q + 4853) ≤ 6561 * q + 1820 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 4853) + 1 = 2 ^ 3 * (6561 * q + 1820) := by ring
    have hne : (6561 * q + 1820) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 4853) + 1) = 3 + ν₂ (6561 * q + 1820) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 1820) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1820) (2 ^ ν₂ (6561 * q + 1820)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2331 (q : ℕ) : step (8192 * q + 2331) = 12288 * q + 3497 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2331) + 1 = 2 ^ 1 * (12288 * q + 3497) := by ring
  have h_odd : (12288 * q + 3497) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2331) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3497) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3497) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3497) (by positivity)]

theorem step2_m8192_2331 (q : ℕ) : step (step (8192 * q + 2331)) = 9216 * q + 2623 := by
  rw [step_m8192_2331 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3497) + 1 = 2 ^ 2 * (9216 * q + 2623) := by ring
  have h_odd : (9216 * q + 2623) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3497) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 2623) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 2623) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 2623) (by positivity)]

theorem step3_m8192_2331 (q : ℕ) : step (step (step (8192 * q + 2331))) = 13824 * q + 3935 := by
  rw [step2_m8192_2331 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 2623) + 1 = 2 ^ 1 * (13824 * q + 3935) := by ring
  have h_odd : (13824 * q + 3935) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 2623) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 3935) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 3935) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 3935) (by positivity)]

theorem step4_m8192_2331 (q : ℕ) : step (step (step (step (8192 * q + 2331)))) = 20736 * q + 5903 := by
  rw [step3_m8192_2331 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 3935) + 1 = 2 ^ 1 * (20736 * q + 5903) := by ring
  have h_odd : (20736 * q + 5903) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 3935) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 5903) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 5903) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 5903) (by positivity)]

theorem step5_m8192_2331 (q : ℕ) : step (step (step (step (step (8192 * q + 2331))))) = 31104 * q + 8855 := by
  rw [step4_m8192_2331 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 5903) + 1 = 2 ^ 1 * (31104 * q + 8855) := by ring
  have h_odd : (31104 * q + 8855) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 5903) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 8855) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 8855) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 8855) (by positivity)]

theorem step6_m8192_2331 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2331)))))) = 46656 * q + 13283 := by
  rw [step5_m8192_2331 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 8855) + 1 = 2 ^ 1 * (46656 * q + 13283) := by ring
  have h_odd : (46656 * q + 13283) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 8855) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 13283) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 13283) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 13283) (by positivity)]

theorem step7_m8192_2331 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2331))))))) = 69984 * q + 19925 := by
  rw [step6_m8192_2331 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 13283) + 1 = 2 ^ 1 * (69984 * q + 19925) := by ring
  have h_odd : (69984 * q + 19925) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 13283) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (69984 * q + 19925) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (69984 * q + 19925) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (69984 * q + 19925) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2331 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2331 (q : ℕ) (hq : 8192 * q + 2331 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2331)))))))) < 8192 * q + 2331 := by
  rw [step7_m8192_2331 q]
  have h_bound : step (69984 * q + 19925) ≤ 6561 * q + 1868 := by
    unfold step
    have h3n1 : 3 * (69984 * q + 19925) + 1 = 2 ^ 5 * (6561 * q + 1868) := by ring
    have hne : (6561 * q + 1868) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (69984 * q + 19925) + 1) = 5 + ν₂ (6561 * q + 1868) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (6561 * q + 1868) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1868) (2 ^ ν₂ (6561 * q + 1868)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2431 (q : ℕ) : step (8192 * q + 2431) = 12288 * q + 3647 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2431) + 1 = 2 ^ 1 * (12288 * q + 3647) := by ring
  have h_odd : (12288 * q + 3647) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2431) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3647) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3647) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3647) (by positivity)]

theorem step2_m8192_2431 (q : ℕ) : step (step (8192 * q + 2431)) = 18432 * q + 5471 := by
  rw [step_m8192_2431 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3647) + 1 = 2 ^ 1 * (18432 * q + 5471) := by ring
  have h_odd : (18432 * q + 5471) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3647) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 5471) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 5471) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 5471) (by positivity)]

theorem step3_m8192_2431 (q : ℕ) : step (step (step (8192 * q + 2431))) = 27648 * q + 8207 := by
  rw [step2_m8192_2431 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 5471) + 1 = 2 ^ 1 * (27648 * q + 8207) := by ring
  have h_odd : (27648 * q + 8207) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 5471) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 8207) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 8207) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 8207) (by positivity)]

theorem step4_m8192_2431 (q : ℕ) : step (step (step (step (8192 * q + 2431)))) = 41472 * q + 12311 := by
  rw [step3_m8192_2431 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 8207) + 1 = 2 ^ 1 * (41472 * q + 12311) := by ring
  have h_odd : (41472 * q + 12311) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 8207) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 12311) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 12311) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 12311) (by positivity)]

theorem step5_m8192_2431 (q : ℕ) : step (step (step (step (step (8192 * q + 2431))))) = 62208 * q + 18467 := by
  rw [step4_m8192_2431 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 12311) + 1 = 2 ^ 1 * (62208 * q + 18467) := by ring
  have h_odd : (62208 * q + 18467) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 12311) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 18467) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 18467) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 18467) (by positivity)]

theorem step6_m8192_2431 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2431)))))) = 93312 * q + 27701 := by
  rw [step5_m8192_2431 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 18467) + 1 = 2 ^ 1 * (93312 * q + 27701) := by ring
  have h_odd : (93312 * q + 27701) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 18467) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (93312 * q + 27701) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (93312 * q + 27701) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (93312 * q + 27701) (by positivity)]

theorem step7_m8192_2431 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2431))))))) = 8748 * q + 2597 := by
  rw [step6_m8192_2431 q]
  unfold step
  have h3n1 : 3 * (93312 * q + 27701) + 1 = 2 ^ 5 * (8748 * q + 2597) := by ring
  have h_odd : (8748 * q + 2597) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (93312 * q + 27701) + 1) = 5 := by
    rw [h3n1, ν₂_mul (2 ^ 5) (8748 * q + 2597) (by positivity) (by omega),
        ν₂_pow_two' 5, ν₂_odd (8748 * q + 2597) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 2597) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2431 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2431 (q : ℕ) (hq : 8192 * q + 2431 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2431)))))))) < 8192 * q + 2431 := by
  rw [step7_m8192_2431 q]
  have h_bound : step (8748 * q + 2597) ≤ 6561 * q + 1948 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 2597) + 1 = 2 ^ 2 * (6561 * q + 1948) := by ring
    have hne : (6561 * q + 1948) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 2597) + 1) = 2 + ν₂ (6561 * q + 1948) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 1948) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1948) (2 ^ ν₂ (6561 * q + 1948)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2473 (q : ℕ) : step (8192 * q + 2473) = 6144 * q + 1855 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2473) + 1 = 2 ^ 2 * (6144 * q + 1855) := by ring
  have h_odd : (6144 * q + 1855) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2473) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 1855) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 1855) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 1855) (by positivity)]

theorem step2_m8192_2473 (q : ℕ) : step (step (8192 * q + 2473)) = 9216 * q + 2783 := by
  rw [step_m8192_2473 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 1855) + 1 = 2 ^ 1 * (9216 * q + 2783) := by ring
  have h_odd : (9216 * q + 2783) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 1855) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 2783) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 2783) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 2783) (by positivity)]

theorem step3_m8192_2473 (q : ℕ) : step (step (step (8192 * q + 2473))) = 13824 * q + 4175 := by
  rw [step2_m8192_2473 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 2783) + 1 = 2 ^ 1 * (13824 * q + 4175) := by ring
  have h_odd : (13824 * q + 4175) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 2783) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 4175) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 4175) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 4175) (by positivity)]

theorem step4_m8192_2473 (q : ℕ) : step (step (step (step (8192 * q + 2473)))) = 20736 * q + 6263 := by
  rw [step3_m8192_2473 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 4175) + 1 = 2 ^ 1 * (20736 * q + 6263) := by ring
  have h_odd : (20736 * q + 6263) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 4175) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 6263) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 6263) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 6263) (by positivity)]

theorem step5_m8192_2473 (q : ℕ) : step (step (step (step (step (8192 * q + 2473))))) = 31104 * q + 9395 := by
  rw [step4_m8192_2473 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 6263) + 1 = 2 ^ 1 * (31104 * q + 9395) := by ring
  have h_odd : (31104 * q + 9395) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 6263) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 9395) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 9395) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 9395) (by positivity)]

theorem step6_m8192_2473 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2473)))))) = 46656 * q + 14093 := by
  rw [step5_m8192_2473 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 9395) + 1 = 2 ^ 1 * (46656 * q + 14093) := by ring
  have h_odd : (46656 * q + 14093) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 9395) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 14093) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 14093) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 14093) (by positivity)]

theorem step7_m8192_2473 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2473))))))) = 17496 * q + 5285 := by
  rw [step6_m8192_2473 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 14093) + 1 = 2 ^ 3 * (17496 * q + 5285) := by ring
  have h_odd : (17496 * q + 5285) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 14093) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (17496 * q + 5285) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (17496 * q + 5285) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 5285) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2473 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2473 (q : ℕ) (hq : 8192 * q + 2473 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2473)))))))) < 8192 * q + 2473 := by
  rw [step7_m8192_2473 q]
  have h_bound : step (17496 * q + 5285) ≤ 6561 * q + 1982 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 5285) + 1 = 2 ^ 3 * (6561 * q + 1982) := by ring
    have hne : (6561 * q + 1982) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 5285) + 1) = 3 + ν₂ (6561 * q + 1982) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 1982) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 1982) (2 ^ ν₂ (6561 * q + 1982)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2607 (q : ℕ) : step (8192 * q + 2607) = 12288 * q + 3911 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2607) + 1 = 2 ^ 1 * (12288 * q + 3911) := by ring
  have h_odd : (12288 * q + 3911) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3911) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3911) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3911) (by positivity)]

theorem step2_m8192_2607 (q : ℕ) : step (step (8192 * q + 2607)) = 18432 * q + 5867 := by
  rw [step_m8192_2607 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3911) + 1 = 2 ^ 1 * (18432 * q + 5867) := by ring
  have h_odd : (18432 * q + 5867) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 5867) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 5867) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 5867) (by positivity)]

theorem step3_m8192_2607 (q : ℕ) : step (step (step (8192 * q + 2607))) = 27648 * q + 8801 := by
  rw [step2_m8192_2607 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 5867) + 1 = 2 ^ 1 * (27648 * q + 8801) := by ring
  have h_odd : (27648 * q + 8801) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 5867) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 8801) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 8801) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 8801) (by positivity)]

theorem step4_m8192_2607 (q : ℕ) : step (step (step (step (8192 * q + 2607)))) = 20736 * q + 6601 := by
  rw [step3_m8192_2607 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 8801) + 1 = 2 ^ 2 * (20736 * q + 6601) := by ring
  have h_odd : (20736 * q + 6601) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 8801) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 6601) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 6601) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 6601) (by positivity)]

theorem step5_m8192_2607 (q : ℕ) : step (step (step (step (step (8192 * q + 2607))))) = 15552 * q + 4951 := by
  rw [step4_m8192_2607 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 6601) + 1 = 2 ^ 2 * (15552 * q + 4951) := by ring
  have h_odd : (15552 * q + 4951) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 6601) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 4951) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 4951) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 4951) (by positivity)]

theorem step6_m8192_2607 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2607)))))) = 23328 * q + 7427 := by
  rw [step5_m8192_2607 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 4951) + 1 = 2 ^ 1 * (23328 * q + 7427) := by ring
  have h_odd : (23328 * q + 7427) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 4951) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 7427) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 7427) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 7427) (by positivity)]

theorem step7_m8192_2607 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2607))))))) = 34992 * q + 11141 := by
  rw [step6_m8192_2607 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 7427) + 1 = 2 ^ 1 * (34992 * q + 11141) := by ring
  have h_odd : (34992 * q + 11141) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 7427) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 11141) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 11141) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 11141) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2607 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2607 (q : ℕ) (hq : 8192 * q + 2607 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2607)))))))) < 8192 * q + 2607 := by
  rw [step7_m8192_2607 q]
  have h_bound : step (34992 * q + 11141) ≤ 6561 * q + 2089 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 11141) + 1 = 2 ^ 4 * (6561 * q + 2089) := by ring
    have hne : (6561 * q + 2089) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 11141) + 1) = 4 + ν₂ (6561 * q + 2089) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 2089) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2089) (2 ^ ν₂ (6561 * q + 2089)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2663 (q : ℕ) : step (8192 * q + 2663) = 12288 * q + 3995 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2663) + 1 = 2 ^ 1 * (12288 * q + 3995) := by ring
  have h_odd : (12288 * q + 3995) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2663) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 3995) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 3995) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 3995) (by positivity)]

theorem step2_m8192_2663 (q : ℕ) : step (step (8192 * q + 2663)) = 18432 * q + 5993 := by
  rw [step_m8192_2663 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 3995) + 1 = 2 ^ 1 * (18432 * q + 5993) := by ring
  have h_odd : (18432 * q + 5993) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 3995) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 5993) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 5993) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 5993) (by positivity)]

theorem step3_m8192_2663 (q : ℕ) : step (step (step (8192 * q + 2663))) = 13824 * q + 4495 := by
  rw [step2_m8192_2663 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 5993) + 1 = 2 ^ 2 * (13824 * q + 4495) := by ring
  have h_odd : (13824 * q + 4495) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 5993) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 4495) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 4495) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 4495) (by positivity)]

theorem step4_m8192_2663 (q : ℕ) : step (step (step (step (8192 * q + 2663)))) = 20736 * q + 6743 := by
  rw [step3_m8192_2663 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 4495) + 1 = 2 ^ 1 * (20736 * q + 6743) := by ring
  have h_odd : (20736 * q + 6743) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 4495) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 6743) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 6743) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 6743) (by positivity)]

theorem step5_m8192_2663 (q : ℕ) : step (step (step (step (step (8192 * q + 2663))))) = 31104 * q + 10115 := by
  rw [step4_m8192_2663 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 6743) + 1 = 2 ^ 1 * (31104 * q + 10115) := by ring
  have h_odd : (31104 * q + 10115) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 6743) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 10115) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 10115) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 10115) (by positivity)]

theorem step6_m8192_2663 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2663)))))) = 46656 * q + 15173 := by
  rw [step5_m8192_2663 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 10115) + 1 = 2 ^ 1 * (46656 * q + 15173) := by ring
  have h_odd : (46656 * q + 15173) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 10115) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 15173) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 15173) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 15173) (by positivity)]

theorem step7_m8192_2663 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2663))))))) = 8748 * q + 2845 := by
  rw [step6_m8192_2663 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 15173) + 1 = 2 ^ 4 * (8748 * q + 2845) := by ring
  have h_odd : (8748 * q + 2845) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 15173) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (8748 * q + 2845) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (8748 * q + 2845) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 2845) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2663 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2663 (q : ℕ) (hq : 8192 * q + 2663 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2663)))))))) < 8192 * q + 2663 := by
  rw [step7_m8192_2663 q]
  have h_bound : step (8748 * q + 2845) ≤ 6561 * q + 2134 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 2845) + 1 = 2 ^ 2 * (6561 * q + 2134) := by ring
    have hne : (6561 * q + 2134) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 2845) + 1) = 2 + ν₂ (6561 * q + 2134) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 2134) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2134) (2 ^ ν₂ (6561 * q + 2134)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_2985 (q : ℕ) : step (8192 * q + 2985) = 6144 * q + 2239 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 2985) + 1 = 2 ^ 2 * (6144 * q + 2239) := by ring
  have h_odd : (6144 * q + 2239) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 2985) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 2239) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 2239) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2239) (by positivity)]

theorem step2_m8192_2985 (q : ℕ) : step (step (8192 * q + 2985)) = 9216 * q + 3359 := by
  rw [step_m8192_2985 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2239) + 1 = 2 ^ 1 * (9216 * q + 3359) := by ring
  have h_odd : (9216 * q + 3359) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2239) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 3359) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 3359) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 3359) (by positivity)]

theorem step3_m8192_2985 (q : ℕ) : step (step (step (8192 * q + 2985))) = 13824 * q + 5039 := by
  rw [step2_m8192_2985 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 3359) + 1 = 2 ^ 1 * (13824 * q + 5039) := by ring
  have h_odd : (13824 * q + 5039) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 3359) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 5039) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 5039) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 5039) (by positivity)]

theorem step4_m8192_2985 (q : ℕ) : step (step (step (step (8192 * q + 2985)))) = 20736 * q + 7559 := by
  rw [step3_m8192_2985 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 5039) + 1 = 2 ^ 1 * (20736 * q + 7559) := by ring
  have h_odd : (20736 * q + 7559) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 5039) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 7559) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 7559) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 7559) (by positivity)]

theorem step5_m8192_2985 (q : ℕ) : step (step (step (step (step (8192 * q + 2985))))) = 31104 * q + 11339 := by
  rw [step4_m8192_2985 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 7559) + 1 = 2 ^ 1 * (31104 * q + 11339) := by ring
  have h_odd : (31104 * q + 11339) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 7559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 11339) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 11339) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 11339) (by positivity)]

theorem step6_m8192_2985 (q : ℕ) : step (step (step (step (step (step (8192 * q + 2985)))))) = 46656 * q + 17009 := by
  rw [step5_m8192_2985 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 11339) + 1 = 2 ^ 1 * (46656 * q + 17009) := by ring
  have h_odd : (46656 * q + 17009) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 11339) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 17009) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 17009) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 17009) (by positivity)]

theorem step7_m8192_2985 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 2985))))))) = 34992 * q + 12757 := by
  rw [step6_m8192_2985 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 17009) + 1 = 2 ^ 2 * (34992 * q + 12757) := by ring
  have h_odd : (34992 * q + 12757) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 17009) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (34992 * q + 12757) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (34992 * q + 12757) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 12757) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 2985 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_2985 (q : ℕ) (hq : 8192 * q + 2985 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 2985)))))))) < 8192 * q + 2985 := by
  rw [step7_m8192_2985 q]
  have h_bound : step (34992 * q + 12757) ≤ 6561 * q + 2392 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 12757) + 1 = 2 ^ 4 * (6561 * q + 2392) := by ring
    have hne : (6561 * q + 2392) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 12757) + 1) = 4 + ν₂ (6561 * q + 2392) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 2392) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2392) (2 ^ ν₂ (6561 * q + 2392)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3039 (q : ℕ) : step (8192 * q + 3039) = 12288 * q + 4559 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3039) + 1 = 2 ^ 1 * (12288 * q + 4559) := by ring
  have h_odd : (12288 * q + 4559) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3039) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 4559) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 4559) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 4559) (by positivity)]

theorem step2_m8192_3039 (q : ℕ) : step (step (8192 * q + 3039)) = 18432 * q + 6839 := by
  rw [step_m8192_3039 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 4559) + 1 = 2 ^ 1 * (18432 * q + 6839) := by ring
  have h_odd : (18432 * q + 6839) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 4559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 6839) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 6839) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 6839) (by positivity)]

theorem step3_m8192_3039 (q : ℕ) : step (step (step (8192 * q + 3039))) = 27648 * q + 10259 := by
  rw [step2_m8192_3039 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 6839) + 1 = 2 ^ 1 * (27648 * q + 10259) := by ring
  have h_odd : (27648 * q + 10259) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 6839) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 10259) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 10259) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 10259) (by positivity)]

theorem step4_m8192_3039 (q : ℕ) : step (step (step (step (8192 * q + 3039)))) = 41472 * q + 15389 := by
  rw [step3_m8192_3039 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 10259) + 1 = 2 ^ 1 * (41472 * q + 15389) := by ring
  have h_odd : (41472 * q + 15389) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 10259) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 15389) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 15389) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 15389) (by positivity)]

theorem step5_m8192_3039 (q : ℕ) : step (step (step (step (step (8192 * q + 3039))))) = 15552 * q + 5771 := by
  rw [step4_m8192_3039 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 15389) + 1 = 2 ^ 3 * (15552 * q + 5771) := by ring
  have h_odd : (15552 * q + 5771) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 15389) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (15552 * q + 5771) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (15552 * q + 5771) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 5771) (by positivity)]

theorem step6_m8192_3039 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3039)))))) = 23328 * q + 8657 := by
  rw [step5_m8192_3039 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 5771) + 1 = 2 ^ 1 * (23328 * q + 8657) := by ring
  have h_odd : (23328 * q + 8657) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 5771) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 8657) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 8657) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 8657) (by positivity)]

theorem step7_m8192_3039 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3039))))))) = 17496 * q + 6493 := by
  rw [step6_m8192_3039 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 8657) + 1 = 2 ^ 2 * (17496 * q + 6493) := by ring
  have h_odd : (17496 * q + 6493) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 8657) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 6493) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 6493) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 6493) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3039 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3039 (q : ℕ) (hq : 8192 * q + 3039 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3039)))))))) < 8192 * q + 3039 := by
  rw [step7_m8192_3039 q]
  have h_bound : step (17496 * q + 6493) ≤ 6561 * q + 2435 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 6493) + 1 = 2 ^ 3 * (6561 * q + 2435) := by ring
    have hne : (6561 * q + 2435) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 6493) + 1) = 3 + ν₂ (6561 * q + 2435) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 2435) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2435) (2 ^ ν₂ (6561 * q + 2435)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3067 (q : ℕ) : step (8192 * q + 3067) = 12288 * q + 4601 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3067) + 1 = 2 ^ 1 * (12288 * q + 4601) := by ring
  have h_odd : (12288 * q + 4601) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3067) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 4601) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 4601) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 4601) (by positivity)]

theorem step2_m8192_3067 (q : ℕ) : step (step (8192 * q + 3067)) = 9216 * q + 3451 := by
  rw [step_m8192_3067 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 4601) + 1 = 2 ^ 2 * (9216 * q + 3451) := by ring
  have h_odd : (9216 * q + 3451) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 4601) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 3451) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 3451) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 3451) (by positivity)]

theorem step3_m8192_3067 (q : ℕ) : step (step (step (8192 * q + 3067))) = 13824 * q + 5177 := by
  rw [step2_m8192_3067 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 3451) + 1 = 2 ^ 1 * (13824 * q + 5177) := by ring
  have h_odd : (13824 * q + 5177) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 3451) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 5177) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 5177) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 5177) (by positivity)]

theorem step4_m8192_3067 (q : ℕ) : step (step (step (step (8192 * q + 3067)))) = 10368 * q + 3883 := by
  rw [step3_m8192_3067 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 5177) + 1 = 2 ^ 2 * (10368 * q + 3883) := by ring
  have h_odd : (10368 * q + 3883) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 5177) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 3883) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 3883) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 3883) (by positivity)]

theorem step5_m8192_3067 (q : ℕ) : step (step (step (step (step (8192 * q + 3067))))) = 15552 * q + 5825 := by
  rw [step4_m8192_3067 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 3883) + 1 = 2 ^ 1 * (15552 * q + 5825) := by ring
  have h_odd : (15552 * q + 5825) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 3883) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 5825) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 5825) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 5825) (by positivity)]

theorem step6_m8192_3067 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3067)))))) = 11664 * q + 4369 := by
  rw [step5_m8192_3067 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 5825) + 1 = 2 ^ 2 * (11664 * q + 4369) := by ring
  have h_odd : (11664 * q + 4369) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 5825) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 4369) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 4369) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 4369) (by positivity)]

theorem step7_m8192_3067 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3067))))))) = 8748 * q + 3277 := by
  rw [step6_m8192_3067 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 4369) + 1 = 2 ^ 2 * (8748 * q + 3277) := by ring
  have h_odd : (8748 * q + 3277) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 4369) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 3277) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 3277) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 3277) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3067 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3067 (q : ℕ) (hq : 8192 * q + 3067 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3067)))))))) < 8192 * q + 3067 := by
  rw [step7_m8192_3067 q]
  have h_bound : step (8748 * q + 3277) ≤ 6561 * q + 2458 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 3277) + 1 = 2 ^ 2 * (6561 * q + 2458) := by ring
    have hne : (6561 * q + 2458) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 3277) + 1) = 2 + ν₂ (6561 * q + 2458) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 2458) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2458) (2 ^ ν₂ (6561 * q + 2458)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3135 (q : ℕ) : step (8192 * q + 3135) = 12288 * q + 4703 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3135) + 1 = 2 ^ 1 * (12288 * q + 4703) := by ring
  have h_odd : (12288 * q + 4703) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3135) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 4703) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 4703) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 4703) (by positivity)]

theorem step2_m8192_3135 (q : ℕ) : step (step (8192 * q + 3135)) = 18432 * q + 7055 := by
  rw [step_m8192_3135 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 4703) + 1 = 2 ^ 1 * (18432 * q + 7055) := by ring
  have h_odd : (18432 * q + 7055) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 4703) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 7055) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 7055) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 7055) (by positivity)]

theorem step3_m8192_3135 (q : ℕ) : step (step (step (8192 * q + 3135))) = 27648 * q + 10583 := by
  rw [step2_m8192_3135 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 7055) + 1 = 2 ^ 1 * (27648 * q + 10583) := by ring
  have h_odd : (27648 * q + 10583) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 7055) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 10583) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 10583) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 10583) (by positivity)]

theorem step4_m8192_3135 (q : ℕ) : step (step (step (step (8192 * q + 3135)))) = 41472 * q + 15875 := by
  rw [step3_m8192_3135 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 10583) + 1 = 2 ^ 1 * (41472 * q + 15875) := by ring
  have h_odd : (41472 * q + 15875) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 10583) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 15875) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 15875) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 15875) (by positivity)]

theorem step5_m8192_3135 (q : ℕ) : step (step (step (step (step (8192 * q + 3135))))) = 62208 * q + 23813 := by
  rw [step4_m8192_3135 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 15875) + 1 = 2 ^ 1 * (62208 * q + 23813) := by ring
  have h_odd : (62208 * q + 23813) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 15875) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 23813) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 23813) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 23813) (by positivity)]

theorem step6_m8192_3135 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3135)))))) = 11664 * q + 4465 := by
  rw [step5_m8192_3135 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 23813) + 1 = 2 ^ 4 * (11664 * q + 4465) := by ring
  have h_odd : (11664 * q + 4465) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 23813) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (11664 * q + 4465) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (11664 * q + 4465) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 4465) (by positivity)]

theorem step7_m8192_3135 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3135))))))) = 8748 * q + 3349 := by
  rw [step6_m8192_3135 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 4465) + 1 = 2 ^ 2 * (8748 * q + 3349) := by ring
  have h_odd : (8748 * q + 3349) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 4465) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 3349) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 3349) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 3349) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3135 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3135 (q : ℕ) (hq : 8192 * q + 3135 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3135)))))))) < 8192 * q + 3135 := by
  rw [step7_m8192_3135 q]
  have h_bound : step (8748 * q + 3349) ≤ 6561 * q + 2512 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 3349) + 1 = 2 ^ 2 * (6561 * q + 2512) := by ring
    have hne : (6561 * q + 2512) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 3349) + 1) = 2 + ν₂ (6561 * q + 2512) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 2512) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2512) (2 ^ ν₂ (6561 * q + 2512)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3241 (q : ℕ) : step (8192 * q + 3241) = 6144 * q + 2431 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3241) + 1 = 2 ^ 2 * (6144 * q + 2431) := by ring
  have h_odd : (6144 * q + 2431) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3241) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 2431) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 2431) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2431) (by positivity)]

theorem step2_m8192_3241 (q : ℕ) : step (step (8192 * q + 3241)) = 9216 * q + 3647 := by
  rw [step_m8192_3241 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2431) + 1 = 2 ^ 1 * (9216 * q + 3647) := by ring
  have h_odd : (9216 * q + 3647) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2431) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 3647) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 3647) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 3647) (by positivity)]

theorem step3_m8192_3241 (q : ℕ) : step (step (step (8192 * q + 3241))) = 13824 * q + 5471 := by
  rw [step2_m8192_3241 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 3647) + 1 = 2 ^ 1 * (13824 * q + 5471) := by ring
  have h_odd : (13824 * q + 5471) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 3647) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 5471) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 5471) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 5471) (by positivity)]

theorem step4_m8192_3241 (q : ℕ) : step (step (step (step (8192 * q + 3241)))) = 20736 * q + 8207 := by
  rw [step3_m8192_3241 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 5471) + 1 = 2 ^ 1 * (20736 * q + 8207) := by ring
  have h_odd : (20736 * q + 8207) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 5471) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 8207) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 8207) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 8207) (by positivity)]

theorem step5_m8192_3241 (q : ℕ) : step (step (step (step (step (8192 * q + 3241))))) = 31104 * q + 12311 := by
  rw [step4_m8192_3241 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 8207) + 1 = 2 ^ 1 * (31104 * q + 12311) := by ring
  have h_odd : (31104 * q + 12311) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 8207) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 12311) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 12311) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 12311) (by positivity)]

theorem step6_m8192_3241 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3241)))))) = 46656 * q + 18467 := by
  rw [step5_m8192_3241 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 12311) + 1 = 2 ^ 1 * (46656 * q + 18467) := by ring
  have h_odd : (46656 * q + 18467) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 12311) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 18467) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 18467) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 18467) (by positivity)]

theorem step7_m8192_3241 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3241))))))) = 69984 * q + 27701 := by
  rw [step6_m8192_3241 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 18467) + 1 = 2 ^ 1 * (69984 * q + 27701) := by ring
  have h_odd : (69984 * q + 27701) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 18467) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (69984 * q + 27701) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (69984 * q + 27701) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (69984 * q + 27701) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3241 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3241 (q : ℕ) (hq : 8192 * q + 3241 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3241)))))))) < 8192 * q + 3241 := by
  rw [step7_m8192_3241 q]
  have h_bound : step (69984 * q + 27701) ≤ 6561 * q + 2597 := by
    unfold step
    have h3n1 : 3 * (69984 * q + 27701) + 1 = 2 ^ 5 * (6561 * q + 2597) := by ring
    have hne : (6561 * q + 2597) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (69984 * q + 27701) + 1) = 5 + ν₂ (6561 * q + 2597) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (6561 * q + 2597) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2597) (2 ^ ν₂ (6561 * q + 2597)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3455 (q : ℕ) : step (8192 * q + 3455) = 12288 * q + 5183 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3455) + 1 = 2 ^ 1 * (12288 * q + 5183) := by ring
  have h_odd : (12288 * q + 5183) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3455) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 5183) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 5183) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 5183) (by positivity)]

theorem step2_m8192_3455 (q : ℕ) : step (step (8192 * q + 3455)) = 18432 * q + 7775 := by
  rw [step_m8192_3455 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 5183) + 1 = 2 ^ 1 * (18432 * q + 7775) := by ring
  have h_odd : (18432 * q + 7775) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 5183) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 7775) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 7775) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 7775) (by positivity)]

theorem step3_m8192_3455 (q : ℕ) : step (step (step (8192 * q + 3455))) = 27648 * q + 11663 := by
  rw [step2_m8192_3455 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 7775) + 1 = 2 ^ 1 * (27648 * q + 11663) := by ring
  have h_odd : (27648 * q + 11663) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 7775) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 11663) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 11663) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 11663) (by positivity)]

theorem step4_m8192_3455 (q : ℕ) : step (step (step (step (8192 * q + 3455)))) = 41472 * q + 17495 := by
  rw [step3_m8192_3455 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 11663) + 1 = 2 ^ 1 * (41472 * q + 17495) := by ring
  have h_odd : (41472 * q + 17495) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 11663) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 17495) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 17495) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 17495) (by positivity)]

theorem step5_m8192_3455 (q : ℕ) : step (step (step (step (step (8192 * q + 3455))))) = 62208 * q + 26243 := by
  rw [step4_m8192_3455 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 17495) + 1 = 2 ^ 1 * (62208 * q + 26243) := by ring
  have h_odd : (62208 * q + 26243) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 17495) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 26243) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 26243) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 26243) (by positivity)]

theorem step6_m8192_3455 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3455)))))) = 93312 * q + 39365 := by
  rw [step5_m8192_3455 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 26243) + 1 = 2 ^ 1 * (93312 * q + 39365) := by ring
  have h_odd : (93312 * q + 39365) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 26243) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (93312 * q + 39365) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (93312 * q + 39365) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (93312 * q + 39365) (by positivity)]

theorem step7_m8192_3455 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3455))))))) = 17496 * q + 7381 := by
  rw [step6_m8192_3455 q]
  unfold step
  have h3n1 : 3 * (93312 * q + 39365) + 1 = 2 ^ 4 * (17496 * q + 7381) := by ring
  have h_odd : (17496 * q + 7381) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (93312 * q + 39365) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (17496 * q + 7381) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (17496 * q + 7381) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 7381) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3455 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3455 (q : ℕ) (hq : 8192 * q + 3455 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3455)))))))) < 8192 * q + 3455 := by
  rw [step7_m8192_3455 q]
  have h_bound : step (17496 * q + 7381) ≤ 6561 * q + 2768 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 7381) + 1 = 2 ^ 3 * (6561 * q + 2768) := by ring
    have hne : (6561 * q + 2768) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 7381) + 1) = 3 + ν₂ (6561 * q + 2768) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 2768) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2768) (2 ^ ν₂ (6561 * q + 2768)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3483 (q : ℕ) : step (8192 * q + 3483) = 12288 * q + 5225 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3483) + 1 = 2 ^ 1 * (12288 * q + 5225) := by ring
  have h_odd : (12288 * q + 5225) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3483) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 5225) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 5225) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 5225) (by positivity)]

theorem step2_m8192_3483 (q : ℕ) : step (step (8192 * q + 3483)) = 9216 * q + 3919 := by
  rw [step_m8192_3483 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 5225) + 1 = 2 ^ 2 * (9216 * q + 3919) := by ring
  have h_odd : (9216 * q + 3919) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 5225) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 3919) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 3919) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 3919) (by positivity)]

theorem step3_m8192_3483 (q : ℕ) : step (step (step (8192 * q + 3483))) = 13824 * q + 5879 := by
  rw [step2_m8192_3483 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 3919) + 1 = 2 ^ 1 * (13824 * q + 5879) := by ring
  have h_odd : (13824 * q + 5879) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 3919) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 5879) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 5879) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 5879) (by positivity)]

theorem step4_m8192_3483 (q : ℕ) : step (step (step (step (8192 * q + 3483)))) = 20736 * q + 8819 := by
  rw [step3_m8192_3483 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 5879) + 1 = 2 ^ 1 * (20736 * q + 8819) := by ring
  have h_odd : (20736 * q + 8819) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 5879) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 8819) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 8819) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 8819) (by positivity)]

theorem step5_m8192_3483 (q : ℕ) : step (step (step (step (step (8192 * q + 3483))))) = 31104 * q + 13229 := by
  rw [step4_m8192_3483 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 8819) + 1 = 2 ^ 1 * (31104 * q + 13229) := by ring
  have h_odd : (31104 * q + 13229) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 8819) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 13229) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 13229) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 13229) (by positivity)]

theorem step6_m8192_3483 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3483)))))) = 11664 * q + 4961 := by
  rw [step5_m8192_3483 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 13229) + 1 = 2 ^ 3 * (11664 * q + 4961) := by ring
  have h_odd : (11664 * q + 4961) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 13229) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 4961) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 4961) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 4961) (by positivity)]

theorem step7_m8192_3483 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3483))))))) = 8748 * q + 3721 := by
  rw [step6_m8192_3483 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 4961) + 1 = 2 ^ 2 * (8748 * q + 3721) := by ring
  have h_odd : (8748 * q + 3721) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 4961) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 3721) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 3721) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 3721) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3483 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3483 (q : ℕ) (hq : 8192 * q + 3483 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3483)))))))) < 8192 * q + 3483 := by
  rw [step7_m8192_3483 q]
  have h_bound : step (8748 * q + 3721) ≤ 6561 * q + 2791 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 3721) + 1 = 2 ^ 2 * (6561 * q + 2791) := by ring
    have hne : (6561 * q + 2791) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 3721) + 1) = 2 + ν₂ (6561 * q + 2791) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 2791) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2791) (2 ^ ν₂ (6561 * q + 2791)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3551 (q : ℕ) : step (8192 * q + 3551) = 12288 * q + 5327 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3551) + 1 = 2 ^ 1 * (12288 * q + 5327) := by ring
  have h_odd : (12288 * q + 5327) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3551) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 5327) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 5327) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 5327) (by positivity)]

theorem step2_m8192_3551 (q : ℕ) : step (step (8192 * q + 3551)) = 18432 * q + 7991 := by
  rw [step_m8192_3551 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 5327) + 1 = 2 ^ 1 * (18432 * q + 7991) := by ring
  have h_odd : (18432 * q + 7991) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 5327) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 7991) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 7991) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 7991) (by positivity)]

theorem step3_m8192_3551 (q : ℕ) : step (step (step (8192 * q + 3551))) = 27648 * q + 11987 := by
  rw [step2_m8192_3551 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 7991) + 1 = 2 ^ 1 * (27648 * q + 11987) := by ring
  have h_odd : (27648 * q + 11987) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 7991) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 11987) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 11987) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 11987) (by positivity)]

theorem step4_m8192_3551 (q : ℕ) : step (step (step (step (8192 * q + 3551)))) = 41472 * q + 17981 := by
  rw [step3_m8192_3551 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 11987) + 1 = 2 ^ 1 * (41472 * q + 17981) := by ring
  have h_odd : (41472 * q + 17981) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 11987) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 17981) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 17981) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 17981) (by positivity)]

theorem step5_m8192_3551 (q : ℕ) : step (step (step (step (step (8192 * q + 3551))))) = 15552 * q + 6743 := by
  rw [step4_m8192_3551 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 17981) + 1 = 2 ^ 3 * (15552 * q + 6743) := by ring
  have h_odd : (15552 * q + 6743) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 17981) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (15552 * q + 6743) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (15552 * q + 6743) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 6743) (by positivity)]

theorem step6_m8192_3551 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3551)))))) = 23328 * q + 10115 := by
  rw [step5_m8192_3551 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 6743) + 1 = 2 ^ 1 * (23328 * q + 10115) := by ring
  have h_odd : (23328 * q + 10115) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 6743) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 10115) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 10115) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 10115) (by positivity)]

theorem step7_m8192_3551 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3551))))))) = 34992 * q + 15173 := by
  rw [step6_m8192_3551 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 10115) + 1 = 2 ^ 1 * (34992 * q + 15173) := by ring
  have h_odd : (34992 * q + 15173) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 10115) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 15173) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 15173) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 15173) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3551 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3551 (q : ℕ) (hq : 8192 * q + 3551 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3551)))))))) < 8192 * q + 3551 := by
  rw [step7_m8192_3551 q]
  have h_bound : step (34992 * q + 15173) ≤ 6561 * q + 2845 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 15173) + 1 = 2 ^ 4 * (6561 * q + 2845) := by ring
    have hne : (6561 * q + 2845) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 15173) + 1) = 4 + ν₂ (6561 * q + 2845) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 2845) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2845) (2 ^ ν₂ (6561 * q + 2845)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3687 (q : ℕ) : step (8192 * q + 3687) = 12288 * q + 5531 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3687) + 1 = 2 ^ 1 * (12288 * q + 5531) := by ring
  have h_odd : (12288 * q + 5531) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3687) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 5531) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 5531) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 5531) (by positivity)]

theorem step2_m8192_3687 (q : ℕ) : step (step (8192 * q + 3687)) = 18432 * q + 8297 := by
  rw [step_m8192_3687 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 5531) + 1 = 2 ^ 1 * (18432 * q + 8297) := by ring
  have h_odd : (18432 * q + 8297) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 5531) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 8297) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 8297) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 8297) (by positivity)]

theorem step3_m8192_3687 (q : ℕ) : step (step (step (8192 * q + 3687))) = 13824 * q + 6223 := by
  rw [step2_m8192_3687 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 8297) + 1 = 2 ^ 2 * (13824 * q + 6223) := by ring
  have h_odd : (13824 * q + 6223) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 8297) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 6223) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 6223) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 6223) (by positivity)]

theorem step4_m8192_3687 (q : ℕ) : step (step (step (step (8192 * q + 3687)))) = 20736 * q + 9335 := by
  rw [step3_m8192_3687 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 6223) + 1 = 2 ^ 1 * (20736 * q + 9335) := by ring
  have h_odd : (20736 * q + 9335) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 6223) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 9335) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 9335) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 9335) (by positivity)]

theorem step5_m8192_3687 (q : ℕ) : step (step (step (step (step (8192 * q + 3687))))) = 31104 * q + 14003 := by
  rw [step4_m8192_3687 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 9335) + 1 = 2 ^ 1 * (31104 * q + 14003) := by ring
  have h_odd : (31104 * q + 14003) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 9335) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 14003) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 14003) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 14003) (by positivity)]

theorem step6_m8192_3687 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3687)))))) = 46656 * q + 21005 := by
  rw [step5_m8192_3687 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 14003) + 1 = 2 ^ 1 * (46656 * q + 21005) := by ring
  have h_odd : (46656 * q + 21005) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 14003) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 21005) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 21005) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 21005) (by positivity)]

theorem step7_m8192_3687 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3687))))))) = 17496 * q + 7877 := by
  rw [step6_m8192_3687 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 21005) + 1 = 2 ^ 3 * (17496 * q + 7877) := by ring
  have h_odd : (17496 * q + 7877) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 21005) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (17496 * q + 7877) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (17496 * q + 7877) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 7877) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3687 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3687 (q : ℕ) (hq : 8192 * q + 3687 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3687)))))))) < 8192 * q + 3687 := by
  rw [step7_m8192_3687 q]
  have h_bound : step (17496 * q + 7877) ≤ 6561 * q + 2954 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 7877) + 1 = 2 ^ 3 * (6561 * q + 2954) := by ring
    have hne : (6561 * q + 2954) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 7877) + 1) = 3 + ν₂ (6561 * q + 2954) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 2954) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 2954) (2 ^ ν₂ (6561 * q + 2954)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3835 (q : ℕ) : step (8192 * q + 3835) = 12288 * q + 5753 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3835) + 1 = 2 ^ 1 * (12288 * q + 5753) := by ring
  have h_odd : (12288 * q + 5753) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3835) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 5753) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 5753) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 5753) (by positivity)]

theorem step2_m8192_3835 (q : ℕ) : step (step (8192 * q + 3835)) = 9216 * q + 4315 := by
  rw [step_m8192_3835 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 5753) + 1 = 2 ^ 2 * (9216 * q + 4315) := by ring
  have h_odd : (9216 * q + 4315) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 5753) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 4315) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 4315) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4315) (by positivity)]

theorem step3_m8192_3835 (q : ℕ) : step (step (step (8192 * q + 3835))) = 13824 * q + 6473 := by
  rw [step2_m8192_3835 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4315) + 1 = 2 ^ 1 * (13824 * q + 6473) := by ring
  have h_odd : (13824 * q + 6473) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4315) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 6473) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 6473) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 6473) (by positivity)]

theorem step4_m8192_3835 (q : ℕ) : step (step (step (step (8192 * q + 3835)))) = 10368 * q + 4855 := by
  rw [step3_m8192_3835 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 6473) + 1 = 2 ^ 2 * (10368 * q + 4855) := by ring
  have h_odd : (10368 * q + 4855) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 6473) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 4855) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 4855) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 4855) (by positivity)]

theorem step5_m8192_3835 (q : ℕ) : step (step (step (step (step (8192 * q + 3835))))) = 15552 * q + 7283 := by
  rw [step4_m8192_3835 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 4855) + 1 = 2 ^ 1 * (15552 * q + 7283) := by ring
  have h_odd : (15552 * q + 7283) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 4855) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 7283) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 7283) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 7283) (by positivity)]

theorem step6_m8192_3835 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3835)))))) = 23328 * q + 10925 := by
  rw [step5_m8192_3835 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 7283) + 1 = 2 ^ 1 * (23328 * q + 10925) := by ring
  have h_odd : (23328 * q + 10925) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 7283) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 10925) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 10925) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 10925) (by positivity)]

theorem step7_m8192_3835 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3835))))))) = 8748 * q + 4097 := by
  rw [step6_m8192_3835 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 10925) + 1 = 2 ^ 3 * (8748 * q + 4097) := by ring
  have h_odd : (8748 * q + 4097) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 10925) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 4097) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 4097) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 4097) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3835 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3835 (q : ℕ) (hq : 8192 * q + 3835 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3835)))))))) < 8192 * q + 3835 := by
  rw [step7_m8192_3835 q]
  have h_bound : step (8748 * q + 4097) ≤ 6561 * q + 3073 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 4097) + 1 = 2 ^ 2 * (6561 * q + 3073) := by ring
    have hne : (6561 * q + 3073) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 4097) + 1) = 2 + ν₂ (6561 * q + 3073) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3073) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3073) (2 ^ ν₂ (6561 * q + 3073)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3903 (q : ℕ) : step (8192 * q + 3903) = 12288 * q + 5855 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3903) + 1 = 2 ^ 1 * (12288 * q + 5855) := by ring
  have h_odd : (12288 * q + 5855) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3903) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 5855) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 5855) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 5855) (by positivity)]

theorem step2_m8192_3903 (q : ℕ) : step (step (8192 * q + 3903)) = 18432 * q + 8783 := by
  rw [step_m8192_3903 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 5855) + 1 = 2 ^ 1 * (18432 * q + 8783) := by ring
  have h_odd : (18432 * q + 8783) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 5855) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 8783) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 8783) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 8783) (by positivity)]

theorem step3_m8192_3903 (q : ℕ) : step (step (step (8192 * q + 3903))) = 27648 * q + 13175 := by
  rw [step2_m8192_3903 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 8783) + 1 = 2 ^ 1 * (27648 * q + 13175) := by ring
  have h_odd : (27648 * q + 13175) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 8783) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 13175) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 13175) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 13175) (by positivity)]

theorem step4_m8192_3903 (q : ℕ) : step (step (step (step (8192 * q + 3903)))) = 41472 * q + 19763 := by
  rw [step3_m8192_3903 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 13175) + 1 = 2 ^ 1 * (41472 * q + 19763) := by ring
  have h_odd : (41472 * q + 19763) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 13175) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 19763) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 19763) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 19763) (by positivity)]

theorem step5_m8192_3903 (q : ℕ) : step (step (step (step (step (8192 * q + 3903))))) = 62208 * q + 29645 := by
  rw [step4_m8192_3903 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 19763) + 1 = 2 ^ 1 * (62208 * q + 29645) := by ring
  have h_odd : (62208 * q + 29645) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 19763) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 29645) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 29645) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 29645) (by positivity)]

theorem step6_m8192_3903 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3903)))))) = 23328 * q + 11117 := by
  rw [step5_m8192_3903 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 29645) + 1 = 2 ^ 3 * (23328 * q + 11117) := by ring
  have h_odd : (23328 * q + 11117) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 29645) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (23328 * q + 11117) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (23328 * q + 11117) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 11117) (by positivity)]

theorem step7_m8192_3903 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3903))))))) = 8748 * q + 4169 := by
  rw [step6_m8192_3903 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 11117) + 1 = 2 ^ 3 * (8748 * q + 4169) := by ring
  have h_odd : (8748 * q + 4169) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 11117) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 4169) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 4169) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 4169) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3903 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3903 (q : ℕ) (hq : 8192 * q + 3903 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3903)))))))) < 8192 * q + 3903 := by
  rw [step7_m8192_3903 q]
  have h_bound : step (8748 * q + 4169) ≤ 6561 * q + 3127 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 4169) + 1 = 2 ^ 2 * (6561 * q + 3127) := by ring
    have hne : (6561 * q + 3127) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 4169) + 1) = 2 + ν₂ (6561 * q + 3127) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3127) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3127) (2 ^ ν₂ (6561 * q + 3127)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3967 (q : ℕ) : step (8192 * q + 3967) = 12288 * q + 5951 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3967) + 1 = 2 ^ 1 * (12288 * q + 5951) := by ring
  have h_odd : (12288 * q + 5951) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3967) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 5951) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 5951) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 5951) (by positivity)]

theorem step2_m8192_3967 (q : ℕ) : step (step (8192 * q + 3967)) = 18432 * q + 8927 := by
  rw [step_m8192_3967 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 5951) + 1 = 2 ^ 1 * (18432 * q + 8927) := by ring
  have h_odd : (18432 * q + 8927) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 5951) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 8927) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 8927) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 8927) (by positivity)]

theorem step3_m8192_3967 (q : ℕ) : step (step (step (8192 * q + 3967))) = 27648 * q + 13391 := by
  rw [step2_m8192_3967 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 8927) + 1 = 2 ^ 1 * (27648 * q + 13391) := by ring
  have h_odd : (27648 * q + 13391) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 8927) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 13391) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 13391) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 13391) (by positivity)]

theorem step4_m8192_3967 (q : ℕ) : step (step (step (step (8192 * q + 3967)))) = 41472 * q + 20087 := by
  rw [step3_m8192_3967 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 13391) + 1 = 2 ^ 1 * (41472 * q + 20087) := by ring
  have h_odd : (41472 * q + 20087) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 13391) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 20087) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 20087) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 20087) (by positivity)]

theorem step5_m8192_3967 (q : ℕ) : step (step (step (step (step (8192 * q + 3967))))) = 62208 * q + 30131 := by
  rw [step4_m8192_3967 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 20087) + 1 = 2 ^ 1 * (62208 * q + 30131) := by ring
  have h_odd : (62208 * q + 30131) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 20087) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 30131) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 30131) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 30131) (by positivity)]

theorem step6_m8192_3967 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3967)))))) = 93312 * q + 45197 := by
  rw [step5_m8192_3967 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 30131) + 1 = 2 ^ 1 * (93312 * q + 45197) := by ring
  have h_odd : (93312 * q + 45197) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 30131) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (93312 * q + 45197) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (93312 * q + 45197) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (93312 * q + 45197) (by positivity)]

theorem step7_m8192_3967 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3967))))))) = 34992 * q + 16949 := by
  rw [step6_m8192_3967 q]
  unfold step
  have h3n1 : 3 * (93312 * q + 45197) + 1 = 2 ^ 3 * (34992 * q + 16949) := by ring
  have h_odd : (34992 * q + 16949) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (93312 * q + 45197) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (34992 * q + 16949) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (34992 * q + 16949) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 16949) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3967 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3967 (q : ℕ) (hq : 8192 * q + 3967 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3967)))))))) < 8192 * q + 3967 := by
  rw [step7_m8192_3967 q]
  have h_bound : step (34992 * q + 16949) ≤ 6561 * q + 3178 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 16949) + 1 = 2 ^ 4 * (6561 * q + 3178) := by ring
    have hne : (6561 * q + 3178) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 16949) + 1) = 4 + ν₂ (6561 * q + 3178) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 3178) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3178) (2 ^ ν₂ (6561 * q + 3178)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_3977 (q : ℕ) : step (8192 * q + 3977) = 6144 * q + 2983 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 3977) + 1 = 2 ^ 2 * (6144 * q + 2983) := by ring
  have h_odd : (6144 * q + 2983) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 3977) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 2983) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 2983) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 2983) (by positivity)]

theorem step2_m8192_3977 (q : ℕ) : step (step (8192 * q + 3977)) = 9216 * q + 4475 := by
  rw [step_m8192_3977 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 2983) + 1 = 2 ^ 1 * (9216 * q + 4475) := by ring
  have h_odd : (9216 * q + 4475) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 2983) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 4475) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 4475) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4475) (by positivity)]

theorem step3_m8192_3977 (q : ℕ) : step (step (step (8192 * q + 3977))) = 13824 * q + 6713 := by
  rw [step2_m8192_3977 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4475) + 1 = 2 ^ 1 * (13824 * q + 6713) := by ring
  have h_odd : (13824 * q + 6713) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4475) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 6713) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 6713) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 6713) (by positivity)]

theorem step4_m8192_3977 (q : ℕ) : step (step (step (step (8192 * q + 3977)))) = 10368 * q + 5035 := by
  rw [step3_m8192_3977 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 6713) + 1 = 2 ^ 2 * (10368 * q + 5035) := by ring
  have h_odd : (10368 * q + 5035) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 6713) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 5035) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 5035) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 5035) (by positivity)]

theorem step5_m8192_3977 (q : ℕ) : step (step (step (step (step (8192 * q + 3977))))) = 15552 * q + 7553 := by
  rw [step4_m8192_3977 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 5035) + 1 = 2 ^ 1 * (15552 * q + 7553) := by ring
  have h_odd : (15552 * q + 7553) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 5035) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 7553) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 7553) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 7553) (by positivity)]

theorem step6_m8192_3977 (q : ℕ) : step (step (step (step (step (step (8192 * q + 3977)))))) = 11664 * q + 5665 := by
  rw [step5_m8192_3977 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 7553) + 1 = 2 ^ 2 * (11664 * q + 5665) := by ring
  have h_odd : (11664 * q + 5665) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 7553) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 5665) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 5665) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 5665) (by positivity)]

theorem step7_m8192_3977 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 3977))))))) = 8748 * q + 4249 := by
  rw [step6_m8192_3977 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 5665) + 1 = 2 ^ 2 * (8748 * q + 4249) := by ring
  have h_odd : (8748 * q + 4249) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 5665) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 4249) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 4249) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 4249) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 3977 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_3977 (q : ℕ) (hq : 8192 * q + 3977 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 3977)))))))) < 8192 * q + 3977 := by
  rw [step7_m8192_3977 q]
  have h_bound : step (8748 * q + 4249) ≤ 6561 * q + 3187 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 4249) + 1 = 2 ^ 2 * (6561 * q + 3187) := by ring
    have hne : (6561 * q + 3187) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 4249) + 1) = 2 + ν₂ (6561 * q + 3187) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3187) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3187) (2 ^ ν₂ (6561 * q + 3187)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4079 (q : ℕ) : step (8192 * q + 4079) = 12288 * q + 6119 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4079) + 1 = 2 ^ 1 * (12288 * q + 6119) := by ring
  have h_odd : (12288 * q + 6119) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4079) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6119) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6119) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6119) (by positivity)]

theorem step2_m8192_4079 (q : ℕ) : step (step (8192 * q + 4079)) = 18432 * q + 9179 := by
  rw [step_m8192_4079 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6119) + 1 = 2 ^ 1 * (18432 * q + 9179) := by ring
  have h_odd : (18432 * q + 9179) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6119) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 9179) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 9179) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 9179) (by positivity)]

theorem step3_m8192_4079 (q : ℕ) : step (step (step (8192 * q + 4079))) = 27648 * q + 13769 := by
  rw [step2_m8192_4079 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 9179) + 1 = 2 ^ 1 * (27648 * q + 13769) := by ring
  have h_odd : (27648 * q + 13769) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 9179) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 13769) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 13769) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 13769) (by positivity)]

theorem step4_m8192_4079 (q : ℕ) : step (step (step (step (8192 * q + 4079)))) = 20736 * q + 10327 := by
  rw [step3_m8192_4079 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 13769) + 1 = 2 ^ 2 * (20736 * q + 10327) := by ring
  have h_odd : (20736 * q + 10327) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 13769) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 10327) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 10327) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 10327) (by positivity)]

theorem step5_m8192_4079 (q : ℕ) : step (step (step (step (step (8192 * q + 4079))))) = 31104 * q + 15491 := by
  rw [step4_m8192_4079 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 10327) + 1 = 2 ^ 1 * (31104 * q + 15491) := by ring
  have h_odd : (31104 * q + 15491) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 10327) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 15491) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 15491) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 15491) (by positivity)]

theorem step6_m8192_4079 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4079)))))) = 46656 * q + 23237 := by
  rw [step5_m8192_4079 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 15491) + 1 = 2 ^ 1 * (46656 * q + 23237) := by ring
  have h_odd : (46656 * q + 23237) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 15491) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 23237) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 23237) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 23237) (by positivity)]

theorem step7_m8192_4079 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4079))))))) = 8748 * q + 4357 := by
  rw [step6_m8192_4079 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 23237) + 1 = 2 ^ 4 * (8748 * q + 4357) := by ring
  have h_odd : (8748 * q + 4357) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 23237) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (8748 * q + 4357) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (8748 * q + 4357) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 4357) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4079 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4079 (q : ℕ) (hq : 8192 * q + 4079 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4079)))))))) < 8192 * q + 4079 := by
  rw [step7_m8192_4079 q]
  have h_bound : step (8748 * q + 4357) ≤ 6561 * q + 3268 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 4357) + 1 = 2 ^ 2 * (6561 * q + 3268) := by ring
    have hne : (6561 * q + 3268) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 4357) + 1) = 2 + ν₂ (6561 * q + 3268) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3268) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3268) (2 ^ ν₂ (6561 * q + 3268)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4091 (q : ℕ) : step (8192 * q + 4091) = 12288 * q + 6137 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4091) + 1 = 2 ^ 1 * (12288 * q + 6137) := by ring
  have h_odd : (12288 * q + 6137) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4091) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6137) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6137) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6137) (by positivity)]

theorem step2_m8192_4091 (q : ℕ) : step (step (8192 * q + 4091)) = 9216 * q + 4603 := by
  rw [step_m8192_4091 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6137) + 1 = 2 ^ 2 * (9216 * q + 4603) := by ring
  have h_odd : (9216 * q + 4603) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6137) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 4603) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 4603) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4603) (by positivity)]

theorem step3_m8192_4091 (q : ℕ) : step (step (step (8192 * q + 4091))) = 13824 * q + 6905 := by
  rw [step2_m8192_4091 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4603) + 1 = 2 ^ 1 * (13824 * q + 6905) := by ring
  have h_odd : (13824 * q + 6905) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4603) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 6905) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 6905) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 6905) (by positivity)]

theorem step4_m8192_4091 (q : ℕ) : step (step (step (step (8192 * q + 4091)))) = 10368 * q + 5179 := by
  rw [step3_m8192_4091 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 6905) + 1 = 2 ^ 2 * (10368 * q + 5179) := by ring
  have h_odd : (10368 * q + 5179) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 6905) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 5179) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 5179) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 5179) (by positivity)]

theorem step5_m8192_4091 (q : ℕ) : step (step (step (step (step (8192 * q + 4091))))) = 15552 * q + 7769 := by
  rw [step4_m8192_4091 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 5179) + 1 = 2 ^ 1 * (15552 * q + 7769) := by ring
  have h_odd : (15552 * q + 7769) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 5179) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 7769) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 7769) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 7769) (by positivity)]

theorem step6_m8192_4091 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4091)))))) = 11664 * q + 5827 := by
  rw [step5_m8192_4091 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 7769) + 1 = 2 ^ 2 * (11664 * q + 5827) := by ring
  have h_odd : (11664 * q + 5827) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 7769) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 5827) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 5827) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 5827) (by positivity)]

theorem step7_m8192_4091 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4091))))))) = 17496 * q + 8741 := by
  rw [step6_m8192_4091 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 5827) + 1 = 2 ^ 1 * (17496 * q + 8741) := by ring
  have h_odd : (17496 * q + 8741) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 5827) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 8741) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 8741) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 8741) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4091 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4091 (q : ℕ) (hq : 8192 * q + 4091 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4091)))))))) < 8192 * q + 4091 := by
  rw [step7_m8192_4091 q]
  have h_bound : step (17496 * q + 8741) ≤ 6561 * q + 3278 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 8741) + 1 = 2 ^ 3 * (6561 * q + 3278) := by ring
    have hne : (6561 * q + 3278) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 8741) + 1) = 3 + ν₂ (6561 * q + 3278) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 3278) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3278) (2 ^ ν₂ (6561 * q + 3278)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4097 (q : ℕ) : step (8192 * q + 4097) = 6144 * q + 3073 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4097) + 1 = 2 ^ 2 * (6144 * q + 3073) := by ring
  have h_odd : (6144 * q + 3073) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4097) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 3073) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 3073) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3073) (by positivity)]

theorem step2_m8192_4097 (q : ℕ) : step (step (8192 * q + 4097)) = 4608 * q + 2305 := by
  rw [step_m8192_4097 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3073) + 1 = 2 ^ 2 * (4608 * q + 2305) := by ring
  have h_odd : (4608 * q + 2305) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3073) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 2305) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 2305) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 2305) (by positivity)]

theorem step3_m8192_4097 (q : ℕ) : step (step (step (8192 * q + 4097))) = 3456 * q + 1729 := by
  rw [step2_m8192_4097 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 2305) + 1 = 2 ^ 2 * (3456 * q + 1729) := by ring
  have h_odd : (3456 * q + 1729) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 2305) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3456 * q + 1729) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3456 * q + 1729) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3456 * q + 1729) (by positivity)]

theorem step4_m8192_4097 (q : ℕ) : step (step (step (step (8192 * q + 4097)))) = 2592 * q + 1297 := by
  rw [step3_m8192_4097 q]
  unfold step
  have h3n1 : 3 * (3456 * q + 1729) + 1 = 2 ^ 2 * (2592 * q + 1297) := by ring
  have h_odd : (2592 * q + 1297) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3456 * q + 1729) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (2592 * q + 1297) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (2592 * q + 1297) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2592 * q + 1297) (by positivity)]

theorem step5_m8192_4097 (q : ℕ) : step (step (step (step (step (8192 * q + 4097))))) = 1944 * q + 973 := by
  rw [step4_m8192_4097 q]
  unfold step
  have h3n1 : 3 * (2592 * q + 1297) + 1 = 2 ^ 2 * (1944 * q + 973) := by ring
  have h_odd : (1944 * q + 973) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2592 * q + 1297) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (1944 * q + 973) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (1944 * q + 973) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (1944 * q + 973) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4097 (mod 8192) ⇒ step^6(n) < n. -/
theorem descent_m8192_4097 (q : ℕ) (hq : 8192 * q + 4097 > 1) :
    step (step (step (step (step (step (8192 * q + 4097)))))) < 8192 * q + 4097 := by
  rw [step5_m8192_4097 q]
  have h_bound : step (1944 * q + 973) ≤ 729 * q + 365 := by
    unfold step
    have h3n1 : 3 * (1944 * q + 973) + 1 = 2 ^ 3 * (729 * q + 365) := by ring
    have hne : (729 * q + 365) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (1944 * q + 973) + 1) = 3 + ν₂ (729 * q + 365) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (729 * q + 365) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (729 * q + 365) (2 ^ ν₂ (729 * q + 365)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4159 (q : ℕ) : step (8192 * q + 4159) = 12288 * q + 6239 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4159) + 1 = 2 ^ 1 * (12288 * q + 6239) := by ring
  have h_odd : (12288 * q + 6239) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4159) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6239) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6239) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6239) (by positivity)]

theorem step2_m8192_4159 (q : ℕ) : step (step (8192 * q + 4159)) = 18432 * q + 9359 := by
  rw [step_m8192_4159 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6239) + 1 = 2 ^ 1 * (18432 * q + 9359) := by ring
  have h_odd : (18432 * q + 9359) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6239) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 9359) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 9359) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 9359) (by positivity)]

theorem step3_m8192_4159 (q : ℕ) : step (step (step (8192 * q + 4159))) = 27648 * q + 14039 := by
  rw [step2_m8192_4159 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 9359) + 1 = 2 ^ 1 * (27648 * q + 14039) := by ring
  have h_odd : (27648 * q + 14039) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 9359) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 14039) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 14039) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 14039) (by positivity)]

theorem step4_m8192_4159 (q : ℕ) : step (step (step (step (8192 * q + 4159)))) = 41472 * q + 21059 := by
  rw [step3_m8192_4159 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 14039) + 1 = 2 ^ 1 * (41472 * q + 21059) := by ring
  have h_odd : (41472 * q + 21059) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 14039) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 21059) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 21059) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 21059) (by positivity)]

theorem step5_m8192_4159 (q : ℕ) : step (step (step (step (step (8192 * q + 4159))))) = 62208 * q + 31589 := by
  rw [step4_m8192_4159 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 21059) + 1 = 2 ^ 1 * (62208 * q + 31589) := by ring
  have h_odd : (62208 * q + 31589) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 21059) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 31589) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 31589) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 31589) (by positivity)]

theorem step6_m8192_4159 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4159)))))) = 11664 * q + 5923 := by
  rw [step5_m8192_4159 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 31589) + 1 = 2 ^ 4 * (11664 * q + 5923) := by ring
  have h_odd : (11664 * q + 5923) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 31589) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (11664 * q + 5923) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (11664 * q + 5923) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 5923) (by positivity)]

theorem step7_m8192_4159 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4159))))))) = 17496 * q + 8885 := by
  rw [step6_m8192_4159 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 5923) + 1 = 2 ^ 1 * (17496 * q + 8885) := by ring
  have h_odd : (17496 * q + 8885) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 5923) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 8885) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 8885) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 8885) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4159 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4159 (q : ℕ) (hq : 8192 * q + 4159 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4159)))))))) < 8192 * q + 4159 := by
  rw [step7_m8192_4159 q]
  have h_bound : step (17496 * q + 8885) ≤ 6561 * q + 3332 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 8885) + 1 = 2 ^ 3 * (6561 * q + 3332) := by ring
    have hne : (6561 * q + 3332) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 8885) + 1) = 3 + ν₂ (6561 * q + 3332) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 3332) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3332) (2 ^ ν₂ (6561 * q + 3332)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4199 (q : ℕ) : step (8192 * q + 4199) = 12288 * q + 6299 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4199) + 1 = 2 ^ 1 * (12288 * q + 6299) := by ring
  have h_odd : (12288 * q + 6299) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4199) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6299) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6299) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6299) (by positivity)]

theorem step2_m8192_4199 (q : ℕ) : step (step (8192 * q + 4199)) = 18432 * q + 9449 := by
  rw [step_m8192_4199 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6299) + 1 = 2 ^ 1 * (18432 * q + 9449) := by ring
  have h_odd : (18432 * q + 9449) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6299) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 9449) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 9449) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 9449) (by positivity)]

theorem step3_m8192_4199 (q : ℕ) : step (step (step (8192 * q + 4199))) = 13824 * q + 7087 := by
  rw [step2_m8192_4199 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 9449) + 1 = 2 ^ 2 * (13824 * q + 7087) := by ring
  have h_odd : (13824 * q + 7087) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 9449) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 7087) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 7087) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 7087) (by positivity)]

theorem step4_m8192_4199 (q : ℕ) : step (step (step (step (8192 * q + 4199)))) = 20736 * q + 10631 := by
  rw [step3_m8192_4199 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 7087) + 1 = 2 ^ 1 * (20736 * q + 10631) := by ring
  have h_odd : (20736 * q + 10631) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 7087) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 10631) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 10631) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 10631) (by positivity)]

theorem step5_m8192_4199 (q : ℕ) : step (step (step (step (step (8192 * q + 4199))))) = 31104 * q + 15947 := by
  rw [step4_m8192_4199 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 10631) + 1 = 2 ^ 1 * (31104 * q + 15947) := by ring
  have h_odd : (31104 * q + 15947) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 10631) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 15947) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 15947) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 15947) (by positivity)]

theorem step6_m8192_4199 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4199)))))) = 46656 * q + 23921 := by
  rw [step5_m8192_4199 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 15947) + 1 = 2 ^ 1 * (46656 * q + 23921) := by ring
  have h_odd : (46656 * q + 23921) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 15947) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 23921) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 23921) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 23921) (by positivity)]

theorem step7_m8192_4199 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4199))))))) = 34992 * q + 17941 := by
  rw [step6_m8192_4199 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 23921) + 1 = 2 ^ 2 * (34992 * q + 17941) := by ring
  have h_odd : (34992 * q + 17941) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 23921) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (34992 * q + 17941) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (34992 * q + 17941) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 17941) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4199 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4199 (q : ℕ) (hq : 8192 * q + 4199 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4199)))))))) < 8192 * q + 4199 := by
  rw [step7_m8192_4199 q]
  have h_bound : step (34992 * q + 17941) ≤ 6561 * q + 3364 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 17941) + 1 = 2 ^ 4 * (6561 * q + 3364) := by ring
    have hne : (6561 * q + 3364) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 17941) + 1) = 4 + ν₂ (6561 * q + 3364) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 3364) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3364) (2 ^ ν₂ (6561 * q + 3364)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4223 (q : ℕ) : step (8192 * q + 4223) = 12288 * q + 6335 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4223) + 1 = 2 ^ 1 * (12288 * q + 6335) := by ring
  have h_odd : (12288 * q + 6335) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4223) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6335) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6335) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6335) (by positivity)]

theorem step2_m8192_4223 (q : ℕ) : step (step (8192 * q + 4223)) = 18432 * q + 9503 := by
  rw [step_m8192_4223 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6335) + 1 = 2 ^ 1 * (18432 * q + 9503) := by ring
  have h_odd : (18432 * q + 9503) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6335) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 9503) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 9503) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 9503) (by positivity)]

theorem step3_m8192_4223 (q : ℕ) : step (step (step (8192 * q + 4223))) = 27648 * q + 14255 := by
  rw [step2_m8192_4223 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 9503) + 1 = 2 ^ 1 * (27648 * q + 14255) := by ring
  have h_odd : (27648 * q + 14255) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 9503) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 14255) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 14255) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 14255) (by positivity)]

theorem step4_m8192_4223 (q : ℕ) : step (step (step (step (8192 * q + 4223)))) = 41472 * q + 21383 := by
  rw [step3_m8192_4223 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 14255) + 1 = 2 ^ 1 * (41472 * q + 21383) := by ring
  have h_odd : (41472 * q + 21383) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 14255) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 21383) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 21383) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 21383) (by positivity)]

theorem step5_m8192_4223 (q : ℕ) : step (step (step (step (step (8192 * q + 4223))))) = 62208 * q + 32075 := by
  rw [step4_m8192_4223 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 21383) + 1 = 2 ^ 1 * (62208 * q + 32075) := by ring
  have h_odd : (62208 * q + 32075) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 21383) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 32075) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 32075) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 32075) (by positivity)]

theorem step6_m8192_4223 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4223)))))) = 93312 * q + 48113 := by
  rw [step5_m8192_4223 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 32075) + 1 = 2 ^ 1 * (93312 * q + 48113) := by ring
  have h_odd : (93312 * q + 48113) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 32075) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (93312 * q + 48113) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (93312 * q + 48113) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (93312 * q + 48113) (by positivity)]

theorem step7_m8192_4223 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4223))))))) = 69984 * q + 36085 := by
  rw [step6_m8192_4223 q]
  unfold step
  have h3n1 : 3 * (93312 * q + 48113) + 1 = 2 ^ 2 * (69984 * q + 36085) := by ring
  have h_odd : (69984 * q + 36085) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (93312 * q + 48113) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (69984 * q + 36085) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (69984 * q + 36085) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (69984 * q + 36085) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4223 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4223 (q : ℕ) (hq : 8192 * q + 4223 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4223)))))))) < 8192 * q + 4223 := by
  rw [step7_m8192_4223 q]
  have h_bound : step (69984 * q + 36085) ≤ 6561 * q + 3383 := by
    unfold step
    have h3n1 : 3 * (69984 * q + 36085) + 1 = 2 ^ 5 * (6561 * q + 3383) := by ring
    have hne : (6561 * q + 3383) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (69984 * q + 36085) + 1) = 5 + ν₂ (6561 * q + 3383) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (6561 * q + 3383) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3383) (2 ^ ν₂ (6561 * q + 3383)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4251 (q : ℕ) : step (8192 * q + 4251) = 12288 * q + 6377 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4251) + 1 = 2 ^ 1 * (12288 * q + 6377) := by ring
  have h_odd : (12288 * q + 6377) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4251) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6377) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6377) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6377) (by positivity)]

theorem step2_m8192_4251 (q : ℕ) : step (step (8192 * q + 4251)) = 9216 * q + 4783 := by
  rw [step_m8192_4251 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6377) + 1 = 2 ^ 2 * (9216 * q + 4783) := by ring
  have h_odd : (9216 * q + 4783) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6377) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 4783) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 4783) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4783) (by positivity)]

theorem step3_m8192_4251 (q : ℕ) : step (step (step (8192 * q + 4251))) = 13824 * q + 7175 := by
  rw [step2_m8192_4251 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4783) + 1 = 2 ^ 1 * (13824 * q + 7175) := by ring
  have h_odd : (13824 * q + 7175) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4783) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 7175) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 7175) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 7175) (by positivity)]

theorem step4_m8192_4251 (q : ℕ) : step (step (step (step (8192 * q + 4251)))) = 20736 * q + 10763 := by
  rw [step3_m8192_4251 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 7175) + 1 = 2 ^ 1 * (20736 * q + 10763) := by ring
  have h_odd : (20736 * q + 10763) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 7175) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 10763) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 10763) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 10763) (by positivity)]

theorem step5_m8192_4251 (q : ℕ) : step (step (step (step (step (8192 * q + 4251))))) = 31104 * q + 16145 := by
  rw [step4_m8192_4251 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 10763) + 1 = 2 ^ 1 * (31104 * q + 16145) := by ring
  have h_odd : (31104 * q + 16145) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 10763) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 16145) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 16145) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 16145) (by positivity)]

theorem step6_m8192_4251 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4251)))))) = 23328 * q + 12109 := by
  rw [step5_m8192_4251 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 16145) + 1 = 2 ^ 2 * (23328 * q + 12109) := by ring
  have h_odd : (23328 * q + 12109) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 16145) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 12109) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 12109) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 12109) (by positivity)]

theorem step7_m8192_4251 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4251))))))) = 8748 * q + 4541 := by
  rw [step6_m8192_4251 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 12109) + 1 = 2 ^ 3 * (8748 * q + 4541) := by ring
  have h_odd : (8748 * q + 4541) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 12109) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 4541) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 4541) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 4541) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4251 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4251 (q : ℕ) (hq : 8192 * q + 4251 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4251)))))))) < 8192 * q + 4251 := by
  rw [step7_m8192_4251 q]
  have h_bound : step (8748 * q + 4541) ≤ 6561 * q + 3406 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 4541) + 1 = 2 ^ 2 * (6561 * q + 3406) := by ring
    have hne : (6561 * q + 3406) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 4541) + 1) = 2 + ν₂ (6561 * q + 3406) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3406) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3406) (2 ^ ν₂ (6561 * q + 3406)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4393 (q : ℕ) : step (8192 * q + 4393) = 6144 * q + 3295 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4393) + 1 = 2 ^ 2 * (6144 * q + 3295) := by ring
  have h_odd : (6144 * q + 3295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4393) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 3295) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 3295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3295) (by positivity)]

theorem step2_m8192_4393 (q : ℕ) : step (step (8192 * q + 4393)) = 9216 * q + 4943 := by
  rw [step_m8192_4393 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3295) + 1 = 2 ^ 1 * (9216 * q + 4943) := by ring
  have h_odd : (9216 * q + 4943) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 4943) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 4943) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4943) (by positivity)]

theorem step3_m8192_4393 (q : ℕ) : step (step (step (8192 * q + 4393))) = 13824 * q + 7415 := by
  rw [step2_m8192_4393 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4943) + 1 = 2 ^ 1 * (13824 * q + 7415) := by ring
  have h_odd : (13824 * q + 7415) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4943) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 7415) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 7415) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 7415) (by positivity)]

theorem step4_m8192_4393 (q : ℕ) : step (step (step (step (8192 * q + 4393)))) = 20736 * q + 11123 := by
  rw [step3_m8192_4393 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 7415) + 1 = 2 ^ 1 * (20736 * q + 11123) := by ring
  have h_odd : (20736 * q + 11123) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 7415) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 11123) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 11123) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 11123) (by positivity)]

theorem step5_m8192_4393 (q : ℕ) : step (step (step (step (step (8192 * q + 4393))))) = 31104 * q + 16685 := by
  rw [step4_m8192_4393 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 11123) + 1 = 2 ^ 1 * (31104 * q + 16685) := by ring
  have h_odd : (31104 * q + 16685) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 11123) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 16685) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 16685) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 16685) (by positivity)]

theorem step6_m8192_4393 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4393)))))) = 11664 * q + 6257 := by
  rw [step5_m8192_4393 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 16685) + 1 = 2 ^ 3 * (11664 * q + 6257) := by ring
  have h_odd : (11664 * q + 6257) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 16685) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 6257) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 6257) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 6257) (by positivity)]

theorem step7_m8192_4393 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4393))))))) = 8748 * q + 4693 := by
  rw [step6_m8192_4393 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 6257) + 1 = 2 ^ 2 * (8748 * q + 4693) := by ring
  have h_odd : (8748 * q + 4693) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 6257) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 4693) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 4693) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 4693) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4393 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4393 (q : ℕ) (hq : 8192 * q + 4393 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4393)))))))) < 8192 * q + 4393 := by
  rw [step7_m8192_4393 q]
  have h_bound : step (8748 * q + 4693) ≤ 6561 * q + 3520 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 4693) + 1 = 2 ^ 2 * (6561 * q + 3520) := by ring
    have hne : (6561 * q + 3520) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 4693) + 1) = 2 + ν₂ (6561 * q + 3520) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3520) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3520) (2 ^ ν₂ (6561 * q + 3520)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4455 (q : ℕ) : step (8192 * q + 4455) = 12288 * q + 6683 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4455) + 1 = 2 ^ 1 * (12288 * q + 6683) := by ring
  have h_odd : (12288 * q + 6683) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4455) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6683) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6683) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6683) (by positivity)]

theorem step2_m8192_4455 (q : ℕ) : step (step (8192 * q + 4455)) = 18432 * q + 10025 := by
  rw [step_m8192_4455 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6683) + 1 = 2 ^ 1 * (18432 * q + 10025) := by ring
  have h_odd : (18432 * q + 10025) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6683) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 10025) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 10025) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 10025) (by positivity)]

theorem step3_m8192_4455 (q : ℕ) : step (step (step (8192 * q + 4455))) = 13824 * q + 7519 := by
  rw [step2_m8192_4455 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 10025) + 1 = 2 ^ 2 * (13824 * q + 7519) := by ring
  have h_odd : (13824 * q + 7519) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 10025) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 7519) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 7519) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 7519) (by positivity)]

theorem step4_m8192_4455 (q : ℕ) : step (step (step (step (8192 * q + 4455)))) = 20736 * q + 11279 := by
  rw [step3_m8192_4455 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 7519) + 1 = 2 ^ 1 * (20736 * q + 11279) := by ring
  have h_odd : (20736 * q + 11279) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 7519) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 11279) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 11279) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 11279) (by positivity)]

theorem step5_m8192_4455 (q : ℕ) : step (step (step (step (step (8192 * q + 4455))))) = 31104 * q + 16919 := by
  rw [step4_m8192_4455 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 11279) + 1 = 2 ^ 1 * (31104 * q + 16919) := by ring
  have h_odd : (31104 * q + 16919) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 11279) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 16919) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 16919) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 16919) (by positivity)]

theorem step6_m8192_4455 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4455)))))) = 46656 * q + 25379 := by
  rw [step5_m8192_4455 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 16919) + 1 = 2 ^ 1 * (46656 * q + 25379) := by ring
  have h_odd : (46656 * q + 25379) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 16919) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 25379) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 25379) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 25379) (by positivity)]

theorem step7_m8192_4455 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4455))))))) = 69984 * q + 38069 := by
  rw [step6_m8192_4455 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 25379) + 1 = 2 ^ 1 * (69984 * q + 38069) := by ring
  have h_odd : (69984 * q + 38069) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 25379) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (69984 * q + 38069) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (69984 * q + 38069) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (69984 * q + 38069) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4455 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4455 (q : ℕ) (hq : 8192 * q + 4455 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4455)))))))) < 8192 * q + 4455 := by
  rw [step7_m8192_4455 q]
  have h_bound : step (69984 * q + 38069) ≤ 6561 * q + 3569 := by
    unfold step
    have h3n1 : 3 * (69984 * q + 38069) + 1 = 2 ^ 5 * (6561 * q + 3569) := by ring
    have hne : (6561 * q + 3569) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (69984 * q + 38069) + 1) = 5 + ν₂ (6561 * q + 3569) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (6561 * q + 3569) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3569) (2 ^ ν₂ (6561 * q + 3569)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4507 (q : ℕ) : step (8192 * q + 4507) = 12288 * q + 6761 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4507) + 1 = 2 ^ 1 * (12288 * q + 6761) := by ring
  have h_odd : (12288 * q + 6761) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4507) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 6761) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 6761) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6761) (by positivity)]

theorem step2_m8192_4507 (q : ℕ) : step (step (8192 * q + 4507)) = 9216 * q + 5071 := by
  rw [step_m8192_4507 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6761) + 1 = 2 ^ 2 * (9216 * q + 5071) := by ring
  have h_odd : (9216 * q + 5071) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6761) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 5071) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 5071) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5071) (by positivity)]

theorem step3_m8192_4507 (q : ℕ) : step (step (step (8192 * q + 4507))) = 13824 * q + 7607 := by
  rw [step2_m8192_4507 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5071) + 1 = 2 ^ 1 * (13824 * q + 7607) := by ring
  have h_odd : (13824 * q + 7607) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5071) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 7607) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 7607) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 7607) (by positivity)]

theorem step4_m8192_4507 (q : ℕ) : step (step (step (step (8192 * q + 4507)))) = 20736 * q + 11411 := by
  rw [step3_m8192_4507 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 7607) + 1 = 2 ^ 1 * (20736 * q + 11411) := by ring
  have h_odd : (20736 * q + 11411) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 7607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 11411) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 11411) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 11411) (by positivity)]

theorem step5_m8192_4507 (q : ℕ) : step (step (step (step (step (8192 * q + 4507))))) = 31104 * q + 17117 := by
  rw [step4_m8192_4507 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 11411) + 1 = 2 ^ 1 * (31104 * q + 17117) := by ring
  have h_odd : (31104 * q + 17117) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 11411) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 17117) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 17117) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 17117) (by positivity)]

theorem step6_m8192_4507 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4507)))))) = 11664 * q + 6419 := by
  rw [step5_m8192_4507 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 17117) + 1 = 2 ^ 3 * (11664 * q + 6419) := by ring
  have h_odd : (11664 * q + 6419) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 17117) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 6419) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 6419) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 6419) (by positivity)]

theorem step7_m8192_4507 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4507))))))) = 17496 * q + 9629 := by
  rw [step6_m8192_4507 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 6419) + 1 = 2 ^ 1 * (17496 * q + 9629) := by ring
  have h_odd : (17496 * q + 9629) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 6419) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 9629) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 9629) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 9629) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4507 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4507 (q : ℕ) (hq : 8192 * q + 4507 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4507)))))))) < 8192 * q + 4507 := by
  rw [step7_m8192_4507 q]
  have h_bound : step (17496 * q + 9629) ≤ 6561 * q + 3611 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 9629) + 1 = 2 ^ 3 * (6561 * q + 3611) := by ring
    have hne : (6561 * q + 3611) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 9629) + 1) = 3 + ν₂ (6561 * q + 3611) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 3611) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3611) (2 ^ ν₂ (6561 * q + 3611)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4745 (q : ℕ) : step (8192 * q + 4745) = 6144 * q + 3559 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4745) + 1 = 2 ^ 2 * (6144 * q + 3559) := by ring
  have h_odd : (6144 * q + 3559) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4745) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 3559) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 3559) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3559) (by positivity)]

theorem step2_m8192_4745 (q : ℕ) : step (step (8192 * q + 4745)) = 9216 * q + 5339 := by
  rw [step_m8192_4745 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3559) + 1 = 2 ^ 1 * (9216 * q + 5339) := by ring
  have h_odd : (9216 * q + 5339) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 5339) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 5339) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5339) (by positivity)]

theorem step3_m8192_4745 (q : ℕ) : step (step (step (8192 * q + 4745))) = 13824 * q + 8009 := by
  rw [step2_m8192_4745 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5339) + 1 = 2 ^ 1 * (13824 * q + 8009) := by ring
  have h_odd : (13824 * q + 8009) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5339) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 8009) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 8009) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8009) (by positivity)]

theorem step4_m8192_4745 (q : ℕ) : step (step (step (step (8192 * q + 4745)))) = 10368 * q + 6007 := by
  rw [step3_m8192_4745 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8009) + 1 = 2 ^ 2 * (10368 * q + 6007) := by ring
  have h_odd : (10368 * q + 6007) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8009) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 6007) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 6007) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 6007) (by positivity)]

theorem step5_m8192_4745 (q : ℕ) : step (step (step (step (step (8192 * q + 4745))))) = 15552 * q + 9011 := by
  rw [step4_m8192_4745 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 6007) + 1 = 2 ^ 1 * (15552 * q + 9011) := by ring
  have h_odd : (15552 * q + 9011) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 6007) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 9011) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 9011) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9011) (by positivity)]

theorem step6_m8192_4745 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4745)))))) = 23328 * q + 13517 := by
  rw [step5_m8192_4745 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9011) + 1 = 2 ^ 1 * (23328 * q + 13517) := by ring
  have h_odd : (23328 * q + 13517) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9011) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 13517) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 13517) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 13517) (by positivity)]

theorem step7_m8192_4745 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4745))))))) = 8748 * q + 5069 := by
  rw [step6_m8192_4745 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 13517) + 1 = 2 ^ 3 * (8748 * q + 5069) := by ring
  have h_odd : (8748 * q + 5069) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 13517) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 5069) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 5069) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 5069) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4745 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4745 (q : ℕ) (hq : 8192 * q + 4745 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4745)))))))) < 8192 * q + 4745 := by
  rw [step7_m8192_4745 q]
  have h_bound : step (8748 * q + 5069) ≤ 6561 * q + 3802 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 5069) + 1 = 2 ^ 2 * (6561 * q + 3802) := by ring
    have hne : (6561 * q + 3802) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 5069) + 1) = 2 + ν₂ (6561 * q + 3802) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3802) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3802) (2 ^ ν₂ (6561 * q + 3802)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4859 (q : ℕ) : step (8192 * q + 4859) = 12288 * q + 7289 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4859) + 1 = 2 ^ 1 * (12288 * q + 7289) := by ring
  have h_odd : (12288 * q + 7289) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4859) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 7289) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 7289) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 7289) (by positivity)]

theorem step2_m8192_4859 (q : ℕ) : step (step (8192 * q + 4859)) = 9216 * q + 5467 := by
  rw [step_m8192_4859 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 7289) + 1 = 2 ^ 2 * (9216 * q + 5467) := by ring
  have h_odd : (9216 * q + 5467) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 7289) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 5467) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 5467) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5467) (by positivity)]

theorem step3_m8192_4859 (q : ℕ) : step (step (step (8192 * q + 4859))) = 13824 * q + 8201 := by
  rw [step2_m8192_4859 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5467) + 1 = 2 ^ 1 * (13824 * q + 8201) := by ring
  have h_odd : (13824 * q + 8201) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5467) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 8201) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 8201) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8201) (by positivity)]

theorem step4_m8192_4859 (q : ℕ) : step (step (step (step (8192 * q + 4859)))) = 10368 * q + 6151 := by
  rw [step3_m8192_4859 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8201) + 1 = 2 ^ 2 * (10368 * q + 6151) := by ring
  have h_odd : (10368 * q + 6151) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8201) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 6151) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 6151) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 6151) (by positivity)]

theorem step5_m8192_4859 (q : ℕ) : step (step (step (step (step (8192 * q + 4859))))) = 15552 * q + 9227 := by
  rw [step4_m8192_4859 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 6151) + 1 = 2 ^ 1 * (15552 * q + 9227) := by ring
  have h_odd : (15552 * q + 9227) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 6151) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 9227) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 9227) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9227) (by positivity)]

theorem step6_m8192_4859 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4859)))))) = 23328 * q + 13841 := by
  rw [step5_m8192_4859 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9227) + 1 = 2 ^ 1 * (23328 * q + 13841) := by ring
  have h_odd : (23328 * q + 13841) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9227) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 13841) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 13841) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 13841) (by positivity)]

theorem step7_m8192_4859 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4859))))))) = 17496 * q + 10381 := by
  rw [step6_m8192_4859 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 13841) + 1 = 2 ^ 2 * (17496 * q + 10381) := by ring
  have h_odd : (17496 * q + 10381) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 13841) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 10381) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 10381) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 10381) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4859 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4859 (q : ℕ) (hq : 8192 * q + 4859 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4859)))))))) < 8192 * q + 4859 := by
  rw [step7_m8192_4859 q]
  have h_bound : step (17496 * q + 10381) ≤ 6561 * q + 3893 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 10381) + 1 = 2 ^ 3 * (6561 * q + 3893) := by ring
    have hne : (6561 * q + 3893) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 10381) + 1) = 3 + ν₂ (6561 * q + 3893) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 3893) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3893) (2 ^ ν₂ (6561 * q + 3893)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4927 (q : ℕ) : step (8192 * q + 4927) = 12288 * q + 7391 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4927) + 1 = 2 ^ 1 * (12288 * q + 7391) := by ring
  have h_odd : (12288 * q + 7391) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4927) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 7391) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 7391) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 7391) (by positivity)]

theorem step2_m8192_4927 (q : ℕ) : step (step (8192 * q + 4927)) = 18432 * q + 11087 := by
  rw [step_m8192_4927 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 7391) + 1 = 2 ^ 1 * (18432 * q + 11087) := by ring
  have h_odd : (18432 * q + 11087) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 7391) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 11087) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 11087) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 11087) (by positivity)]

theorem step3_m8192_4927 (q : ℕ) : step (step (step (8192 * q + 4927))) = 27648 * q + 16631 := by
  rw [step2_m8192_4927 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 11087) + 1 = 2 ^ 1 * (27648 * q + 16631) := by ring
  have h_odd : (27648 * q + 16631) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 11087) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 16631) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 16631) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 16631) (by positivity)]

theorem step4_m8192_4927 (q : ℕ) : step (step (step (step (8192 * q + 4927)))) = 41472 * q + 24947 := by
  rw [step3_m8192_4927 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 16631) + 1 = 2 ^ 1 * (41472 * q + 24947) := by ring
  have h_odd : (41472 * q + 24947) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 16631) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 24947) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 24947) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 24947) (by positivity)]

theorem step5_m8192_4927 (q : ℕ) : step (step (step (step (step (8192 * q + 4927))))) = 62208 * q + 37421 := by
  rw [step4_m8192_4927 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 24947) + 1 = 2 ^ 1 * (62208 * q + 37421) := by ring
  have h_odd : (62208 * q + 37421) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 24947) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 37421) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 37421) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 37421) (by positivity)]

theorem step6_m8192_4927 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4927)))))) = 23328 * q + 14033 := by
  rw [step5_m8192_4927 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 37421) + 1 = 2 ^ 3 * (23328 * q + 14033) := by ring
  have h_odd : (23328 * q + 14033) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 37421) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (23328 * q + 14033) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (23328 * q + 14033) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 14033) (by positivity)]

theorem step7_m8192_4927 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4927))))))) = 17496 * q + 10525 := by
  rw [step6_m8192_4927 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 14033) + 1 = 2 ^ 2 * (17496 * q + 10525) := by ring
  have h_odd : (17496 * q + 10525) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 14033) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 10525) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 10525) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 10525) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4927 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4927 (q : ℕ) (hq : 8192 * q + 4927 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4927)))))))) < 8192 * q + 4927 := by
  rw [step7_m8192_4927 q]
  have h_bound : step (17496 * q + 10525) ≤ 6561 * q + 3947 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 10525) + 1 = 2 ^ 3 * (6561 * q + 3947) := by ring
    have hne : (6561 * q + 3947) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 10525) + 1) = 3 + ν₂ (6561 * q + 3947) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 3947) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3947) (2 ^ ν₂ (6561 * q + 3947)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_4955 (q : ℕ) : step (8192 * q + 4955) = 12288 * q + 7433 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 4955) + 1 = 2 ^ 1 * (12288 * q + 7433) := by ring
  have h_odd : (12288 * q + 7433) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 4955) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 7433) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 7433) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 7433) (by positivity)]

theorem step2_m8192_4955 (q : ℕ) : step (step (8192 * q + 4955)) = 9216 * q + 5575 := by
  rw [step_m8192_4955 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 7433) + 1 = 2 ^ 2 * (9216 * q + 5575) := by ring
  have h_odd : (9216 * q + 5575) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 7433) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 5575) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 5575) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5575) (by positivity)]

theorem step3_m8192_4955 (q : ℕ) : step (step (step (8192 * q + 4955))) = 13824 * q + 8363 := by
  rw [step2_m8192_4955 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5575) + 1 = 2 ^ 1 * (13824 * q + 8363) := by ring
  have h_odd : (13824 * q + 8363) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5575) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 8363) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 8363) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8363) (by positivity)]

theorem step4_m8192_4955 (q : ℕ) : step (step (step (step (8192 * q + 4955)))) = 20736 * q + 12545 := by
  rw [step3_m8192_4955 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8363) + 1 = 2 ^ 1 * (20736 * q + 12545) := by ring
  have h_odd : (20736 * q + 12545) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8363) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 12545) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 12545) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 12545) (by positivity)]

theorem step5_m8192_4955 (q : ℕ) : step (step (step (step (step (8192 * q + 4955))))) = 15552 * q + 9409 := by
  rw [step4_m8192_4955 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 12545) + 1 = 2 ^ 2 * (15552 * q + 9409) := by ring
  have h_odd : (15552 * q + 9409) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 12545) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 9409) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 9409) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9409) (by positivity)]

theorem step6_m8192_4955 (q : ℕ) : step (step (step (step (step (step (8192 * q + 4955)))))) = 11664 * q + 7057 := by
  rw [step5_m8192_4955 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9409) + 1 = 2 ^ 2 * (11664 * q + 7057) := by ring
  have h_odd : (11664 * q + 7057) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9409) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 7057) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 7057) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7057) (by positivity)]

theorem step7_m8192_4955 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 4955))))))) = 8748 * q + 5293 := by
  rw [step6_m8192_4955 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 7057) + 1 = 2 ^ 2 * (8748 * q + 5293) := by ring
  have h_odd : (8748 * q + 5293) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 7057) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 5293) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 5293) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 5293) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 4955 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_4955 (q : ℕ) (hq : 8192 * q + 4955 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 4955)))))))) < 8192 * q + 4955 := by
  rw [step7_m8192_4955 q]
  have h_bound : step (8748 * q + 5293) ≤ 6561 * q + 3970 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 5293) + 1 = 2 ^ 2 * (6561 * q + 3970) := by ring
    have hne : (6561 * q + 3970) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 5293) + 1) = 2 + ν₂ (6561 * q + 3970) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 3970) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3970) (2 ^ ν₂ (6561 * q + 3970)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5001 (q : ℕ) : step (8192 * q + 5001) = 6144 * q + 3751 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5001) + 1 = 2 ^ 2 * (6144 * q + 3751) := by ring
  have h_odd : (6144 * q + 3751) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5001) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 3751) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 3751) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3751) (by positivity)]

theorem step2_m8192_5001 (q : ℕ) : step (step (8192 * q + 5001)) = 9216 * q + 5627 := by
  rw [step_m8192_5001 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3751) + 1 = 2 ^ 1 * (9216 * q + 5627) := by ring
  have h_odd : (9216 * q + 5627) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3751) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 5627) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 5627) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5627) (by positivity)]

theorem step3_m8192_5001 (q : ℕ) : step (step (step (8192 * q + 5001))) = 13824 * q + 8441 := by
  rw [step2_m8192_5001 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5627) + 1 = 2 ^ 1 * (13824 * q + 8441) := by ring
  have h_odd : (13824 * q + 8441) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5627) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 8441) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 8441) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8441) (by positivity)]

theorem step4_m8192_5001 (q : ℕ) : step (step (step (step (8192 * q + 5001)))) = 10368 * q + 6331 := by
  rw [step3_m8192_5001 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8441) + 1 = 2 ^ 2 * (10368 * q + 6331) := by ring
  have h_odd : (10368 * q + 6331) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8441) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 6331) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 6331) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 6331) (by positivity)]

theorem step5_m8192_5001 (q : ℕ) : step (step (step (step (step (8192 * q + 5001))))) = 15552 * q + 9497 := by
  rw [step4_m8192_5001 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 6331) + 1 = 2 ^ 1 * (15552 * q + 9497) := by ring
  have h_odd : (15552 * q + 9497) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 6331) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 9497) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 9497) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9497) (by positivity)]

theorem step6_m8192_5001 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5001)))))) = 11664 * q + 7123 := by
  rw [step5_m8192_5001 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9497) + 1 = 2 ^ 2 * (11664 * q + 7123) := by ring
  have h_odd : (11664 * q + 7123) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9497) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 7123) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 7123) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7123) (by positivity)]

theorem step7_m8192_5001 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5001))))))) = 17496 * q + 10685 := by
  rw [step6_m8192_5001 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 7123) + 1 = 2 ^ 1 * (17496 * q + 10685) := by ring
  have h_odd : (17496 * q + 10685) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 7123) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 10685) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 10685) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 10685) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5001 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5001 (q : ℕ) (hq : 8192 * q + 5001 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5001)))))))) < 8192 * q + 5001 := by
  rw [step7_m8192_5001 q]
  have h_bound : step (17496 * q + 10685) ≤ 6561 * q + 4007 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 10685) + 1 = 2 ^ 3 * (6561 * q + 4007) := by ring
    have hne : (6561 * q + 4007) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 10685) + 1) = 3 + ν₂ (6561 * q + 4007) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4007) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4007) (2 ^ ν₂ (6561 * q + 4007)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5023 (q : ℕ) : step (8192 * q + 5023) = 12288 * q + 7535 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5023) + 1 = 2 ^ 1 * (12288 * q + 7535) := by ring
  have h_odd : (12288 * q + 7535) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5023) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 7535) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 7535) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 7535) (by positivity)]

theorem step2_m8192_5023 (q : ℕ) : step (step (8192 * q + 5023)) = 18432 * q + 11303 := by
  rw [step_m8192_5023 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 7535) + 1 = 2 ^ 1 * (18432 * q + 11303) := by ring
  have h_odd : (18432 * q + 11303) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 7535) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 11303) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 11303) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 11303) (by positivity)]

theorem step3_m8192_5023 (q : ℕ) : step (step (step (8192 * q + 5023))) = 27648 * q + 16955 := by
  rw [step2_m8192_5023 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 11303) + 1 = 2 ^ 1 * (27648 * q + 16955) := by ring
  have h_odd : (27648 * q + 16955) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 11303) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 16955) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 16955) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 16955) (by positivity)]

theorem step4_m8192_5023 (q : ℕ) : step (step (step (step (8192 * q + 5023)))) = 41472 * q + 25433 := by
  rw [step3_m8192_5023 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 16955) + 1 = 2 ^ 1 * (41472 * q + 25433) := by ring
  have h_odd : (41472 * q + 25433) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 16955) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 25433) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 25433) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 25433) (by positivity)]

theorem step5_m8192_5023 (q : ℕ) : step (step (step (step (step (8192 * q + 5023))))) = 31104 * q + 19075 := by
  rw [step4_m8192_5023 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 25433) + 1 = 2 ^ 2 * (31104 * q + 19075) := by ring
  have h_odd : (31104 * q + 19075) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 25433) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 19075) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 19075) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 19075) (by positivity)]

theorem step6_m8192_5023 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5023)))))) = 46656 * q + 28613 := by
  rw [step5_m8192_5023 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 19075) + 1 = 2 ^ 1 * (46656 * q + 28613) := by ring
  have h_odd : (46656 * q + 28613) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 19075) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 28613) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 28613) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 28613) (by positivity)]

theorem step7_m8192_5023 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5023))))))) = 8748 * q + 5365 := by
  rw [step6_m8192_5023 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 28613) + 1 = 2 ^ 4 * (8748 * q + 5365) := by ring
  have h_odd : (8748 * q + 5365) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 28613) + 1) = 4 := by
    rw [h3n1, ν₂_mul (2 ^ 4) (8748 * q + 5365) (by positivity) (by omega),
        ν₂_pow_two' 4, ν₂_odd (8748 * q + 5365) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 5365) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5023 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5023 (q : ℕ) (hq : 8192 * q + 5023 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5023)))))))) < 8192 * q + 5023 := by
  rw [step7_m8192_5023 q]
  have h_bound : step (8748 * q + 5365) ≤ 6561 * q + 4024 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 5365) + 1 = 2 ^ 2 * (6561 * q + 4024) := by ring
    have hne : (6561 * q + 4024) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 5365) + 1) = 2 + ν₂ (6561 * q + 4024) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4024) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4024) (2 ^ ν₂ (6561 * q + 4024)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5089 (q : ℕ) : step (8192 * q + 5089) = 6144 * q + 3817 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5089) + 1 = 2 ^ 2 * (6144 * q + 3817) := by ring
  have h_odd : (6144 * q + 3817) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5089) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 3817) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 3817) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3817) (by positivity)]

theorem step2_m8192_5089 (q : ℕ) : step (step (8192 * q + 5089)) = 4608 * q + 2863 := by
  rw [step_m8192_5089 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3817) + 1 = 2 ^ 2 * (4608 * q + 2863) := by ring
  have h_odd : (4608 * q + 2863) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3817) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 2863) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 2863) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 2863) (by positivity)]

theorem step3_m8192_5089 (q : ℕ) : step (step (step (8192 * q + 5089))) = 6912 * q + 4295 := by
  rw [step2_m8192_5089 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 2863) + 1 = 2 ^ 1 * (6912 * q + 4295) := by ring
  have h_odd : (6912 * q + 4295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 2863) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 4295) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 4295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 4295) (by positivity)]

theorem step4_m8192_5089 (q : ℕ) : step (step (step (step (8192 * q + 5089)))) = 10368 * q + 6443 := by
  rw [step3_m8192_5089 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 4295) + 1 = 2 ^ 1 * (10368 * q + 6443) := by ring
  have h_odd : (10368 * q + 6443) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 4295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 6443) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 6443) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 6443) (by positivity)]

theorem step5_m8192_5089 (q : ℕ) : step (step (step (step (step (8192 * q + 5089))))) = 15552 * q + 9665 := by
  rw [step4_m8192_5089 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 6443) + 1 = 2 ^ 1 * (15552 * q + 9665) := by ring
  have h_odd : (15552 * q + 9665) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 6443) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 9665) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 9665) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9665) (by positivity)]

theorem step6_m8192_5089 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5089)))))) = 11664 * q + 7249 := by
  rw [step5_m8192_5089 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9665) + 1 = 2 ^ 2 * (11664 * q + 7249) := by ring
  have h_odd : (11664 * q + 7249) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9665) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 7249) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 7249) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7249) (by positivity)]

theorem step7_m8192_5089 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5089))))))) = 8748 * q + 5437 := by
  rw [step6_m8192_5089 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 7249) + 1 = 2 ^ 2 * (8748 * q + 5437) := by ring
  have h_odd : (8748 * q + 5437) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 7249) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 5437) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 5437) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 5437) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5089 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5089 (q : ℕ) (hq : 8192 * q + 5089 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5089)))))))) < 8192 * q + 5089 := by
  rw [step7_m8192_5089 q]
  have h_bound : step (8748 * q + 5437) ≤ 6561 * q + 4078 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 5437) + 1 = 2 ^ 2 * (6561 * q + 4078) := by ring
    have hne : (6561 * q + 4078) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 5437) + 1) = 2 + ν₂ (6561 * q + 4078) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4078) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4078) (2 ^ ν₂ (6561 * q + 4078)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5103 (q : ℕ) : step (8192 * q + 5103) = 12288 * q + 7655 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5103) + 1 = 2 ^ 1 * (12288 * q + 7655) := by ring
  have h_odd : (12288 * q + 7655) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5103) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 7655) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 7655) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 7655) (by positivity)]

theorem step2_m8192_5103 (q : ℕ) : step (step (8192 * q + 5103)) = 18432 * q + 11483 := by
  rw [step_m8192_5103 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 7655) + 1 = 2 ^ 1 * (18432 * q + 11483) := by ring
  have h_odd : (18432 * q + 11483) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 7655) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 11483) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 11483) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 11483) (by positivity)]

theorem step3_m8192_5103 (q : ℕ) : step (step (step (8192 * q + 5103))) = 27648 * q + 17225 := by
  rw [step2_m8192_5103 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 11483) + 1 = 2 ^ 1 * (27648 * q + 17225) := by ring
  have h_odd : (27648 * q + 17225) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 11483) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 17225) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 17225) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 17225) (by positivity)]

theorem step4_m8192_5103 (q : ℕ) : step (step (step (step (8192 * q + 5103)))) = 20736 * q + 12919 := by
  rw [step3_m8192_5103 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 17225) + 1 = 2 ^ 2 * (20736 * q + 12919) := by ring
  have h_odd : (20736 * q + 12919) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 17225) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 12919) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 12919) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 12919) (by positivity)]

theorem step5_m8192_5103 (q : ℕ) : step (step (step (step (step (8192 * q + 5103))))) = 31104 * q + 19379 := by
  rw [step4_m8192_5103 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 12919) + 1 = 2 ^ 1 * (31104 * q + 19379) := by ring
  have h_odd : (31104 * q + 19379) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 12919) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 19379) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 19379) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 19379) (by positivity)]

theorem step6_m8192_5103 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5103)))))) = 46656 * q + 29069 := by
  rw [step5_m8192_5103 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 19379) + 1 = 2 ^ 1 * (46656 * q + 29069) := by ring
  have h_odd : (46656 * q + 29069) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 19379) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 29069) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 29069) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 29069) (by positivity)]

theorem step7_m8192_5103 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5103))))))) = 17496 * q + 10901 := by
  rw [step6_m8192_5103 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 29069) + 1 = 2 ^ 3 * (17496 * q + 10901) := by ring
  have h_odd : (17496 * q + 10901) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 29069) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (17496 * q + 10901) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (17496 * q + 10901) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 10901) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5103 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5103 (q : ℕ) (hq : 8192 * q + 5103 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5103)))))))) < 8192 * q + 5103 := by
  rw [step7_m8192_5103 q]
  have h_bound : step (17496 * q + 10901) ≤ 6561 * q + 4088 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 10901) + 1 = 2 ^ 3 * (6561 * q + 4088) := by ring
    have hne : (6561 * q + 4088) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 10901) + 1) = 3 + ν₂ (6561 * q + 4088) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4088) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4088) (2 ^ ν₂ (6561 * q + 4088)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5161 (q : ℕ) : step (8192 * q + 5161) = 6144 * q + 3871 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5161) + 1 = 2 ^ 2 * (6144 * q + 3871) := by ring
  have h_odd : (6144 * q + 3871) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5161) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 3871) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 3871) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 3871) (by positivity)]

theorem step2_m8192_5161 (q : ℕ) : step (step (8192 * q + 5161)) = 9216 * q + 5807 := by
  rw [step_m8192_5161 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 3871) + 1 = 2 ^ 1 * (9216 * q + 5807) := by ring
  have h_odd : (9216 * q + 5807) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 3871) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 5807) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 5807) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5807) (by positivity)]

theorem step3_m8192_5161 (q : ℕ) : step (step (step (8192 * q + 5161))) = 13824 * q + 8711 := by
  rw [step2_m8192_5161 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5807) + 1 = 2 ^ 1 * (13824 * q + 8711) := by ring
  have h_odd : (13824 * q + 8711) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5807) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 8711) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 8711) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8711) (by positivity)]

theorem step4_m8192_5161 (q : ℕ) : step (step (step (step (8192 * q + 5161)))) = 20736 * q + 13067 := by
  rw [step3_m8192_5161 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8711) + 1 = 2 ^ 1 * (20736 * q + 13067) := by ring
  have h_odd : (20736 * q + 13067) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8711) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 13067) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 13067) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 13067) (by positivity)]

theorem step5_m8192_5161 (q : ℕ) : step (step (step (step (step (8192 * q + 5161))))) = 31104 * q + 19601 := by
  rw [step4_m8192_5161 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 13067) + 1 = 2 ^ 1 * (31104 * q + 19601) := by ring
  have h_odd : (31104 * q + 19601) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 13067) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 19601) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 19601) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 19601) (by positivity)]

theorem step6_m8192_5161 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5161)))))) = 23328 * q + 14701 := by
  rw [step5_m8192_5161 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 19601) + 1 = 2 ^ 2 * (23328 * q + 14701) := by ring
  have h_odd : (23328 * q + 14701) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 19601) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 14701) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 14701) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 14701) (by positivity)]

theorem step7_m8192_5161 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5161))))))) = 8748 * q + 5513 := by
  rw [step6_m8192_5161 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 14701) + 1 = 2 ^ 3 * (8748 * q + 5513) := by ring
  have h_odd : (8748 * q + 5513) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 14701) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 5513) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 5513) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 5513) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5161 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5161 (q : ℕ) (hq : 8192 * q + 5161 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5161)))))))) < 8192 * q + 5161 := by
  rw [step7_m8192_5161 q]
  have h_bound : step (8748 * q + 5513) ≤ 6561 * q + 4135 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 5513) + 1 = 2 ^ 2 * (6561 * q + 4135) := by ring
    have hne : (6561 * q + 4135) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 5513) + 1) = 2 + ν₂ (6561 * q + 4135) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4135) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4135) (2 ^ ν₂ (6561 * q + 4135)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5191 (q : ℕ) : step (8192 * q + 5191) = 12288 * q + 7787 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5191) + 1 = 2 ^ 1 * (12288 * q + 7787) := by ring
  have h_odd : (12288 * q + 7787) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5191) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 7787) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 7787) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 7787) (by positivity)]

theorem step2_m8192_5191 (q : ℕ) : step (step (8192 * q + 5191)) = 18432 * q + 11681 := by
  rw [step_m8192_5191 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 7787) + 1 = 2 ^ 1 * (18432 * q + 11681) := by ring
  have h_odd : (18432 * q + 11681) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 7787) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 11681) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 11681) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 11681) (by positivity)]

theorem step3_m8192_5191 (q : ℕ) : step (step (step (8192 * q + 5191))) = 13824 * q + 8761 := by
  rw [step2_m8192_5191 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 11681) + 1 = 2 ^ 2 * (13824 * q + 8761) := by ring
  have h_odd : (13824 * q + 8761) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 11681) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 8761) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 8761) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8761) (by positivity)]

theorem step4_m8192_5191 (q : ℕ) : step (step (step (step (8192 * q + 5191)))) = 10368 * q + 6571 := by
  rw [step3_m8192_5191 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8761) + 1 = 2 ^ 2 * (10368 * q + 6571) := by ring
  have h_odd : (10368 * q + 6571) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8761) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 6571) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 6571) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 6571) (by positivity)]

theorem step5_m8192_5191 (q : ℕ) : step (step (step (step (step (8192 * q + 5191))))) = 15552 * q + 9857 := by
  rw [step4_m8192_5191 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 6571) + 1 = 2 ^ 1 * (15552 * q + 9857) := by ring
  have h_odd : (15552 * q + 9857) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 6571) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 9857) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 9857) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 9857) (by positivity)]

theorem step6_m8192_5191 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5191)))))) = 11664 * q + 7393 := by
  rw [step5_m8192_5191 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 9857) + 1 = 2 ^ 2 * (11664 * q + 7393) := by ring
  have h_odd : (11664 * q + 7393) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 9857) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 7393) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 7393) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7393) (by positivity)]

theorem step7_m8192_5191 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5191))))))) = 8748 * q + 5545 := by
  rw [step6_m8192_5191 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 7393) + 1 = 2 ^ 2 * (8748 * q + 5545) := by ring
  have h_odd : (8748 * q + 5545) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 7393) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 5545) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 5545) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 5545) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5191 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5191 (q : ℕ) (hq : 8192 * q + 5191 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5191)))))))) < 8192 * q + 5191 := by
  rw [step7_m8192_5191 q]
  have h_bound : step (8748 * q + 5545) ≤ 6561 * q + 4159 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 5545) + 1 = 2 ^ 2 * (6561 * q + 4159) := by ring
    have hne : (6561 * q + 4159) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 5545) + 1) = 2 + ν₂ (6561 * q + 4159) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4159) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4159) (2 ^ ν₂ (6561 * q + 4159)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5275 (q : ℕ) : step (8192 * q + 5275) = 12288 * q + 7913 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5275) + 1 = 2 ^ 1 * (12288 * q + 7913) := by ring
  have h_odd : (12288 * q + 7913) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5275) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 7913) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 7913) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 7913) (by positivity)]

theorem step2_m8192_5275 (q : ℕ) : step (step (8192 * q + 5275)) = 9216 * q + 5935 := by
  rw [step_m8192_5275 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 7913) + 1 = 2 ^ 2 * (9216 * q + 5935) := by ring
  have h_odd : (9216 * q + 5935) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 7913) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 5935) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 5935) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 5935) (by positivity)]

theorem step3_m8192_5275 (q : ℕ) : step (step (step (8192 * q + 5275))) = 13824 * q + 8903 := by
  rw [step2_m8192_5275 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 5935) + 1 = 2 ^ 1 * (13824 * q + 8903) := by ring
  have h_odd : (13824 * q + 8903) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 5935) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 8903) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 8903) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 8903) (by positivity)]

theorem step4_m8192_5275 (q : ℕ) : step (step (step (step (8192 * q + 5275)))) = 20736 * q + 13355 := by
  rw [step3_m8192_5275 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 8903) + 1 = 2 ^ 1 * (20736 * q + 13355) := by ring
  have h_odd : (20736 * q + 13355) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 8903) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 13355) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 13355) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 13355) (by positivity)]

theorem step5_m8192_5275 (q : ℕ) : step (step (step (step (step (8192 * q + 5275))))) = 31104 * q + 20033 := by
  rw [step4_m8192_5275 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 13355) + 1 = 2 ^ 1 * (31104 * q + 20033) := by ring
  have h_odd : (31104 * q + 20033) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 13355) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 20033) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 20033) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 20033) (by positivity)]

theorem step6_m8192_5275 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5275)))))) = 23328 * q + 15025 := by
  rw [step5_m8192_5275 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 20033) + 1 = 2 ^ 2 * (23328 * q + 15025) := by ring
  have h_odd : (23328 * q + 15025) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 20033) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 15025) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 15025) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 15025) (by positivity)]

theorem step7_m8192_5275 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5275))))))) = 17496 * q + 11269 := by
  rw [step6_m8192_5275 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 15025) + 1 = 2 ^ 2 * (17496 * q + 11269) := by ring
  have h_odd : (17496 * q + 11269) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 15025) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 11269) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 11269) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 11269) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5275 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5275 (q : ℕ) (hq : 8192 * q + 5275 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5275)))))))) < 8192 * q + 5275 := by
  rw [step7_m8192_5275 q]
  have h_bound : step (17496 * q + 11269) ≤ 6561 * q + 4226 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 11269) + 1 = 2 ^ 3 * (6561 * q + 4226) := by ring
    have hne : (6561 * q + 4226) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 11269) + 1) = 3 + ν₂ (6561 * q + 4226) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4226) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4226) (2 ^ ν₂ (6561 * q + 4226)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5371 (q : ℕ) : step (8192 * q + 5371) = 12288 * q + 8057 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5371) + 1 = 2 ^ 1 * (12288 * q + 8057) := by ring
  have h_odd : (12288 * q + 8057) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5371) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8057) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8057) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8057) (by positivity)]

theorem step2_m8192_5371 (q : ℕ) : step (step (8192 * q + 5371)) = 9216 * q + 6043 := by
  rw [step_m8192_5371 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8057) + 1 = 2 ^ 2 * (9216 * q + 6043) := by ring
  have h_odd : (9216 * q + 6043) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8057) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 6043) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 6043) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6043) (by positivity)]

theorem step3_m8192_5371 (q : ℕ) : step (step (step (8192 * q + 5371))) = 13824 * q + 9065 := by
  rw [step2_m8192_5371 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6043) + 1 = 2 ^ 1 * (13824 * q + 9065) := by ring
  have h_odd : (13824 * q + 9065) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6043) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 9065) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 9065) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 9065) (by positivity)]

theorem step4_m8192_5371 (q : ℕ) : step (step (step (step (8192 * q + 5371)))) = 10368 * q + 6799 := by
  rw [step3_m8192_5371 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 9065) + 1 = 2 ^ 2 * (10368 * q + 6799) := by ring
  have h_odd : (10368 * q + 6799) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 9065) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 6799) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 6799) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 6799) (by positivity)]

theorem step5_m8192_5371 (q : ℕ) : step (step (step (step (step (8192 * q + 5371))))) = 15552 * q + 10199 := by
  rw [step4_m8192_5371 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 6799) + 1 = 2 ^ 1 * (15552 * q + 10199) := by ring
  have h_odd : (15552 * q + 10199) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 6799) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 10199) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 10199) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 10199) (by positivity)]

theorem step6_m8192_5371 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5371)))))) = 23328 * q + 15299 := by
  rw [step5_m8192_5371 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 10199) + 1 = 2 ^ 1 * (23328 * q + 15299) := by ring
  have h_odd : (23328 * q + 15299) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 10199) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 15299) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 15299) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 15299) (by positivity)]

theorem step7_m8192_5371 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5371))))))) = 34992 * q + 22949 := by
  rw [step6_m8192_5371 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 15299) + 1 = 2 ^ 1 * (34992 * q + 22949) := by ring
  have h_odd : (34992 * q + 22949) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 15299) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 22949) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 22949) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 22949) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5371 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5371 (q : ℕ) (hq : 8192 * q + 5371 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5371)))))))) < 8192 * q + 5371 := by
  rw [step7_m8192_5371 q]
  have h_bound : step (34992 * q + 22949) ≤ 6561 * q + 4303 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 22949) + 1 = 2 ^ 4 * (6561 * q + 4303) := by ring
    have hne : (6561 * q + 4303) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 22949) + 1) = 4 + ν₂ (6561 * q + 4303) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 4303) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4303) (2 ^ ν₂ (6561 * q + 4303)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5417 (q : ℕ) : step (8192 * q + 5417) = 6144 * q + 4063 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5417) + 1 = 2 ^ 2 * (6144 * q + 4063) := by ring
  have h_odd : (6144 * q + 4063) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5417) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4063) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4063) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4063) (by positivity)]

theorem step2_m8192_5417 (q : ℕ) : step (step (8192 * q + 5417)) = 9216 * q + 6095 := by
  rw [step_m8192_5417 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4063) + 1 = 2 ^ 1 * (9216 * q + 6095) := by ring
  have h_odd : (9216 * q + 6095) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4063) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 6095) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 6095) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6095) (by positivity)]

theorem step3_m8192_5417 (q : ℕ) : step (step (step (8192 * q + 5417))) = 13824 * q + 9143 := by
  rw [step2_m8192_5417 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6095) + 1 = 2 ^ 1 * (13824 * q + 9143) := by ring
  have h_odd : (13824 * q + 9143) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6095) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 9143) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 9143) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 9143) (by positivity)]

theorem step4_m8192_5417 (q : ℕ) : step (step (step (step (8192 * q + 5417)))) = 20736 * q + 13715 := by
  rw [step3_m8192_5417 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 9143) + 1 = 2 ^ 1 * (20736 * q + 13715) := by ring
  have h_odd : (20736 * q + 13715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 9143) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 13715) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 13715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 13715) (by positivity)]

theorem step5_m8192_5417 (q : ℕ) : step (step (step (step (step (8192 * q + 5417))))) = 31104 * q + 20573 := by
  rw [step4_m8192_5417 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 13715) + 1 = 2 ^ 1 * (31104 * q + 20573) := by ring
  have h_odd : (31104 * q + 20573) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 13715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 20573) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 20573) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 20573) (by positivity)]

theorem step6_m8192_5417 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5417)))))) = 11664 * q + 7715 := by
  rw [step5_m8192_5417 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 20573) + 1 = 2 ^ 3 * (11664 * q + 7715) := by ring
  have h_odd : (11664 * q + 7715) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 20573) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 7715) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 7715) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7715) (by positivity)]

theorem step7_m8192_5417 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5417))))))) = 17496 * q + 11573 := by
  rw [step6_m8192_5417 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 7715) + 1 = 2 ^ 1 * (17496 * q + 11573) := by ring
  have h_odd : (17496 * q + 11573) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 7715) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 11573) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 11573) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 11573) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5417 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5417 (q : ℕ) (hq : 8192 * q + 5417 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5417)))))))) < 8192 * q + 5417 := by
  rw [step7_m8192_5417 q]
  have h_bound : step (17496 * q + 11573) ≤ 6561 * q + 4340 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 11573) + 1 = 2 ^ 3 * (6561 * q + 4340) := by ring
    have hne : (6561 * q + 4340) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 11573) + 1) = 3 + ν₂ (6561 * q + 4340) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4340) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4340) (2 ^ ν₂ (6561 * q + 4340)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5439 (q : ℕ) : step (8192 * q + 5439) = 12288 * q + 8159 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5439) + 1 = 2 ^ 1 * (12288 * q + 8159) := by ring
  have h_odd : (12288 * q + 8159) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5439) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8159) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8159) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8159) (by positivity)]

theorem step2_m8192_5439 (q : ℕ) : step (step (8192 * q + 5439)) = 18432 * q + 12239 := by
  rw [step_m8192_5439 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8159) + 1 = 2 ^ 1 * (18432 * q + 12239) := by ring
  have h_odd : (18432 * q + 12239) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8159) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 12239) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 12239) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 12239) (by positivity)]

theorem step3_m8192_5439 (q : ℕ) : step (step (step (8192 * q + 5439))) = 27648 * q + 18359 := by
  rw [step2_m8192_5439 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 12239) + 1 = 2 ^ 1 * (27648 * q + 18359) := by ring
  have h_odd : (27648 * q + 18359) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 12239) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 18359) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 18359) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 18359) (by positivity)]

theorem step4_m8192_5439 (q : ℕ) : step (step (step (step (8192 * q + 5439)))) = 41472 * q + 27539 := by
  rw [step3_m8192_5439 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 18359) + 1 = 2 ^ 1 * (41472 * q + 27539) := by ring
  have h_odd : (41472 * q + 27539) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 18359) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 27539) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 27539) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 27539) (by positivity)]

theorem step5_m8192_5439 (q : ℕ) : step (step (step (step (step (8192 * q + 5439))))) = 62208 * q + 41309 := by
  rw [step4_m8192_5439 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 27539) + 1 = 2 ^ 1 * (62208 * q + 41309) := by ring
  have h_odd : (62208 * q + 41309) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 27539) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (62208 * q + 41309) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (62208 * q + 41309) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (62208 * q + 41309) (by positivity)]

theorem step6_m8192_5439 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5439)))))) = 23328 * q + 15491 := by
  rw [step5_m8192_5439 q]
  unfold step
  have h3n1 : 3 * (62208 * q + 41309) + 1 = 2 ^ 3 * (23328 * q + 15491) := by ring
  have h_odd : (23328 * q + 15491) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (62208 * q + 41309) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (23328 * q + 15491) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (23328 * q + 15491) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 15491) (by positivity)]

theorem step7_m8192_5439 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5439))))))) = 34992 * q + 23237 := by
  rw [step6_m8192_5439 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 15491) + 1 = 2 ^ 1 * (34992 * q + 23237) := by ring
  have h_odd : (34992 * q + 23237) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 15491) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 23237) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 23237) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 23237) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5439 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5439 (q : ℕ) (hq : 8192 * q + 5439 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5439)))))))) < 8192 * q + 5439 := by
  rw [step7_m8192_5439 q]
  have h_bound : step (34992 * q + 23237) ≤ 6561 * q + 4357 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 23237) + 1 = 2 ^ 4 * (6561 * q + 4357) := by ring
    have hne : (6561 * q + 4357) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 23237) + 1) = 4 + ν₂ (6561 * q + 4357) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 4357) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4357) (2 ^ ν₂ (6561 * q + 4357)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5607 (q : ℕ) : step (8192 * q + 5607) = 12288 * q + 8411 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5607) + 1 = 2 ^ 1 * (12288 * q + 8411) := by ring
  have h_odd : (12288 * q + 8411) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8411) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8411) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8411) (by positivity)]

theorem step2_m8192_5607 (q : ℕ) : step (step (8192 * q + 5607)) = 18432 * q + 12617 := by
  rw [step_m8192_5607 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8411) + 1 = 2 ^ 1 * (18432 * q + 12617) := by ring
  have h_odd : (18432 * q + 12617) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8411) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 12617) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 12617) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 12617) (by positivity)]

theorem step3_m8192_5607 (q : ℕ) : step (step (step (8192 * q + 5607))) = 13824 * q + 9463 := by
  rw [step2_m8192_5607 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 12617) + 1 = 2 ^ 2 * (13824 * q + 9463) := by ring
  have h_odd : (13824 * q + 9463) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 12617) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 9463) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 9463) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 9463) (by positivity)]

theorem step4_m8192_5607 (q : ℕ) : step (step (step (step (8192 * q + 5607)))) = 20736 * q + 14195 := by
  rw [step3_m8192_5607 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 9463) + 1 = 2 ^ 1 * (20736 * q + 14195) := by ring
  have h_odd : (20736 * q + 14195) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 9463) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 14195) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 14195) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 14195) (by positivity)]

theorem step5_m8192_5607 (q : ℕ) : step (step (step (step (step (8192 * q + 5607))))) = 31104 * q + 21293 := by
  rw [step4_m8192_5607 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 14195) + 1 = 2 ^ 1 * (31104 * q + 21293) := by ring
  have h_odd : (31104 * q + 21293) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 14195) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 21293) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 21293) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 21293) (by positivity)]

theorem step6_m8192_5607 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5607)))))) = 11664 * q + 7985 := by
  rw [step5_m8192_5607 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 21293) + 1 = 2 ^ 3 * (11664 * q + 7985) := by ring
  have h_odd : (11664 * q + 7985) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 21293) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 7985) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 7985) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 7985) (by positivity)]

theorem step7_m8192_5607 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5607))))))) = 8748 * q + 5989 := by
  rw [step6_m8192_5607 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 7985) + 1 = 2 ^ 2 * (8748 * q + 5989) := by ring
  have h_odd : (8748 * q + 5989) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 7985) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 5989) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 5989) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 5989) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5607 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5607 (q : ℕ) (hq : 8192 * q + 5607 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5607)))))))) < 8192 * q + 5607 := by
  rw [step7_m8192_5607 q]
  have h_bound : step (8748 * q + 5989) ≤ 6561 * q + 4492 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 5989) + 1 = 2 ^ 2 * (6561 * q + 4492) := by ring
    have hne : (6561 * q + 4492) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 5989) + 1) = 2 + ν₂ (6561 * q + 4492) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4492) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4492) (2 ^ ν₂ (6561 * q + 4492)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5615 (q : ℕ) : step (8192 * q + 5615) = 12288 * q + 8423 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5615) + 1 = 2 ^ 1 * (12288 * q + 8423) := by ring
  have h_odd : (12288 * q + 8423) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5615) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8423) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8423) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8423) (by positivity)]

theorem step2_m8192_5615 (q : ℕ) : step (step (8192 * q + 5615)) = 18432 * q + 12635 := by
  rw [step_m8192_5615 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8423) + 1 = 2 ^ 1 * (18432 * q + 12635) := by ring
  have h_odd : (18432 * q + 12635) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8423) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 12635) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 12635) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 12635) (by positivity)]

theorem step3_m8192_5615 (q : ℕ) : step (step (step (8192 * q + 5615))) = 27648 * q + 18953 := by
  rw [step2_m8192_5615 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 12635) + 1 = 2 ^ 1 * (27648 * q + 18953) := by ring
  have h_odd : (27648 * q + 18953) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 12635) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 18953) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 18953) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 18953) (by positivity)]

theorem step4_m8192_5615 (q : ℕ) : step (step (step (step (8192 * q + 5615)))) = 20736 * q + 14215 := by
  rw [step3_m8192_5615 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 18953) + 1 = 2 ^ 2 * (20736 * q + 14215) := by ring
  have h_odd : (20736 * q + 14215) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 18953) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 14215) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 14215) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 14215) (by positivity)]

theorem step5_m8192_5615 (q : ℕ) : step (step (step (step (step (8192 * q + 5615))))) = 31104 * q + 21323 := by
  rw [step4_m8192_5615 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 14215) + 1 = 2 ^ 1 * (31104 * q + 21323) := by ring
  have h_odd : (31104 * q + 21323) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 14215) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 21323) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 21323) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 21323) (by positivity)]

theorem step6_m8192_5615 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5615)))))) = 46656 * q + 31985 := by
  rw [step5_m8192_5615 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 21323) + 1 = 2 ^ 1 * (46656 * q + 31985) := by ring
  have h_odd : (46656 * q + 31985) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 21323) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 31985) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 31985) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 31985) (by positivity)]

theorem step7_m8192_5615 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5615))))))) = 34992 * q + 23989 := by
  rw [step6_m8192_5615 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 31985) + 1 = 2 ^ 2 * (34992 * q + 23989) := by ring
  have h_odd : (34992 * q + 23989) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 31985) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (34992 * q + 23989) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (34992 * q + 23989) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 23989) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5615 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5615 (q : ℕ) (hq : 8192 * q + 5615 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5615)))))))) < 8192 * q + 5615 := by
  rw [step7_m8192_5615 q]
  have h_bound : step (34992 * q + 23989) ≤ 6561 * q + 4498 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 23989) + 1 = 2 ^ 4 * (6561 * q + 4498) := by ring
    have hne : (6561 * q + 4498) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 23989) + 1) = 4 + ν₂ (6561 * q + 4498) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 4498) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4498) (2 ^ ν₂ (6561 * q + 4498)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5723 (q : ℕ) : step (8192 * q + 5723) = 12288 * q + 8585 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5723) + 1 = 2 ^ 1 * (12288 * q + 8585) := by ring
  have h_odd : (12288 * q + 8585) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5723) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8585) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8585) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8585) (by positivity)]

theorem step2_m8192_5723 (q : ℕ) : step (step (8192 * q + 5723)) = 9216 * q + 6439 := by
  rw [step_m8192_5723 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8585) + 1 = 2 ^ 2 * (9216 * q + 6439) := by ring
  have h_odd : (9216 * q + 6439) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8585) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 6439) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 6439) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6439) (by positivity)]

theorem step3_m8192_5723 (q : ℕ) : step (step (step (8192 * q + 5723))) = 13824 * q + 9659 := by
  rw [step2_m8192_5723 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6439) + 1 = 2 ^ 1 * (13824 * q + 9659) := by ring
  have h_odd : (13824 * q + 9659) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6439) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 9659) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 9659) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 9659) (by positivity)]

theorem step4_m8192_5723 (q : ℕ) : step (step (step (step (8192 * q + 5723)))) = 20736 * q + 14489 := by
  rw [step3_m8192_5723 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 9659) + 1 = 2 ^ 1 * (20736 * q + 14489) := by ring
  have h_odd : (20736 * q + 14489) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 9659) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 14489) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 14489) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 14489) (by positivity)]

theorem step5_m8192_5723 (q : ℕ) : step (step (step (step (step (8192 * q + 5723))))) = 15552 * q + 10867 := by
  rw [step4_m8192_5723 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 14489) + 1 = 2 ^ 2 * (15552 * q + 10867) := by ring
  have h_odd : (15552 * q + 10867) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 14489) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 10867) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 10867) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 10867) (by positivity)]

theorem step6_m8192_5723 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5723)))))) = 23328 * q + 16301 := by
  rw [step5_m8192_5723 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 10867) + 1 = 2 ^ 1 * (23328 * q + 16301) := by ring
  have h_odd : (23328 * q + 16301) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 10867) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 16301) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 16301) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 16301) (by positivity)]

theorem step7_m8192_5723 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5723))))))) = 8748 * q + 6113 := by
  rw [step6_m8192_5723 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 16301) + 1 = 2 ^ 3 * (8748 * q + 6113) := by ring
  have h_odd : (8748 * q + 6113) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 16301) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 6113) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 6113) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 6113) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5723 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5723 (q : ℕ) (hq : 8192 * q + 5723 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5723)))))))) < 8192 * q + 5723 := by
  rw [step7_m8192_5723 q]
  have h_bound : step (8748 * q + 6113) ≤ 6561 * q + 4585 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 6113) + 1 = 2 ^ 2 * (6561 * q + 4585) := by ring
    have hne : (6561 * q + 4585) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 6113) + 1) = 2 + ν₂ (6561 * q + 4585) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4585) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4585) (2 ^ ν₂ (6561 * q + 4585)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5769 (q : ℕ) : step (8192 * q + 5769) = 6144 * q + 4327 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5769) + 1 = 2 ^ 2 * (6144 * q + 4327) := by ring
  have h_odd : (6144 * q + 4327) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5769) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4327) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4327) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4327) (by positivity)]

theorem step2_m8192_5769 (q : ℕ) : step (step (8192 * q + 5769)) = 9216 * q + 6491 := by
  rw [step_m8192_5769 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4327) + 1 = 2 ^ 1 * (9216 * q + 6491) := by ring
  have h_odd : (9216 * q + 6491) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4327) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 6491) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 6491) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6491) (by positivity)]

theorem step3_m8192_5769 (q : ℕ) : step (step (step (8192 * q + 5769))) = 13824 * q + 9737 := by
  rw [step2_m8192_5769 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6491) + 1 = 2 ^ 1 * (13824 * q + 9737) := by ring
  have h_odd : (13824 * q + 9737) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6491) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 9737) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 9737) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 9737) (by positivity)]

theorem step4_m8192_5769 (q : ℕ) : step (step (step (step (8192 * q + 5769)))) = 10368 * q + 7303 := by
  rw [step3_m8192_5769 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 9737) + 1 = 2 ^ 2 * (10368 * q + 7303) := by ring
  have h_odd : (10368 * q + 7303) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 9737) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 7303) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 7303) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7303) (by positivity)]

theorem step5_m8192_5769 (q : ℕ) : step (step (step (step (step (8192 * q + 5769))))) = 15552 * q + 10955 := by
  rw [step4_m8192_5769 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7303) + 1 = 2 ^ 1 * (15552 * q + 10955) := by ring
  have h_odd : (15552 * q + 10955) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7303) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 10955) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 10955) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 10955) (by positivity)]

theorem step6_m8192_5769 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5769)))))) = 23328 * q + 16433 := by
  rw [step5_m8192_5769 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 10955) + 1 = 2 ^ 1 * (23328 * q + 16433) := by ring
  have h_odd : (23328 * q + 16433) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 10955) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 16433) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 16433) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 16433) (by positivity)]

theorem step7_m8192_5769 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5769))))))) = 17496 * q + 12325 := by
  rw [step6_m8192_5769 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 16433) + 1 = 2 ^ 2 * (17496 * q + 12325) := by ring
  have h_odd : (17496 * q + 12325) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 16433) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 12325) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 12325) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 12325) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5769 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5769 (q : ℕ) (hq : 8192 * q + 5769 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5769)))))))) < 8192 * q + 5769 := by
  rw [step7_m8192_5769 q]
  have h_bound : step (17496 * q + 12325) ≤ 6561 * q + 4622 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 12325) + 1 = 2 ^ 3 * (6561 * q + 4622) := by ring
    have hne : (6561 * q + 4622) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 12325) + 1) = 3 + ν₂ (6561 * q + 4622) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4622) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4622) (2 ^ ν₂ (6561 * q + 4622)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5787 (q : ℕ) : step (8192 * q + 5787) = 12288 * q + 8681 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5787) + 1 = 2 ^ 1 * (12288 * q + 8681) := by ring
  have h_odd : (12288 * q + 8681) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5787) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8681) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8681) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8681) (by positivity)]

theorem step2_m8192_5787 (q : ℕ) : step (step (8192 * q + 5787)) = 9216 * q + 6511 := by
  rw [step_m8192_5787 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8681) + 1 = 2 ^ 2 * (9216 * q + 6511) := by ring
  have h_odd : (9216 * q + 6511) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8681) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 6511) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 6511) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6511) (by positivity)]

theorem step3_m8192_5787 (q : ℕ) : step (step (step (8192 * q + 5787))) = 13824 * q + 9767 := by
  rw [step2_m8192_5787 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6511) + 1 = 2 ^ 1 * (13824 * q + 9767) := by ring
  have h_odd : (13824 * q + 9767) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6511) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 9767) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 9767) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 9767) (by positivity)]

theorem step4_m8192_5787 (q : ℕ) : step (step (step (step (8192 * q + 5787)))) = 20736 * q + 14651 := by
  rw [step3_m8192_5787 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 9767) + 1 = 2 ^ 1 * (20736 * q + 14651) := by ring
  have h_odd : (20736 * q + 14651) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 9767) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 14651) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 14651) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 14651) (by positivity)]

theorem step5_m8192_5787 (q : ℕ) : step (step (step (step (step (8192 * q + 5787))))) = 31104 * q + 21977 := by
  rw [step4_m8192_5787 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 14651) + 1 = 2 ^ 1 * (31104 * q + 21977) := by ring
  have h_odd : (31104 * q + 21977) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 14651) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 21977) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 21977) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 21977) (by positivity)]

theorem step6_m8192_5787 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5787)))))) = 23328 * q + 16483 := by
  rw [step5_m8192_5787 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 21977) + 1 = 2 ^ 2 * (23328 * q + 16483) := by ring
  have h_odd : (23328 * q + 16483) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 21977) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 16483) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 16483) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 16483) (by positivity)]

theorem step7_m8192_5787 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5787))))))) = 34992 * q + 24725 := by
  rw [step6_m8192_5787 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 16483) + 1 = 2 ^ 1 * (34992 * q + 24725) := by ring
  have h_odd : (34992 * q + 24725) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 16483) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 24725) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 24725) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 24725) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5787 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5787 (q : ℕ) (hq : 8192 * q + 5787 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5787)))))))) < 8192 * q + 5787 := by
  rw [step7_m8192_5787 q]
  have h_bound : step (34992 * q + 24725) ≤ 6561 * q + 4636 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 24725) + 1 = 2 ^ 4 * (6561 * q + 4636) := by ring
    have hne : (6561 * q + 4636) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 24725) + 1) = 4 + ν₂ (6561 * q + 4636) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 4636) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4636) (2 ^ ν₂ (6561 * q + 4636)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5857 (q : ℕ) : step (8192 * q + 5857) = 6144 * q + 4393 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5857) + 1 = 2 ^ 2 * (6144 * q + 4393) := by ring
  have h_odd : (6144 * q + 4393) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5857) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4393) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4393) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4393) (by positivity)]

theorem step2_m8192_5857 (q : ℕ) : step (step (8192 * q + 5857)) = 4608 * q + 3295 := by
  rw [step_m8192_5857 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4393) + 1 = 2 ^ 2 * (4608 * q + 3295) := by ring
  have h_odd : (4608 * q + 3295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4393) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 3295) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 3295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 3295) (by positivity)]

theorem step3_m8192_5857 (q : ℕ) : step (step (step (8192 * q + 5857))) = 6912 * q + 4943 := by
  rw [step2_m8192_5857 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 3295) + 1 = 2 ^ 1 * (6912 * q + 4943) := by ring
  have h_odd : (6912 * q + 4943) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 3295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 4943) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 4943) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 4943) (by positivity)]

theorem step4_m8192_5857 (q : ℕ) : step (step (step (step (8192 * q + 5857)))) = 10368 * q + 7415 := by
  rw [step3_m8192_5857 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 4943) + 1 = 2 ^ 1 * (10368 * q + 7415) := by ring
  have h_odd : (10368 * q + 7415) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 4943) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 7415) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 7415) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7415) (by positivity)]

theorem step5_m8192_5857 (q : ℕ) : step (step (step (step (step (8192 * q + 5857))))) = 15552 * q + 11123 := by
  rw [step4_m8192_5857 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7415) + 1 = 2 ^ 1 * (15552 * q + 11123) := by ring
  have h_odd : (15552 * q + 11123) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7415) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 11123) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 11123) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11123) (by positivity)]

theorem step6_m8192_5857 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5857)))))) = 23328 * q + 16685 := by
  rw [step5_m8192_5857 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11123) + 1 = 2 ^ 1 * (23328 * q + 16685) := by ring
  have h_odd : (23328 * q + 16685) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11123) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 16685) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 16685) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 16685) (by positivity)]

theorem step7_m8192_5857 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5857))))))) = 8748 * q + 6257 := by
  rw [step6_m8192_5857 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 16685) + 1 = 2 ^ 3 * (8748 * q + 6257) := by ring
  have h_odd : (8748 * q + 6257) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 16685) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 6257) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 6257) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 6257) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5857 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5857 (q : ℕ) (hq : 8192 * q + 5857 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5857)))))))) < 8192 * q + 5857 := by
  rw [step7_m8192_5857 q]
  have h_bound : step (8748 * q + 6257) ≤ 6561 * q + 4693 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 6257) + 1 = 2 ^ 2 * (6561 * q + 4693) := by ring
    have hne : (6561 * q + 4693) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 6257) + 1) = 2 + ν₂ (6561 * q + 4693) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4693) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4693) (2 ^ ν₂ (6561 * q + 4693)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5865 (q : ℕ) : step (8192 * q + 5865) = 6144 * q + 4399 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5865) + 1 = 2 ^ 2 * (6144 * q + 4399) := by ring
  have h_odd : (6144 * q + 4399) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5865) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4399) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4399) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4399) (by positivity)]

theorem step2_m8192_5865 (q : ℕ) : step (step (8192 * q + 5865)) = 9216 * q + 6599 := by
  rw [step_m8192_5865 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4399) + 1 = 2 ^ 1 * (9216 * q + 6599) := by ring
  have h_odd : (9216 * q + 6599) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4399) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 6599) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 6599) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6599) (by positivity)]

theorem step3_m8192_5865 (q : ℕ) : step (step (step (8192 * q + 5865))) = 13824 * q + 9899 := by
  rw [step2_m8192_5865 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6599) + 1 = 2 ^ 1 * (13824 * q + 9899) := by ring
  have h_odd : (13824 * q + 9899) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6599) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 9899) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 9899) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 9899) (by positivity)]

theorem step4_m8192_5865 (q : ℕ) : step (step (step (step (8192 * q + 5865)))) = 20736 * q + 14849 := by
  rw [step3_m8192_5865 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 9899) + 1 = 2 ^ 1 * (20736 * q + 14849) := by ring
  have h_odd : (20736 * q + 14849) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 9899) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 14849) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 14849) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 14849) (by positivity)]

theorem step5_m8192_5865 (q : ℕ) : step (step (step (step (step (8192 * q + 5865))))) = 15552 * q + 11137 := by
  rw [step4_m8192_5865 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 14849) + 1 = 2 ^ 2 * (15552 * q + 11137) := by ring
  have h_odd : (15552 * q + 11137) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 14849) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 11137) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 11137) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11137) (by positivity)]

theorem step6_m8192_5865 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5865)))))) = 11664 * q + 8353 := by
  rw [step5_m8192_5865 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11137) + 1 = 2 ^ 2 * (11664 * q + 8353) := by ring
  have h_odd : (11664 * q + 8353) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11137) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 8353) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 8353) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 8353) (by positivity)]

theorem step7_m8192_5865 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5865))))))) = 8748 * q + 6265 := by
  rw [step6_m8192_5865 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 8353) + 1 = 2 ^ 2 * (8748 * q + 6265) := by ring
  have h_odd : (8748 * q + 6265) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 8353) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 6265) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 6265) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 6265) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5865 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5865 (q : ℕ) (hq : 8192 * q + 5865 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5865)))))))) < 8192 * q + 5865 := by
  rw [step7_m8192_5865 q]
  have h_bound : step (8748 * q + 6265) ≤ 6561 * q + 4699 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 6265) + 1 = 2 ^ 2 * (6561 * q + 4699) := by ring
    have hne : (6561 * q + 4699) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 6265) + 1) = 2 + ν₂ (6561 * q + 4699) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4699) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4699) (2 ^ ν₂ (6561 * q + 4699)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5871 (q : ℕ) : step (8192 * q + 5871) = 12288 * q + 8807 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5871) + 1 = 2 ^ 1 * (12288 * q + 8807) := by ring
  have h_odd : (12288 * q + 8807) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5871) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8807) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8807) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8807) (by positivity)]

theorem step2_m8192_5871 (q : ℕ) : step (step (8192 * q + 5871)) = 18432 * q + 13211 := by
  rw [step_m8192_5871 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8807) + 1 = 2 ^ 1 * (18432 * q + 13211) := by ring
  have h_odd : (18432 * q + 13211) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8807) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 13211) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 13211) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 13211) (by positivity)]

theorem step3_m8192_5871 (q : ℕ) : step (step (step (8192 * q + 5871))) = 27648 * q + 19817 := by
  rw [step2_m8192_5871 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 13211) + 1 = 2 ^ 1 * (27648 * q + 19817) := by ring
  have h_odd : (27648 * q + 19817) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 13211) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 19817) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 19817) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 19817) (by positivity)]

theorem step4_m8192_5871 (q : ℕ) : step (step (step (step (8192 * q + 5871)))) = 20736 * q + 14863 := by
  rw [step3_m8192_5871 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 19817) + 1 = 2 ^ 2 * (20736 * q + 14863) := by ring
  have h_odd : (20736 * q + 14863) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 19817) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 14863) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 14863) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 14863) (by positivity)]

theorem step5_m8192_5871 (q : ℕ) : step (step (step (step (step (8192 * q + 5871))))) = 31104 * q + 22295 := by
  rw [step4_m8192_5871 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 14863) + 1 = 2 ^ 1 * (31104 * q + 22295) := by ring
  have h_odd : (31104 * q + 22295) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 14863) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 22295) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 22295) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 22295) (by positivity)]

theorem step6_m8192_5871 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5871)))))) = 46656 * q + 33443 := by
  rw [step5_m8192_5871 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 22295) + 1 = 2 ^ 1 * (46656 * q + 33443) := by ring
  have h_odd : (46656 * q + 33443) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 22295) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 33443) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 33443) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 33443) (by positivity)]

theorem step7_m8192_5871 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5871))))))) = 69984 * q + 50165 := by
  rw [step6_m8192_5871 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 33443) + 1 = 2 ^ 1 * (69984 * q + 50165) := by ring
  have h_odd : (69984 * q + 50165) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 33443) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (69984 * q + 50165) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (69984 * q + 50165) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (69984 * q + 50165) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5871 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5871 (q : ℕ) (hq : 8192 * q + 5871 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5871)))))))) < 8192 * q + 5871 := by
  rw [step7_m8192_5871 q]
  have h_bound : step (69984 * q + 50165) ≤ 6561 * q + 4703 := by
    unfold step
    have h3n1 : 3 * (69984 * q + 50165) + 1 = 2 ^ 5 * (6561 * q + 4703) := by ring
    have hne : (6561 * q + 4703) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (69984 * q + 50165) + 1) = 5 + ν₂ (6561 * q + 4703) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (6561 * q + 4703) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4703) (2 ^ ν₂ (6561 * q + 4703)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5959 (q : ℕ) : step (8192 * q + 5959) = 12288 * q + 8939 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5959) + 1 = 2 ^ 1 * (12288 * q + 8939) := by ring
  have h_odd : (12288 * q + 8939) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5959) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8939) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8939) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8939) (by positivity)]

theorem step2_m8192_5959 (q : ℕ) : step (step (8192 * q + 5959)) = 18432 * q + 13409 := by
  rw [step_m8192_5959 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8939) + 1 = 2 ^ 1 * (18432 * q + 13409) := by ring
  have h_odd : (18432 * q + 13409) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8939) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 13409) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 13409) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 13409) (by positivity)]

theorem step3_m8192_5959 (q : ℕ) : step (step (step (8192 * q + 5959))) = 13824 * q + 10057 := by
  rw [step2_m8192_5959 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 13409) + 1 = 2 ^ 2 * (13824 * q + 10057) := by ring
  have h_odd : (13824 * q + 10057) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 13409) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 10057) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 10057) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10057) (by positivity)]

theorem step4_m8192_5959 (q : ℕ) : step (step (step (step (8192 * q + 5959)))) = 10368 * q + 7543 := by
  rw [step3_m8192_5959 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10057) + 1 = 2 ^ 2 * (10368 * q + 7543) := by ring
  have h_odd : (10368 * q + 7543) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10057) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 7543) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 7543) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7543) (by positivity)]

theorem step5_m8192_5959 (q : ℕ) : step (step (step (step (step (8192 * q + 5959))))) = 15552 * q + 11315 := by
  rw [step4_m8192_5959 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7543) + 1 = 2 ^ 1 * (15552 * q + 11315) := by ring
  have h_odd : (15552 * q + 11315) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7543) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 11315) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 11315) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11315) (by positivity)]

theorem step6_m8192_5959 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5959)))))) = 23328 * q + 16973 := by
  rw [step5_m8192_5959 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11315) + 1 = 2 ^ 1 * (23328 * q + 16973) := by ring
  have h_odd : (23328 * q + 16973) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11315) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 16973) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 16973) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 16973) (by positivity)]

theorem step7_m8192_5959 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5959))))))) = 8748 * q + 6365 := by
  rw [step6_m8192_5959 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 16973) + 1 = 2 ^ 3 * (8748 * q + 6365) := by ring
  have h_odd : (8748 * q + 6365) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 16973) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 6365) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 6365) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 6365) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5959 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5959 (q : ℕ) (hq : 8192 * q + 5959 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5959)))))))) < 8192 * q + 5959 := by
  rw [step7_m8192_5959 q]
  have h_bound : step (8748 * q + 6365) ≤ 6561 * q + 4774 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 6365) + 1 = 2 ^ 2 * (6561 * q + 4774) := by ring
    have hne : (6561 * q + 4774) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 6365) + 1) = 2 + ν₂ (6561 * q + 4774) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 4774) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4774) (2 ^ ν₂ (6561 * q + 4774)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_5979 (q : ℕ) : step (8192 * q + 5979) = 12288 * q + 8969 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 5979) + 1 = 2 ^ 1 * (12288 * q + 8969) := by ring
  have h_odd : (12288 * q + 8969) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 5979) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 8969) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 8969) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 8969) (by positivity)]

theorem step2_m8192_5979 (q : ℕ) : step (step (8192 * q + 5979)) = 9216 * q + 6727 := by
  rw [step_m8192_5979 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 8969) + 1 = 2 ^ 2 * (9216 * q + 6727) := by ring
  have h_odd : (9216 * q + 6727) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 8969) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 6727) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 6727) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6727) (by positivity)]

theorem step3_m8192_5979 (q : ℕ) : step (step (step (8192 * q + 5979))) = 13824 * q + 10091 := by
  rw [step2_m8192_5979 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6727) + 1 = 2 ^ 1 * (13824 * q + 10091) := by ring
  have h_odd : (13824 * q + 10091) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6727) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 10091) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 10091) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10091) (by positivity)]

theorem step4_m8192_5979 (q : ℕ) : step (step (step (step (8192 * q + 5979)))) = 20736 * q + 15137 := by
  rw [step3_m8192_5979 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10091) + 1 = 2 ^ 1 * (20736 * q + 15137) := by ring
  have h_odd : (20736 * q + 15137) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10091) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 15137) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 15137) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 15137) (by positivity)]

theorem step5_m8192_5979 (q : ℕ) : step (step (step (step (step (8192 * q + 5979))))) = 15552 * q + 11353 := by
  rw [step4_m8192_5979 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 15137) + 1 = 2 ^ 2 * (15552 * q + 11353) := by ring
  have h_odd : (15552 * q + 11353) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 15137) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 11353) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 11353) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11353) (by positivity)]

theorem step6_m8192_5979 (q : ℕ) : step (step (step (step (step (step (8192 * q + 5979)))))) = 11664 * q + 8515 := by
  rw [step5_m8192_5979 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11353) + 1 = 2 ^ 2 * (11664 * q + 8515) := by ring
  have h_odd : (11664 * q + 8515) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11353) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 8515) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 8515) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 8515) (by positivity)]

theorem step7_m8192_5979 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 5979))))))) = 17496 * q + 12773 := by
  rw [step6_m8192_5979 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 8515) + 1 = 2 ^ 1 * (17496 * q + 12773) := by ring
  have h_odd : (17496 * q + 12773) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 8515) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 12773) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 12773) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 12773) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 5979 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_5979 (q : ℕ) (hq : 8192 * q + 5979 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 5979)))))))) < 8192 * q + 5979 := by
  rw [step7_m8192_5979 q]
  have h_bound : step (17496 * q + 12773) ≤ 6561 * q + 4790 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 12773) + 1 = 2 ^ 3 * (6561 * q + 4790) := by ring
    have hne : (6561 * q + 4790) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 12773) + 1) = 3 + ν₂ (6561 * q + 4790) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4790) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4790) (2 ^ ν₂ (6561 * q + 4790)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6047 (q : ℕ) : step (8192 * q + 6047) = 12288 * q + 9071 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6047) + 1 = 2 ^ 1 * (12288 * q + 9071) := by ring
  have h_odd : (12288 * q + 9071) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6047) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 9071) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 9071) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 9071) (by positivity)]

theorem step2_m8192_6047 (q : ℕ) : step (step (8192 * q + 6047)) = 18432 * q + 13607 := by
  rw [step_m8192_6047 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 9071) + 1 = 2 ^ 1 * (18432 * q + 13607) := by ring
  have h_odd : (18432 * q + 13607) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 9071) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 13607) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 13607) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 13607) (by positivity)]

theorem step3_m8192_6047 (q : ℕ) : step (step (step (8192 * q + 6047))) = 27648 * q + 20411 := by
  rw [step2_m8192_6047 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 13607) + 1 = 2 ^ 1 * (27648 * q + 20411) := by ring
  have h_odd : (27648 * q + 20411) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 13607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 20411) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 20411) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 20411) (by positivity)]

theorem step4_m8192_6047 (q : ℕ) : step (step (step (step (8192 * q + 6047)))) = 41472 * q + 30617 := by
  rw [step3_m8192_6047 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 20411) + 1 = 2 ^ 1 * (41472 * q + 30617) := by ring
  have h_odd : (41472 * q + 30617) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 20411) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 30617) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 30617) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 30617) (by positivity)]

theorem step5_m8192_6047 (q : ℕ) : step (step (step (step (step (8192 * q + 6047))))) = 31104 * q + 22963 := by
  rw [step4_m8192_6047 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 30617) + 1 = 2 ^ 2 * (31104 * q + 22963) := by ring
  have h_odd : (31104 * q + 22963) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 30617) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 22963) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 22963) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 22963) (by positivity)]

theorem step6_m8192_6047 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6047)))))) = 46656 * q + 34445 := by
  rw [step5_m8192_6047 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 22963) + 1 = 2 ^ 1 * (46656 * q + 34445) := by ring
  have h_odd : (46656 * q + 34445) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 22963) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 34445) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 34445) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 34445) (by positivity)]

theorem step7_m8192_6047 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6047))))))) = 17496 * q + 12917 := by
  rw [step6_m8192_6047 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 34445) + 1 = 2 ^ 3 * (17496 * q + 12917) := by ring
  have h_odd : (17496 * q + 12917) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 34445) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (17496 * q + 12917) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (17496 * q + 12917) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 12917) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6047 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6047 (q : ℕ) (hq : 8192 * q + 6047 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6047)))))))) < 8192 * q + 6047 := by
  rw [step7_m8192_6047 q]
  have h_bound : step (17496 * q + 12917) ≤ 6561 * q + 4844 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 12917) + 1 = 2 ^ 3 * (6561 * q + 4844) := by ring
    have hne : (6561 * q + 4844) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 12917) + 1) = 3 + ν₂ (6561 * q + 4844) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4844) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4844) (2 ^ ν₂ (6561 * q + 4844)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6113 (q : ℕ) : step (8192 * q + 6113) = 6144 * q + 4585 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6113) + 1 = 2 ^ 2 * (6144 * q + 4585) := by ring
  have h_odd : (6144 * q + 4585) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6113) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4585) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4585) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4585) (by positivity)]

theorem step2_m8192_6113 (q : ℕ) : step (step (8192 * q + 6113)) = 4608 * q + 3439 := by
  rw [step_m8192_6113 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4585) + 1 = 2 ^ 2 * (4608 * q + 3439) := by ring
  have h_odd : (4608 * q + 3439) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4585) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 3439) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 3439) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 3439) (by positivity)]

theorem step3_m8192_6113 (q : ℕ) : step (step (step (8192 * q + 6113))) = 6912 * q + 5159 := by
  rw [step2_m8192_6113 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 3439) + 1 = 2 ^ 1 * (6912 * q + 5159) := by ring
  have h_odd : (6912 * q + 5159) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 3439) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 5159) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 5159) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 5159) (by positivity)]

theorem step4_m8192_6113 (q : ℕ) : step (step (step (step (8192 * q + 6113)))) = 10368 * q + 7739 := by
  rw [step3_m8192_6113 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 5159) + 1 = 2 ^ 1 * (10368 * q + 7739) := by ring
  have h_odd : (10368 * q + 7739) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 5159) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 7739) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 7739) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7739) (by positivity)]

theorem step5_m8192_6113 (q : ℕ) : step (step (step (step (step (8192 * q + 6113))))) = 15552 * q + 11609 := by
  rw [step4_m8192_6113 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7739) + 1 = 2 ^ 1 * (15552 * q + 11609) := by ring
  have h_odd : (15552 * q + 11609) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7739) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 11609) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 11609) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11609) (by positivity)]

theorem step6_m8192_6113 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6113)))))) = 11664 * q + 8707 := by
  rw [step5_m8192_6113 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11609) + 1 = 2 ^ 2 * (11664 * q + 8707) := by ring
  have h_odd : (11664 * q + 8707) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11609) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 8707) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 8707) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 8707) (by positivity)]

theorem step7_m8192_6113 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6113))))))) = 17496 * q + 13061 := by
  rw [step6_m8192_6113 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 8707) + 1 = 2 ^ 1 * (17496 * q + 13061) := by ring
  have h_odd : (17496 * q + 13061) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 8707) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 13061) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 13061) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 13061) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6113 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6113 (q : ℕ) (hq : 8192 * q + 6113 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6113)))))))) < 8192 * q + 6113 := by
  rw [step7_m8192_6113 q]
  have h_bound : step (17496 * q + 13061) ≤ 6561 * q + 4898 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 13061) + 1 = 2 ^ 3 * (6561 * q + 4898) := by ring
    have hne : (6561 * q + 4898) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 13061) + 1) = 3 + ν₂ (6561 * q + 4898) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4898) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4898) (2 ^ ν₂ (6561 * q + 4898)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6185 (q : ℕ) : step (8192 * q + 6185) = 6144 * q + 4639 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6185) + 1 = 2 ^ 2 * (6144 * q + 4639) := by ring
  have h_odd : (6144 * q + 4639) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6185) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4639) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4639) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4639) (by positivity)]

theorem step2_m8192_6185 (q : ℕ) : step (step (8192 * q + 6185)) = 9216 * q + 6959 := by
  rw [step_m8192_6185 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4639) + 1 = 2 ^ 1 * (9216 * q + 6959) := by ring
  have h_odd : (9216 * q + 6959) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4639) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 6959) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 6959) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 6959) (by positivity)]

theorem step3_m8192_6185 (q : ℕ) : step (step (step (8192 * q + 6185))) = 13824 * q + 10439 := by
  rw [step2_m8192_6185 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 6959) + 1 = 2 ^ 1 * (13824 * q + 10439) := by ring
  have h_odd : (13824 * q + 10439) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 6959) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 10439) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 10439) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10439) (by positivity)]

theorem step4_m8192_6185 (q : ℕ) : step (step (step (step (8192 * q + 6185)))) = 20736 * q + 15659 := by
  rw [step3_m8192_6185 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10439) + 1 = 2 ^ 1 * (20736 * q + 15659) := by ring
  have h_odd : (20736 * q + 15659) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10439) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 15659) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 15659) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 15659) (by positivity)]

theorem step5_m8192_6185 (q : ℕ) : step (step (step (step (step (8192 * q + 6185))))) = 31104 * q + 23489 := by
  rw [step4_m8192_6185 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 15659) + 1 = 2 ^ 1 * (31104 * q + 23489) := by ring
  have h_odd : (31104 * q + 23489) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 15659) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 23489) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 23489) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 23489) (by positivity)]

theorem step6_m8192_6185 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6185)))))) = 23328 * q + 17617 := by
  rw [step5_m8192_6185 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 23489) + 1 = 2 ^ 2 * (23328 * q + 17617) := by ring
  have h_odd : (23328 * q + 17617) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 23489) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 17617) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 17617) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 17617) (by positivity)]

theorem step7_m8192_6185 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6185))))))) = 17496 * q + 13213 := by
  rw [step6_m8192_6185 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 17617) + 1 = 2 ^ 2 * (17496 * q + 13213) := by ring
  have h_odd : (17496 * q + 13213) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 17617) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 13213) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 13213) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 13213) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6185 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6185 (q : ℕ) (hq : 8192 * q + 6185 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6185)))))))) < 8192 * q + 6185 := by
  rw [step7_m8192_6185 q]
  have h_bound : step (17496 * q + 13213) ≤ 6561 * q + 4955 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 13213) + 1 = 2 ^ 3 * (6561 * q + 4955) := by ring
    have hne : (6561 * q + 4955) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 13213) + 1) = 3 + ν₂ (6561 * q + 4955) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4955) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4955) (2 ^ ν₂ (6561 * q + 4955)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6215 (q : ℕ) : step (8192 * q + 6215) = 12288 * q + 9323 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6215) + 1 = 2 ^ 1 * (12288 * q + 9323) := by ring
  have h_odd : (12288 * q + 9323) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6215) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 9323) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 9323) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 9323) (by positivity)]

theorem step2_m8192_6215 (q : ℕ) : step (step (8192 * q + 6215)) = 18432 * q + 13985 := by
  rw [step_m8192_6215 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 9323) + 1 = 2 ^ 1 * (18432 * q + 13985) := by ring
  have h_odd : (18432 * q + 13985) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 9323) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 13985) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 13985) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 13985) (by positivity)]

theorem step3_m8192_6215 (q : ℕ) : step (step (step (8192 * q + 6215))) = 13824 * q + 10489 := by
  rw [step2_m8192_6215 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 13985) + 1 = 2 ^ 2 * (13824 * q + 10489) := by ring
  have h_odd : (13824 * q + 10489) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 13985) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 10489) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 10489) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10489) (by positivity)]

theorem step4_m8192_6215 (q : ℕ) : step (step (step (step (8192 * q + 6215)))) = 10368 * q + 7867 := by
  rw [step3_m8192_6215 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10489) + 1 = 2 ^ 2 * (10368 * q + 7867) := by ring
  have h_odd : (10368 * q + 7867) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10489) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 7867) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 7867) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7867) (by positivity)]

theorem step5_m8192_6215 (q : ℕ) : step (step (step (step (step (8192 * q + 6215))))) = 15552 * q + 11801 := by
  rw [step4_m8192_6215 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7867) + 1 = 2 ^ 1 * (15552 * q + 11801) := by ring
  have h_odd : (15552 * q + 11801) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7867) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 11801) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 11801) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11801) (by positivity)]

theorem step6_m8192_6215 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6215)))))) = 11664 * q + 8851 := by
  rw [step5_m8192_6215 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11801) + 1 = 2 ^ 2 * (11664 * q + 8851) := by ring
  have h_odd : (11664 * q + 8851) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11801) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 8851) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 8851) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 8851) (by positivity)]

theorem step7_m8192_6215 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6215))))))) = 17496 * q + 13277 := by
  rw [step6_m8192_6215 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 8851) + 1 = 2 ^ 1 * (17496 * q + 13277) := by ring
  have h_odd : (17496 * q + 13277) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 8851) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 13277) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 13277) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 13277) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6215 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6215 (q : ℕ) (hq : 8192 * q + 6215 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6215)))))))) < 8192 * q + 6215 := by
  rw [step7_m8192_6215 q]
  have h_bound : step (17496 * q + 13277) ≤ 6561 * q + 4979 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 13277) + 1 = 2 ^ 3 * (6561 * q + 4979) := by ring
    have hne : (6561 * q + 4979) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 13277) + 1) = 3 + ν₂ (6561 * q + 4979) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 4979) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 4979) (2 ^ ν₂ (6561 * q + 4979)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6281 (q : ℕ) : step (8192 * q + 6281) = 6144 * q + 4711 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6281) + 1 = 2 ^ 2 * (6144 * q + 4711) := by ring
  have h_odd : (6144 * q + 4711) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6281) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4711) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4711) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4711) (by positivity)]

theorem step2_m8192_6281 (q : ℕ) : step (step (8192 * q + 6281)) = 9216 * q + 7067 := by
  rw [step_m8192_6281 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4711) + 1 = 2 ^ 1 * (9216 * q + 7067) := by ring
  have h_odd : (9216 * q + 7067) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4711) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7067) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7067) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7067) (by positivity)]

theorem step3_m8192_6281 (q : ℕ) : step (step (step (8192 * q + 6281))) = 13824 * q + 10601 := by
  rw [step2_m8192_6281 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7067) + 1 = 2 ^ 1 * (13824 * q + 10601) := by ring
  have h_odd : (13824 * q + 10601) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7067) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 10601) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 10601) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10601) (by positivity)]

theorem step4_m8192_6281 (q : ℕ) : step (step (step (step (8192 * q + 6281)))) = 10368 * q + 7951 := by
  rw [step3_m8192_6281 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10601) + 1 = 2 ^ 2 * (10368 * q + 7951) := by ring
  have h_odd : (10368 * q + 7951) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10601) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 7951) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 7951) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 7951) (by positivity)]

theorem step5_m8192_6281 (q : ℕ) : step (step (step (step (step (8192 * q + 6281))))) = 15552 * q + 11927 := by
  rw [step4_m8192_6281 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 7951) + 1 = 2 ^ 1 * (15552 * q + 11927) := by ring
  have h_odd : (15552 * q + 11927) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 7951) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 11927) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 11927) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 11927) (by positivity)]

theorem step6_m8192_6281 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6281)))))) = 23328 * q + 17891 := by
  rw [step5_m8192_6281 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 11927) + 1 = 2 ^ 1 * (23328 * q + 17891) := by ring
  have h_odd : (23328 * q + 17891) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 11927) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 17891) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 17891) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 17891) (by positivity)]

theorem step7_m8192_6281 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6281))))))) = 34992 * q + 26837 := by
  rw [step6_m8192_6281 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 17891) + 1 = 2 ^ 1 * (34992 * q + 26837) := by ring
  have h_odd : (34992 * q + 26837) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 17891) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 26837) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 26837) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 26837) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6281 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6281 (q : ℕ) (hq : 8192 * q + 6281 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6281)))))))) < 8192 * q + 6281 := by
  rw [step7_m8192_6281 q]
  have h_bound : step (34992 * q + 26837) ≤ 6561 * q + 5032 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 26837) + 1 = 2 ^ 4 * (6561 * q + 5032) := by ring
    have hne : (6561 * q + 5032) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 26837) + 1) = 4 + ν₂ (6561 * q + 5032) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 5032) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5032) (2 ^ ν₂ (6561 * q + 5032)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6375 (q : ℕ) : step (8192 * q + 6375) = 12288 * q + 9563 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6375) + 1 = 2 ^ 1 * (12288 * q + 9563) := by ring
  have h_odd : (12288 * q + 9563) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6375) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 9563) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 9563) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 9563) (by positivity)]

theorem step2_m8192_6375 (q : ℕ) : step (step (8192 * q + 6375)) = 18432 * q + 14345 := by
  rw [step_m8192_6375 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 9563) + 1 = 2 ^ 1 * (18432 * q + 14345) := by ring
  have h_odd : (18432 * q + 14345) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 9563) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 14345) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 14345) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 14345) (by positivity)]

theorem step3_m8192_6375 (q : ℕ) : step (step (step (8192 * q + 6375))) = 13824 * q + 10759 := by
  rw [step2_m8192_6375 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 14345) + 1 = 2 ^ 2 * (13824 * q + 10759) := by ring
  have h_odd : (13824 * q + 10759) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 14345) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 10759) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 10759) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 10759) (by positivity)]

theorem step4_m8192_6375 (q : ℕ) : step (step (step (step (8192 * q + 6375)))) = 20736 * q + 16139 := by
  rw [step3_m8192_6375 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 10759) + 1 = 2 ^ 1 * (20736 * q + 16139) := by ring
  have h_odd : (20736 * q + 16139) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 10759) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 16139) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 16139) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 16139) (by positivity)]

theorem step5_m8192_6375 (q : ℕ) : step (step (step (step (step (8192 * q + 6375))))) = 31104 * q + 24209 := by
  rw [step4_m8192_6375 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 16139) + 1 = 2 ^ 1 * (31104 * q + 24209) := by ring
  have h_odd : (31104 * q + 24209) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 16139) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 24209) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 24209) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 24209) (by positivity)]

theorem step6_m8192_6375 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6375)))))) = 23328 * q + 18157 := by
  rw [step5_m8192_6375 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 24209) + 1 = 2 ^ 2 * (23328 * q + 18157) := by ring
  have h_odd : (23328 * q + 18157) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 24209) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 18157) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 18157) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 18157) (by positivity)]

theorem step7_m8192_6375 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6375))))))) = 8748 * q + 6809 := by
  rw [step6_m8192_6375 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 18157) + 1 = 2 ^ 3 * (8748 * q + 6809) := by ring
  have h_odd : (8748 * q + 6809) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 18157) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 6809) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 6809) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 6809) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6375 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6375 (q : ℕ) (hq : 8192 * q + 6375 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6375)))))))) < 8192 * q + 6375 := by
  rw [step7_m8192_6375 q]
  have h_bound : step (8748 * q + 6809) ≤ 6561 * q + 5107 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 6809) + 1 = 2 ^ 2 * (6561 * q + 5107) := by ring
    have hne : (6561 * q + 5107) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 6809) + 1) = 2 + ν₂ (6561 * q + 5107) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 5107) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5107) (2 ^ ν₂ (6561 * q + 5107)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6559 (q : ℕ) : step (8192 * q + 6559) = 12288 * q + 9839 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6559) + 1 = 2 ^ 1 * (12288 * q + 9839) := by ring
  have h_odd : (12288 * q + 9839) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6559) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 9839) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 9839) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 9839) (by positivity)]

theorem step2_m8192_6559 (q : ℕ) : step (step (8192 * q + 6559)) = 18432 * q + 14759 := by
  rw [step_m8192_6559 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 9839) + 1 = 2 ^ 1 * (18432 * q + 14759) := by ring
  have h_odd : (18432 * q + 14759) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 9839) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 14759) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 14759) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 14759) (by positivity)]

theorem step3_m8192_6559 (q : ℕ) : step (step (step (8192 * q + 6559))) = 27648 * q + 22139 := by
  rw [step2_m8192_6559 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 14759) + 1 = 2 ^ 1 * (27648 * q + 22139) := by ring
  have h_odd : (27648 * q + 22139) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 14759) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 22139) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 22139) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 22139) (by positivity)]

theorem step4_m8192_6559 (q : ℕ) : step (step (step (step (8192 * q + 6559)))) = 41472 * q + 33209 := by
  rw [step3_m8192_6559 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 22139) + 1 = 2 ^ 1 * (41472 * q + 33209) := by ring
  have h_odd : (41472 * q + 33209) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 22139) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 33209) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 33209) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 33209) (by positivity)]

theorem step5_m8192_6559 (q : ℕ) : step (step (step (step (step (8192 * q + 6559))))) = 31104 * q + 24907 := by
  rw [step4_m8192_6559 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 33209) + 1 = 2 ^ 2 * (31104 * q + 24907) := by ring
  have h_odd : (31104 * q + 24907) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 33209) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 24907) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 24907) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 24907) (by positivity)]

theorem step6_m8192_6559 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6559)))))) = 46656 * q + 37361 := by
  rw [step5_m8192_6559 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 24907) + 1 = 2 ^ 1 * (46656 * q + 37361) := by ring
  have h_odd : (46656 * q + 37361) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 24907) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 37361) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 37361) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 37361) (by positivity)]

theorem step7_m8192_6559 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6559))))))) = 34992 * q + 28021 := by
  rw [step6_m8192_6559 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 37361) + 1 = 2 ^ 2 * (34992 * q + 28021) := by ring
  have h_odd : (34992 * q + 28021) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 37361) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (34992 * q + 28021) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (34992 * q + 28021) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 28021) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6559 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6559 (q : ℕ) (hq : 8192 * q + 6559 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6559)))))))) < 8192 * q + 6559 := by
  rw [step7_m8192_6559 q]
  have h_bound : step (34992 * q + 28021) ≤ 6561 * q + 5254 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 28021) + 1 = 2 ^ 4 * (6561 * q + 5254) := by ring
    have hne : (6561 * q + 5254) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 28021) + 1) = 4 + ν₂ (6561 * q + 5254) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 5254) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5254) (2 ^ ν₂ (6561 * q + 5254)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6607 (q : ℕ) : step (8192 * q + 6607) = 12288 * q + 9911 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6607) + 1 = 2 ^ 1 * (12288 * q + 9911) := by ring
  have h_odd : (12288 * q + 9911) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6607) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 9911) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 9911) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 9911) (by positivity)]

theorem step2_m8192_6607 (q : ℕ) : step (step (8192 * q + 6607)) = 18432 * q + 14867 := by
  rw [step_m8192_6607 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 9911) + 1 = 2 ^ 1 * (18432 * q + 14867) := by ring
  have h_odd : (18432 * q + 14867) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 9911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 14867) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 14867) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 14867) (by positivity)]

theorem step3_m8192_6607 (q : ℕ) : step (step (step (8192 * q + 6607))) = 27648 * q + 22301 := by
  rw [step2_m8192_6607 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 14867) + 1 = 2 ^ 1 * (27648 * q + 22301) := by ring
  have h_odd : (27648 * q + 22301) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 14867) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 22301) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 22301) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 22301) (by positivity)]

theorem step4_m8192_6607 (q : ℕ) : step (step (step (step (8192 * q + 6607)))) = 10368 * q + 8363 := by
  rw [step3_m8192_6607 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 22301) + 1 = 2 ^ 3 * (10368 * q + 8363) := by ring
  have h_odd : (10368 * q + 8363) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 22301) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (10368 * q + 8363) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (10368 * q + 8363) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 8363) (by positivity)]

theorem step5_m8192_6607 (q : ℕ) : step (step (step (step (step (8192 * q + 6607))))) = 15552 * q + 12545 := by
  rw [step4_m8192_6607 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 8363) + 1 = 2 ^ 1 * (15552 * q + 12545) := by ring
  have h_odd : (15552 * q + 12545) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 8363) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 12545) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 12545) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 12545) (by positivity)]

theorem step6_m8192_6607 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6607)))))) = 11664 * q + 9409 := by
  rw [step5_m8192_6607 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 12545) + 1 = 2 ^ 2 * (11664 * q + 9409) := by ring
  have h_odd : (11664 * q + 9409) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 12545) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 9409) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 9409) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 9409) (by positivity)]

theorem step7_m8192_6607 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6607))))))) = 8748 * q + 7057 := by
  rw [step6_m8192_6607 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 9409) + 1 = 2 ^ 2 * (8748 * q + 7057) := by ring
  have h_odd : (8748 * q + 7057) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 9409) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 7057) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 7057) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 7057) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6607 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6607 (q : ℕ) (hq : 8192 * q + 6607 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6607)))))))) < 8192 * q + 6607 := by
  rw [step7_m8192_6607 q]
  have h_bound : step (8748 * q + 7057) ≤ 6561 * q + 5293 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 7057) + 1 = 2 ^ 2 * (6561 * q + 5293) := by ring
    have hne : (6561 * q + 5293) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 7057) + 1) = 2 + ν₂ (6561 * q + 5293) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 5293) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5293) (2 ^ ν₂ (6561 * q + 5293)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6631 (q : ℕ) : step (8192 * q + 6631) = 12288 * q + 9947 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6631) + 1 = 2 ^ 1 * (12288 * q + 9947) := by ring
  have h_odd : (12288 * q + 9947) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6631) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 9947) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 9947) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 9947) (by positivity)]

theorem step2_m8192_6631 (q : ℕ) : step (step (8192 * q + 6631)) = 18432 * q + 14921 := by
  rw [step_m8192_6631 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 9947) + 1 = 2 ^ 1 * (18432 * q + 14921) := by ring
  have h_odd : (18432 * q + 14921) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 9947) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 14921) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 14921) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 14921) (by positivity)]

theorem step3_m8192_6631 (q : ℕ) : step (step (step (8192 * q + 6631))) = 13824 * q + 11191 := by
  rw [step2_m8192_6631 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 14921) + 1 = 2 ^ 2 * (13824 * q + 11191) := by ring
  have h_odd : (13824 * q + 11191) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 14921) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 11191) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 11191) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11191) (by positivity)]

theorem step4_m8192_6631 (q : ℕ) : step (step (step (step (8192 * q + 6631)))) = 20736 * q + 16787 := by
  rw [step3_m8192_6631 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11191) + 1 = 2 ^ 1 * (20736 * q + 16787) := by ring
  have h_odd : (20736 * q + 16787) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11191) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 16787) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 16787) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 16787) (by positivity)]

theorem step5_m8192_6631 (q : ℕ) : step (step (step (step (step (8192 * q + 6631))))) = 31104 * q + 25181 := by
  rw [step4_m8192_6631 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 16787) + 1 = 2 ^ 1 * (31104 * q + 25181) := by ring
  have h_odd : (31104 * q + 25181) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 16787) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 25181) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 25181) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 25181) (by positivity)]

theorem step6_m8192_6631 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6631)))))) = 11664 * q + 9443 := by
  rw [step5_m8192_6631 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 25181) + 1 = 2 ^ 3 * (11664 * q + 9443) := by ring
  have h_odd : (11664 * q + 9443) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 25181) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 9443) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 9443) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 9443) (by positivity)]

theorem step7_m8192_6631 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6631))))))) = 17496 * q + 14165 := by
  rw [step6_m8192_6631 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 9443) + 1 = 2 ^ 1 * (17496 * q + 14165) := by ring
  have h_odd : (17496 * q + 14165) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 9443) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 14165) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 14165) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 14165) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6631 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6631 (q : ℕ) (hq : 8192 * q + 6631 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6631)))))))) < 8192 * q + 6631 := by
  rw [step7_m8192_6631 q]
  have h_bound : step (17496 * q + 14165) ≤ 6561 * q + 5312 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 14165) + 1 = 2 ^ 3 * (6561 * q + 5312) := by ring
    have hne : (6561 * q + 5312) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 14165) + 1) = 3 + ν₂ (6561 * q + 5312) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 5312) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5312) (2 ^ ν₂ (6561 * q + 5312)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6633 (q : ℕ) : step (8192 * q + 6633) = 6144 * q + 4975 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6633) + 1 = 2 ^ 2 * (6144 * q + 4975) := by ring
  have h_odd : (6144 * q + 4975) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6633) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 4975) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 4975) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 4975) (by positivity)]

theorem step2_m8192_6633 (q : ℕ) : step (step (8192 * q + 6633)) = 9216 * q + 7463 := by
  rw [step_m8192_6633 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 4975) + 1 = 2 ^ 1 * (9216 * q + 7463) := by ring
  have h_odd : (9216 * q + 7463) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 4975) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7463) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7463) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7463) (by positivity)]

theorem step3_m8192_6633 (q : ℕ) : step (step (step (8192 * q + 6633))) = 13824 * q + 11195 := by
  rw [step2_m8192_6633 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7463) + 1 = 2 ^ 1 * (13824 * q + 11195) := by ring
  have h_odd : (13824 * q + 11195) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7463) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 11195) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 11195) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11195) (by positivity)]

theorem step4_m8192_6633 (q : ℕ) : step (step (step (step (8192 * q + 6633)))) = 20736 * q + 16793 := by
  rw [step3_m8192_6633 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11195) + 1 = 2 ^ 1 * (20736 * q + 16793) := by ring
  have h_odd : (20736 * q + 16793) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11195) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 16793) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 16793) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 16793) (by positivity)]

theorem step5_m8192_6633 (q : ℕ) : step (step (step (step (step (8192 * q + 6633))))) = 15552 * q + 12595 := by
  rw [step4_m8192_6633 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 16793) + 1 = 2 ^ 2 * (15552 * q + 12595) := by ring
  have h_odd : (15552 * q + 12595) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 16793) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 12595) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 12595) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 12595) (by positivity)]

theorem step6_m8192_6633 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6633)))))) = 23328 * q + 18893 := by
  rw [step5_m8192_6633 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 12595) + 1 = 2 ^ 1 * (23328 * q + 18893) := by ring
  have h_odd : (23328 * q + 18893) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 12595) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 18893) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 18893) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 18893) (by positivity)]

theorem step7_m8192_6633 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6633))))))) = 8748 * q + 7085 := by
  rw [step6_m8192_6633 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 18893) + 1 = 2 ^ 3 * (8748 * q + 7085) := by ring
  have h_odd : (8748 * q + 7085) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 18893) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 7085) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 7085) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 7085) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6633 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6633 (q : ℕ) (hq : 8192 * q + 6633 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6633)))))))) < 8192 * q + 6633 := by
  rw [step7_m8192_6633 q]
  have h_bound : step (8748 * q + 7085) ≤ 6561 * q + 5314 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 7085) + 1 = 2 ^ 2 * (6561 * q + 5314) := by ring
    have hne : (6561 * q + 5314) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 7085) + 1) = 2 + ν₂ (6561 * q + 5314) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 5314) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5314) (2 ^ ν₂ (6561 * q + 5314)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6697 (q : ℕ) : step (8192 * q + 6697) = 6144 * q + 5023 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6697) + 1 = 2 ^ 2 * (6144 * q + 5023) := by ring
  have h_odd : (6144 * q + 5023) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6697) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 5023) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 5023) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5023) (by positivity)]

theorem step2_m8192_6697 (q : ℕ) : step (step (8192 * q + 6697)) = 9216 * q + 7535 := by
  rw [step_m8192_6697 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5023) + 1 = 2 ^ 1 * (9216 * q + 7535) := by ring
  have h_odd : (9216 * q + 7535) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5023) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7535) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7535) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7535) (by positivity)]

theorem step3_m8192_6697 (q : ℕ) : step (step (step (8192 * q + 6697))) = 13824 * q + 11303 := by
  rw [step2_m8192_6697 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7535) + 1 = 2 ^ 1 * (13824 * q + 11303) := by ring
  have h_odd : (13824 * q + 11303) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7535) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 11303) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 11303) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11303) (by positivity)]

theorem step4_m8192_6697 (q : ℕ) : step (step (step (step (8192 * q + 6697)))) = 20736 * q + 16955 := by
  rw [step3_m8192_6697 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11303) + 1 = 2 ^ 1 * (20736 * q + 16955) := by ring
  have h_odd : (20736 * q + 16955) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11303) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 16955) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 16955) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 16955) (by positivity)]

theorem step5_m8192_6697 (q : ℕ) : step (step (step (step (step (8192 * q + 6697))))) = 31104 * q + 25433 := by
  rw [step4_m8192_6697 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 16955) + 1 = 2 ^ 1 * (31104 * q + 25433) := by ring
  have h_odd : (31104 * q + 25433) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 16955) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 25433) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 25433) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 25433) (by positivity)]

theorem step6_m8192_6697 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6697)))))) = 23328 * q + 19075 := by
  rw [step5_m8192_6697 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 25433) + 1 = 2 ^ 2 * (23328 * q + 19075) := by ring
  have h_odd : (23328 * q + 19075) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 25433) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 19075) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 19075) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 19075) (by positivity)]

theorem step7_m8192_6697 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6697))))))) = 34992 * q + 28613 := by
  rw [step6_m8192_6697 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 19075) + 1 = 2 ^ 1 * (34992 * q + 28613) := by ring
  have h_odd : (34992 * q + 28613) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 19075) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 28613) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 28613) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 28613) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6697 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6697 (q : ℕ) (hq : 8192 * q + 6697 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6697)))))))) < 8192 * q + 6697 := by
  rw [step7_m8192_6697 q]
  have h_bound : step (34992 * q + 28613) ≤ 6561 * q + 5365 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 28613) + 1 = 2 ^ 4 * (6561 * q + 5365) := by ring
    have hne : (6561 * q + 5365) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 28613) + 1) = 4 + ν₂ (6561 * q + 5365) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 5365) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5365) (2 ^ ν₂ (6561 * q + 5365)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6747 (q : ℕ) : step (8192 * q + 6747) = 12288 * q + 10121 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6747) + 1 = 2 ^ 1 * (12288 * q + 10121) := by ring
  have h_odd : (12288 * q + 10121) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6747) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 10121) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 10121) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 10121) (by positivity)]

theorem step2_m8192_6747 (q : ℕ) : step (step (8192 * q + 6747)) = 9216 * q + 7591 := by
  rw [step_m8192_6747 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 10121) + 1 = 2 ^ 2 * (9216 * q + 7591) := by ring
  have h_odd : (9216 * q + 7591) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 10121) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 7591) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 7591) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7591) (by positivity)]

theorem step3_m8192_6747 (q : ℕ) : step (step (step (8192 * q + 6747))) = 13824 * q + 11387 := by
  rw [step2_m8192_6747 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7591) + 1 = 2 ^ 1 * (13824 * q + 11387) := by ring
  have h_odd : (13824 * q + 11387) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7591) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 11387) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 11387) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11387) (by positivity)]

theorem step4_m8192_6747 (q : ℕ) : step (step (step (step (8192 * q + 6747)))) = 20736 * q + 17081 := by
  rw [step3_m8192_6747 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11387) + 1 = 2 ^ 1 * (20736 * q + 17081) := by ring
  have h_odd : (20736 * q + 17081) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11387) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 17081) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 17081) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 17081) (by positivity)]

theorem step5_m8192_6747 (q : ℕ) : step (step (step (step (step (8192 * q + 6747))))) = 15552 * q + 12811 := by
  rw [step4_m8192_6747 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 17081) + 1 = 2 ^ 2 * (15552 * q + 12811) := by ring
  have h_odd : (15552 * q + 12811) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 17081) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 12811) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 12811) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 12811) (by positivity)]

theorem step6_m8192_6747 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6747)))))) = 23328 * q + 19217 := by
  rw [step5_m8192_6747 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 12811) + 1 = 2 ^ 1 * (23328 * q + 19217) := by ring
  have h_odd : (23328 * q + 19217) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 12811) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 19217) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 19217) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 19217) (by positivity)]

theorem step7_m8192_6747 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6747))))))) = 17496 * q + 14413 := by
  rw [step6_m8192_6747 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 19217) + 1 = 2 ^ 2 * (17496 * q + 14413) := by ring
  have h_odd : (17496 * q + 14413) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 19217) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 14413) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 14413) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 14413) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6747 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6747 (q : ℕ) (hq : 8192 * q + 6747 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6747)))))))) < 8192 * q + 6747 := by
  rw [step7_m8192_6747 q]
  have h_bound : step (17496 * q + 14413) ≤ 6561 * q + 5405 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 14413) + 1 = 2 ^ 3 * (6561 * q + 5405) := by ring
    have hne : (6561 * q + 5405) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 14413) + 1) = 3 + ν₂ (6561 * q + 5405) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 5405) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5405) (2 ^ ν₂ (6561 * q + 5405)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6815 (q : ℕ) : step (8192 * q + 6815) = 12288 * q + 10223 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6815) + 1 = 2 ^ 1 * (12288 * q + 10223) := by ring
  have h_odd : (12288 * q + 10223) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6815) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 10223) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 10223) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 10223) (by positivity)]

theorem step2_m8192_6815 (q : ℕ) : step (step (8192 * q + 6815)) = 18432 * q + 15335 := by
  rw [step_m8192_6815 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 10223) + 1 = 2 ^ 1 * (18432 * q + 15335) := by ring
  have h_odd : (18432 * q + 15335) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 10223) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 15335) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 15335) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 15335) (by positivity)]

theorem step3_m8192_6815 (q : ℕ) : step (step (step (8192 * q + 6815))) = 27648 * q + 23003 := by
  rw [step2_m8192_6815 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 15335) + 1 = 2 ^ 1 * (27648 * q + 23003) := by ring
  have h_odd : (27648 * q + 23003) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 15335) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 23003) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 23003) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 23003) (by positivity)]

theorem step4_m8192_6815 (q : ℕ) : step (step (step (step (8192 * q + 6815)))) = 41472 * q + 34505 := by
  rw [step3_m8192_6815 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 23003) + 1 = 2 ^ 1 * (41472 * q + 34505) := by ring
  have h_odd : (41472 * q + 34505) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 23003) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 34505) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 34505) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 34505) (by positivity)]

theorem step5_m8192_6815 (q : ℕ) : step (step (step (step (step (8192 * q + 6815))))) = 31104 * q + 25879 := by
  rw [step4_m8192_6815 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 34505) + 1 = 2 ^ 2 * (31104 * q + 25879) := by ring
  have h_odd : (31104 * q + 25879) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 34505) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 25879) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 25879) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 25879) (by positivity)]

theorem step6_m8192_6815 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6815)))))) = 46656 * q + 38819 := by
  rw [step5_m8192_6815 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 25879) + 1 = 2 ^ 1 * (46656 * q + 38819) := by ring
  have h_odd : (46656 * q + 38819) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 25879) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (46656 * q + 38819) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (46656 * q + 38819) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (46656 * q + 38819) (by positivity)]

theorem step7_m8192_6815 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6815))))))) = 69984 * q + 58229 := by
  rw [step6_m8192_6815 q]
  unfold step
  have h3n1 : 3 * (46656 * q + 38819) + 1 = 2 ^ 1 * (69984 * q + 58229) := by ring
  have h_odd : (69984 * q + 58229) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (46656 * q + 38819) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (69984 * q + 58229) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (69984 * q + 58229) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (69984 * q + 58229) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6815 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6815 (q : ℕ) (hq : 8192 * q + 6815 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6815)))))))) < 8192 * q + 6815 := by
  rw [step7_m8192_6815 q]
  have h_bound : step (69984 * q + 58229) ≤ 6561 * q + 5459 := by
    unfold step
    have h3n1 : 3 * (69984 * q + 58229) + 1 = 2 ^ 5 * (6561 * q + 5459) := by ring
    have hne : (6561 * q + 5459) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (69984 * q + 58229) + 1) = 5 + ν₂ (6561 * q + 5459) := by
      rw [h3n1, ν₂_mul (2 ^ 5) (6561 * q + 5459) (by positivity) hne, ν₂_pow_two' 5]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5459) (2 ^ ν₂ (6561 * q + 5459)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6881 (q : ℕ) : step (8192 * q + 6881) = 6144 * q + 5161 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6881) + 1 = 2 ^ 2 * (6144 * q + 5161) := by ring
  have h_odd : (6144 * q + 5161) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6881) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 5161) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 5161) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5161) (by positivity)]

theorem step2_m8192_6881 (q : ℕ) : step (step (8192 * q + 6881)) = 4608 * q + 3871 := by
  rw [step_m8192_6881 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5161) + 1 = 2 ^ 2 * (4608 * q + 3871) := by ring
  have h_odd : (4608 * q + 3871) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5161) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 3871) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 3871) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 3871) (by positivity)]

theorem step3_m8192_6881 (q : ℕ) : step (step (step (8192 * q + 6881))) = 6912 * q + 5807 := by
  rw [step2_m8192_6881 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 3871) + 1 = 2 ^ 1 * (6912 * q + 5807) := by ring
  have h_odd : (6912 * q + 5807) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 3871) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 5807) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 5807) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 5807) (by positivity)]

theorem step4_m8192_6881 (q : ℕ) : step (step (step (step (8192 * q + 6881)))) = 10368 * q + 8711 := by
  rw [step3_m8192_6881 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 5807) + 1 = 2 ^ 1 * (10368 * q + 8711) := by ring
  have h_odd : (10368 * q + 8711) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 5807) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 8711) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 8711) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 8711) (by positivity)]

theorem step5_m8192_6881 (q : ℕ) : step (step (step (step (step (8192 * q + 6881))))) = 15552 * q + 13067 := by
  rw [step4_m8192_6881 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 8711) + 1 = 2 ^ 1 * (15552 * q + 13067) := by ring
  have h_odd : (15552 * q + 13067) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 8711) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 13067) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 13067) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 13067) (by positivity)]

theorem step6_m8192_6881 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6881)))))) = 23328 * q + 19601 := by
  rw [step5_m8192_6881 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 13067) + 1 = 2 ^ 1 * (23328 * q + 19601) := by ring
  have h_odd : (23328 * q + 19601) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 13067) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 19601) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 19601) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 19601) (by positivity)]

theorem step7_m8192_6881 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6881))))))) = 17496 * q + 14701 := by
  rw [step6_m8192_6881 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 19601) + 1 = 2 ^ 2 * (17496 * q + 14701) := by ring
  have h_odd : (17496 * q + 14701) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 19601) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 14701) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 14701) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 14701) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6881 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6881 (q : ℕ) (hq : 8192 * q + 6881 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6881)))))))) < 8192 * q + 6881 := by
  rw [step7_m8192_6881 q]
  have h_bound : step (17496 * q + 14701) ≤ 6561 * q + 5513 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 14701) + 1 = 2 ^ 3 * (6561 * q + 5513) := by ring
    have hne : (6561 * q + 5513) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 14701) + 1) = 3 + ν₂ (6561 * q + 5513) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 5513) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5513) (2 ^ ν₂ (6561 * q + 5513)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6889 (q : ℕ) : step (8192 * q + 6889) = 6144 * q + 5167 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6889) + 1 = 2 ^ 2 * (6144 * q + 5167) := by ring
  have h_odd : (6144 * q + 5167) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6889) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 5167) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 5167) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5167) (by positivity)]

theorem step2_m8192_6889 (q : ℕ) : step (step (8192 * q + 6889)) = 9216 * q + 7751 := by
  rw [step_m8192_6889 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5167) + 1 = 2 ^ 1 * (9216 * q + 7751) := by ring
  have h_odd : (9216 * q + 7751) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5167) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7751) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7751) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7751) (by positivity)]

theorem step3_m8192_6889 (q : ℕ) : step (step (step (8192 * q + 6889))) = 13824 * q + 11627 := by
  rw [step2_m8192_6889 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7751) + 1 = 2 ^ 1 * (13824 * q + 11627) := by ring
  have h_odd : (13824 * q + 11627) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7751) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 11627) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 11627) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11627) (by positivity)]

theorem step4_m8192_6889 (q : ℕ) : step (step (step (step (8192 * q + 6889)))) = 20736 * q + 17441 := by
  rw [step3_m8192_6889 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11627) + 1 = 2 ^ 1 * (20736 * q + 17441) := by ring
  have h_odd : (20736 * q + 17441) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11627) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 17441) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 17441) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 17441) (by positivity)]

theorem step5_m8192_6889 (q : ℕ) : step (step (step (step (step (8192 * q + 6889))))) = 15552 * q + 13081 := by
  rw [step4_m8192_6889 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 17441) + 1 = 2 ^ 2 * (15552 * q + 13081) := by ring
  have h_odd : (15552 * q + 13081) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 17441) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 13081) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 13081) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 13081) (by positivity)]

theorem step6_m8192_6889 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6889)))))) = 11664 * q + 9811 := by
  rw [step5_m8192_6889 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 13081) + 1 = 2 ^ 2 * (11664 * q + 9811) := by ring
  have h_odd : (11664 * q + 9811) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 13081) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 9811) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 9811) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 9811) (by positivity)]

theorem step7_m8192_6889 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6889))))))) = 17496 * q + 14717 := by
  rw [step6_m8192_6889 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 9811) + 1 = 2 ^ 1 * (17496 * q + 14717) := by ring
  have h_odd : (17496 * q + 14717) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 9811) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 14717) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 14717) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 14717) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6889 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6889 (q : ℕ) (hq : 8192 * q + 6889 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6889)))))))) < 8192 * q + 6889 := by
  rw [step7_m8192_6889 q]
  have h_bound : step (17496 * q + 14717) ≤ 6561 * q + 5519 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 14717) + 1 = 2 ^ 3 * (6561 * q + 5519) := by ring
    have hne : (6561 * q + 5519) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 14717) + 1) = 3 + ν₂ (6561 * q + 5519) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 5519) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5519) (2 ^ ν₂ (6561 * q + 5519)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6921 (q : ℕ) : step (8192 * q + 6921) = 6144 * q + 5191 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6921) + 1 = 2 ^ 2 * (6144 * q + 5191) := by ring
  have h_odd : (6144 * q + 5191) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6921) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 5191) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 5191) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5191) (by positivity)]

theorem step2_m8192_6921 (q : ℕ) : step (step (8192 * q + 6921)) = 9216 * q + 7787 := by
  rw [step_m8192_6921 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5191) + 1 = 2 ^ 1 * (9216 * q + 7787) := by ring
  have h_odd : (9216 * q + 7787) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5191) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 7787) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 7787) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 7787) (by positivity)]

theorem step3_m8192_6921 (q : ℕ) : step (step (step (8192 * q + 6921))) = 13824 * q + 11681 := by
  rw [step2_m8192_6921 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 7787) + 1 = 2 ^ 1 * (13824 * q + 11681) := by ring
  have h_odd : (13824 * q + 11681) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 7787) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 11681) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 11681) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11681) (by positivity)]

theorem step4_m8192_6921 (q : ℕ) : step (step (step (step (8192 * q + 6921)))) = 10368 * q + 8761 := by
  rw [step3_m8192_6921 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11681) + 1 = 2 ^ 2 * (10368 * q + 8761) := by ring
  have h_odd : (10368 * q + 8761) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11681) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 8761) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 8761) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 8761) (by positivity)]

theorem step5_m8192_6921 (q : ℕ) : step (step (step (step (step (8192 * q + 6921))))) = 7776 * q + 6571 := by
  rw [step4_m8192_6921 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 8761) + 1 = 2 ^ 2 * (7776 * q + 6571) := by ring
  have h_odd : (7776 * q + 6571) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 8761) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 6571) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 6571) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 6571) (by positivity)]

theorem step6_m8192_6921 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6921)))))) = 11664 * q + 9857 := by
  rw [step5_m8192_6921 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 6571) + 1 = 2 ^ 1 * (11664 * q + 9857) := by ring
  have h_odd : (11664 * q + 9857) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 6571) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 9857) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 9857) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 9857) (by positivity)]

theorem step7_m8192_6921 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6921))))))) = 8748 * q + 7393 := by
  rw [step6_m8192_6921 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 9857) + 1 = 2 ^ 2 * (8748 * q + 7393) := by ring
  have h_odd : (8748 * q + 7393) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 9857) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 7393) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 7393) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 7393) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6921 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6921 (q : ℕ) (hq : 8192 * q + 6921 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6921)))))))) < 8192 * q + 6921 := by
  rw [step7_m8192_6921 q]
  have h_bound : step (8748 * q + 7393) ≤ 6561 * q + 5545 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 7393) + 1 = 2 ^ 2 * (6561 * q + 5545) := by ring
    have hne : (6561 * q + 5545) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 7393) + 1) = 2 + ν₂ (6561 * q + 5545) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 5545) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5545) (2 ^ ν₂ (6561 * q + 5545)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_6983 (q : ℕ) : step (8192 * q + 6983) = 12288 * q + 10475 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 6983) + 1 = 2 ^ 1 * (12288 * q + 10475) := by ring
  have h_odd : (12288 * q + 10475) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 6983) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 10475) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 10475) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 10475) (by positivity)]

theorem step2_m8192_6983 (q : ℕ) : step (step (8192 * q + 6983)) = 18432 * q + 15713 := by
  rw [step_m8192_6983 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 10475) + 1 = 2 ^ 1 * (18432 * q + 15713) := by ring
  have h_odd : (18432 * q + 15713) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 10475) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 15713) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 15713) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 15713) (by positivity)]

theorem step3_m8192_6983 (q : ℕ) : step (step (step (8192 * q + 6983))) = 13824 * q + 11785 := by
  rw [step2_m8192_6983 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 15713) + 1 = 2 ^ 2 * (13824 * q + 11785) := by ring
  have h_odd : (13824 * q + 11785) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 15713) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 11785) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 11785) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11785) (by positivity)]

theorem step4_m8192_6983 (q : ℕ) : step (step (step (step (8192 * q + 6983)))) = 10368 * q + 8839 := by
  rw [step3_m8192_6983 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11785) + 1 = 2 ^ 2 * (10368 * q + 8839) := by ring
  have h_odd : (10368 * q + 8839) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11785) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 8839) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 8839) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 8839) (by positivity)]

theorem step5_m8192_6983 (q : ℕ) : step (step (step (step (step (8192 * q + 6983))))) = 15552 * q + 13259 := by
  rw [step4_m8192_6983 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 8839) + 1 = 2 ^ 1 * (15552 * q + 13259) := by ring
  have h_odd : (15552 * q + 13259) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 8839) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 13259) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 13259) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 13259) (by positivity)]

theorem step6_m8192_6983 (q : ℕ) : step (step (step (step (step (step (8192 * q + 6983)))))) = 23328 * q + 19889 := by
  rw [step5_m8192_6983 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 13259) + 1 = 2 ^ 1 * (23328 * q + 19889) := by ring
  have h_odd : (23328 * q + 19889) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 13259) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 19889) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 19889) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 19889) (by positivity)]

theorem step7_m8192_6983 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 6983))))))) = 17496 * q + 14917 := by
  rw [step6_m8192_6983 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 19889) + 1 = 2 ^ 2 * (17496 * q + 14917) := by ring
  have h_odd : (17496 * q + 14917) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 19889) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 14917) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 14917) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 14917) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 6983 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_6983 (q : ℕ) (hq : 8192 * q + 6983 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 6983)))))))) < 8192 * q + 6983 := by
  rw [step7_m8192_6983 q]
  have h_bound : step (17496 * q + 14917) ≤ 6561 * q + 5594 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 14917) + 1 = 2 ^ 3 * (6561 * q + 5594) := by ring
    have hne : (6561 * q + 5594) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 14917) + 1) = 3 + ν₂ (6561 * q + 5594) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 5594) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5594) (2 ^ ν₂ (6561 * q + 5594)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7023 (q : ℕ) : step (8192 * q + 7023) = 12288 * q + 10535 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7023) + 1 = 2 ^ 1 * (12288 * q + 10535) := by ring
  have h_odd : (12288 * q + 10535) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7023) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 10535) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 10535) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 10535) (by positivity)]

theorem step2_m8192_7023 (q : ℕ) : step (step (8192 * q + 7023)) = 18432 * q + 15803 := by
  rw [step_m8192_7023 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 10535) + 1 = 2 ^ 1 * (18432 * q + 15803) := by ring
  have h_odd : (18432 * q + 15803) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 10535) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 15803) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 15803) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 15803) (by positivity)]

theorem step3_m8192_7023 (q : ℕ) : step (step (step (8192 * q + 7023))) = 27648 * q + 23705 := by
  rw [step2_m8192_7023 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 15803) + 1 = 2 ^ 1 * (27648 * q + 23705) := by ring
  have h_odd : (27648 * q + 23705) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 15803) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 23705) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 23705) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 23705) (by positivity)]

theorem step4_m8192_7023 (q : ℕ) : step (step (step (step (8192 * q + 7023)))) = 20736 * q + 17779 := by
  rw [step3_m8192_7023 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 23705) + 1 = 2 ^ 2 * (20736 * q + 17779) := by ring
  have h_odd : (20736 * q + 17779) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 23705) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 17779) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 17779) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 17779) (by positivity)]

theorem step5_m8192_7023 (q : ℕ) : step (step (step (step (step (8192 * q + 7023))))) = 31104 * q + 26669 := by
  rw [step4_m8192_7023 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 17779) + 1 = 2 ^ 1 * (31104 * q + 26669) := by ring
  have h_odd : (31104 * q + 26669) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 17779) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 26669) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 26669) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 26669) (by positivity)]

theorem step6_m8192_7023 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7023)))))) = 11664 * q + 10001 := by
  rw [step5_m8192_7023 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 26669) + 1 = 2 ^ 3 * (11664 * q + 10001) := by ring
  have h_odd : (11664 * q + 10001) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 26669) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 10001) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 10001) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 10001) (by positivity)]

theorem step7_m8192_7023 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7023))))))) = 8748 * q + 7501 := by
  rw [step6_m8192_7023 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 10001) + 1 = 2 ^ 2 * (8748 * q + 7501) := by ring
  have h_odd : (8748 * q + 7501) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 10001) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 7501) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 7501) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 7501) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7023 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7023 (q : ℕ) (hq : 8192 * q + 7023 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7023)))))))) < 8192 * q + 7023 := by
  rw [step7_m8192_7023 q]
  have h_bound : step (8748 * q + 7501) ≤ 6561 * q + 5626 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 7501) + 1 = 2 ^ 2 * (6561 * q + 5626) := by ring
    have hne : (6561 * q + 5626) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 7501) + 1) = 2 + ν₂ (6561 * q + 5626) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 5626) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5626) (2 ^ ν₂ (6561 * q + 5626)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7079 (q : ℕ) : step (8192 * q + 7079) = 12288 * q + 10619 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7079) + 1 = 2 ^ 1 * (12288 * q + 10619) := by ring
  have h_odd : (12288 * q + 10619) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7079) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 10619) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 10619) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 10619) (by positivity)]

theorem step2_m8192_7079 (q : ℕ) : step (step (8192 * q + 7079)) = 18432 * q + 15929 := by
  rw [step_m8192_7079 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 10619) + 1 = 2 ^ 1 * (18432 * q + 15929) := by ring
  have h_odd : (18432 * q + 15929) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 10619) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 15929) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 15929) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 15929) (by positivity)]

theorem step3_m8192_7079 (q : ℕ) : step (step (step (8192 * q + 7079))) = 13824 * q + 11947 := by
  rw [step2_m8192_7079 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 15929) + 1 = 2 ^ 2 * (13824 * q + 11947) := by ring
  have h_odd : (13824 * q + 11947) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 15929) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 11947) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 11947) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 11947) (by positivity)]

theorem step4_m8192_7079 (q : ℕ) : step (step (step (step (8192 * q + 7079)))) = 20736 * q + 17921 := by
  rw [step3_m8192_7079 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 11947) + 1 = 2 ^ 1 * (20736 * q + 17921) := by ring
  have h_odd : (20736 * q + 17921) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 11947) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 17921) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 17921) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 17921) (by positivity)]

theorem step5_m8192_7079 (q : ℕ) : step (step (step (step (step (8192 * q + 7079))))) = 15552 * q + 13441 := by
  rw [step4_m8192_7079 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 17921) + 1 = 2 ^ 2 * (15552 * q + 13441) := by ring
  have h_odd : (15552 * q + 13441) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 17921) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 13441) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 13441) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 13441) (by positivity)]

theorem step6_m8192_7079 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7079)))))) = 11664 * q + 10081 := by
  rw [step5_m8192_7079 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 13441) + 1 = 2 ^ 2 * (11664 * q + 10081) := by ring
  have h_odd : (11664 * q + 10081) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 13441) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 10081) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 10081) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 10081) (by positivity)]

theorem step7_m8192_7079 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7079))))))) = 8748 * q + 7561 := by
  rw [step6_m8192_7079 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 10081) + 1 = 2 ^ 2 * (8748 * q + 7561) := by ring
  have h_odd : (8748 * q + 7561) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 10081) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 7561) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 7561) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 7561) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7079 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7079 (q : ℕ) (hq : 8192 * q + 7079 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7079)))))))) < 8192 * q + 7079 := by
  rw [step7_m8192_7079 q]
  have h_bound : step (8748 * q + 7561) ≤ 6561 * q + 5671 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 7561) + 1 = 2 ^ 2 * (6561 * q + 5671) := by ring
    have hne : (6561 * q + 5671) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 7561) + 1) = 2 + ν₂ (6561 * q + 5671) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 5671) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5671) (2 ^ ν₂ (6561 * q + 5671)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7259 (q : ℕ) : step (8192 * q + 7259) = 12288 * q + 10889 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7259) + 1 = 2 ^ 1 * (12288 * q + 10889) := by ring
  have h_odd : (12288 * q + 10889) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7259) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 10889) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 10889) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 10889) (by positivity)]

theorem step2_m8192_7259 (q : ℕ) : step (step (8192 * q + 7259)) = 9216 * q + 8167 := by
  rw [step_m8192_7259 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 10889) + 1 = 2 ^ 2 * (9216 * q + 8167) := by ring
  have h_odd : (9216 * q + 8167) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 10889) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 8167) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 8167) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 8167) (by positivity)]

theorem step3_m8192_7259 (q : ℕ) : step (step (step (8192 * q + 7259))) = 13824 * q + 12251 := by
  rw [step2_m8192_7259 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 8167) + 1 = 2 ^ 1 * (13824 * q + 12251) := by ring
  have h_odd : (13824 * q + 12251) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 8167) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 12251) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 12251) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 12251) (by positivity)]

theorem step4_m8192_7259 (q : ℕ) : step (step (step (step (8192 * q + 7259)))) = 20736 * q + 18377 := by
  rw [step3_m8192_7259 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 12251) + 1 = 2 ^ 1 * (20736 * q + 18377) := by ring
  have h_odd : (20736 * q + 18377) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 12251) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 18377) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 18377) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 18377) (by positivity)]

theorem step5_m8192_7259 (q : ℕ) : step (step (step (step (step (8192 * q + 7259))))) = 15552 * q + 13783 := by
  rw [step4_m8192_7259 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 18377) + 1 = 2 ^ 2 * (15552 * q + 13783) := by ring
  have h_odd : (15552 * q + 13783) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 18377) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 13783) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 13783) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 13783) (by positivity)]

theorem step6_m8192_7259 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7259)))))) = 23328 * q + 20675 := by
  rw [step5_m8192_7259 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 13783) + 1 = 2 ^ 1 * (23328 * q + 20675) := by ring
  have h_odd : (23328 * q + 20675) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 13783) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 20675) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 20675) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 20675) (by positivity)]

theorem step7_m8192_7259 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7259))))))) = 34992 * q + 31013 := by
  rw [step6_m8192_7259 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 20675) + 1 = 2 ^ 1 * (34992 * q + 31013) := by ring
  have h_odd : (34992 * q + 31013) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 20675) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 31013) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 31013) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 31013) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7259 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7259 (q : ℕ) (hq : 8192 * q + 7259 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7259)))))))) < 8192 * q + 7259 := by
  rw [step7_m8192_7259 q]
  have h_bound : step (34992 * q + 31013) ≤ 6561 * q + 5815 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 31013) + 1 = 2 ^ 4 * (6561 * q + 5815) := by ring
    have hne : (6561 * q + 5815) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 31013) + 1) = 4 + ν₂ (6561 * q + 5815) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 5815) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5815) (2 ^ ν₂ (6561 * q + 5815)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7375 (q : ℕ) : step (8192 * q + 7375) = 12288 * q + 11063 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7375) + 1 = 2 ^ 1 * (12288 * q + 11063) := by ring
  have h_odd : (12288 * q + 11063) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7375) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11063) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11063) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11063) (by positivity)]

theorem step2_m8192_7375 (q : ℕ) : step (step (8192 * q + 7375)) = 18432 * q + 16595 := by
  rw [step_m8192_7375 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11063) + 1 = 2 ^ 1 * (18432 * q + 16595) := by ring
  have h_odd : (18432 * q + 16595) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11063) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 16595) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 16595) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 16595) (by positivity)]

theorem step3_m8192_7375 (q : ℕ) : step (step (step (8192 * q + 7375))) = 27648 * q + 24893 := by
  rw [step2_m8192_7375 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 16595) + 1 = 2 ^ 1 * (27648 * q + 24893) := by ring
  have h_odd : (27648 * q + 24893) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 16595) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 24893) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 24893) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 24893) (by positivity)]

theorem step4_m8192_7375 (q : ℕ) : step (step (step (step (8192 * q + 7375)))) = 10368 * q + 9335 := by
  rw [step3_m8192_7375 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 24893) + 1 = 2 ^ 3 * (10368 * q + 9335) := by ring
  have h_odd : (10368 * q + 9335) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 24893) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (10368 * q + 9335) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (10368 * q + 9335) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 9335) (by positivity)]

theorem step5_m8192_7375 (q : ℕ) : step (step (step (step (step (8192 * q + 7375))))) = 15552 * q + 14003 := by
  rw [step4_m8192_7375 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 9335) + 1 = 2 ^ 1 * (15552 * q + 14003) := by ring
  have h_odd : (15552 * q + 14003) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 9335) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 14003) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 14003) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 14003) (by positivity)]

theorem step6_m8192_7375 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7375)))))) = 23328 * q + 21005 := by
  rw [step5_m8192_7375 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 14003) + 1 = 2 ^ 1 * (23328 * q + 21005) := by ring
  have h_odd : (23328 * q + 21005) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 14003) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 21005) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 21005) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 21005) (by positivity)]

theorem step7_m8192_7375 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7375))))))) = 8748 * q + 7877 := by
  rw [step6_m8192_7375 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 21005) + 1 = 2 ^ 3 * (8748 * q + 7877) := by ring
  have h_odd : (8748 * q + 7877) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 21005) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 7877) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 7877) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 7877) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7375 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7375 (q : ℕ) (hq : 8192 * q + 7375 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7375)))))))) < 8192 * q + 7375 := by
  rw [step7_m8192_7375 q]
  have h_bound : step (8748 * q + 7877) ≤ 6561 * q + 5908 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 7877) + 1 = 2 ^ 2 * (6561 * q + 5908) := by ring
    have hne : (6561 * q + 5908) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 7877) + 1) = 2 + ν₂ (6561 * q + 5908) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 5908) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5908) (2 ^ ν₂ (6561 * q + 5908)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7393 (q : ℕ) : step (8192 * q + 7393) = 6144 * q + 5545 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7393) + 1 = 2 ^ 2 * (6144 * q + 5545) := by ring
  have h_odd : (6144 * q + 5545) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7393) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 5545) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 5545) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5545) (by positivity)]

theorem step2_m8192_7393 (q : ℕ) : step (step (8192 * q + 7393)) = 4608 * q + 4159 := by
  rw [step_m8192_7393 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5545) + 1 = 2 ^ 2 * (4608 * q + 4159) := by ring
  have h_odd : (4608 * q + 4159) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5545) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (4608 * q + 4159) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (4608 * q + 4159) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4608 * q + 4159) (by positivity)]

theorem step3_m8192_7393 (q : ℕ) : step (step (step (8192 * q + 7393))) = 6912 * q + 6239 := by
  rw [step2_m8192_7393 q]
  unfold step
  have h3n1 : 3 * (4608 * q + 4159) + 1 = 2 ^ 1 * (6912 * q + 6239) := by ring
  have h_odd : (6912 * q + 6239) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (4608 * q + 4159) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (6912 * q + 6239) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (6912 * q + 6239) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 6239) (by positivity)]

theorem step4_m8192_7393 (q : ℕ) : step (step (step (step (8192 * q + 7393)))) = 10368 * q + 9359 := by
  rw [step3_m8192_7393 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 6239) + 1 = 2 ^ 1 * (10368 * q + 9359) := by ring
  have h_odd : (10368 * q + 9359) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 6239) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (10368 * q + 9359) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (10368 * q + 9359) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 9359) (by positivity)]

theorem step5_m8192_7393 (q : ℕ) : step (step (step (step (step (8192 * q + 7393))))) = 15552 * q + 14039 := by
  rw [step4_m8192_7393 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 9359) + 1 = 2 ^ 1 * (15552 * q + 14039) := by ring
  have h_odd : (15552 * q + 14039) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 9359) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 14039) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 14039) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 14039) (by positivity)]

theorem step6_m8192_7393 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7393)))))) = 23328 * q + 21059 := by
  rw [step5_m8192_7393 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 14039) + 1 = 2 ^ 1 * (23328 * q + 21059) := by ring
  have h_odd : (23328 * q + 21059) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 14039) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 21059) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 21059) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 21059) (by positivity)]

theorem step7_m8192_7393 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7393))))))) = 34992 * q + 31589 := by
  rw [step6_m8192_7393 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 21059) + 1 = 2 ^ 1 * (34992 * q + 31589) := by ring
  have h_odd : (34992 * q + 31589) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 21059) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 31589) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 31589) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 31589) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7393 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7393 (q : ℕ) (hq : 8192 * q + 7393 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7393)))))))) < 8192 * q + 7393 := by
  rw [step7_m8192_7393 q]
  have h_bound : step (34992 * q + 31589) ≤ 6561 * q + 5923 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 31589) + 1 = 2 ^ 4 * (6561 * q + 5923) := by ring
    have hne : (6561 * q + 5923) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 31589) + 1) = 4 + ν₂ (6561 * q + 5923) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 5923) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5923) (2 ^ ν₂ (6561 * q + 5923)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7399 (q : ℕ) : step (8192 * q + 7399) = 12288 * q + 11099 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7399) + 1 = 2 ^ 1 * (12288 * q + 11099) := by ring
  have h_odd : (12288 * q + 11099) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7399) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11099) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11099) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11099) (by positivity)]

theorem step2_m8192_7399 (q : ℕ) : step (step (8192 * q + 7399)) = 18432 * q + 16649 := by
  rw [step_m8192_7399 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11099) + 1 = 2 ^ 1 * (18432 * q + 16649) := by ring
  have h_odd : (18432 * q + 16649) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11099) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 16649) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 16649) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 16649) (by positivity)]

theorem step3_m8192_7399 (q : ℕ) : step (step (step (8192 * q + 7399))) = 13824 * q + 12487 := by
  rw [step2_m8192_7399 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 16649) + 1 = 2 ^ 2 * (13824 * q + 12487) := by ring
  have h_odd : (13824 * q + 12487) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 16649) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 12487) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 12487) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 12487) (by positivity)]

theorem step4_m8192_7399 (q : ℕ) : step (step (step (step (8192 * q + 7399)))) = 20736 * q + 18731 := by
  rw [step3_m8192_7399 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 12487) + 1 = 2 ^ 1 * (20736 * q + 18731) := by ring
  have h_odd : (20736 * q + 18731) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 12487) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 18731) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 18731) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 18731) (by positivity)]

theorem step5_m8192_7399 (q : ℕ) : step (step (step (step (step (8192 * q + 7399))))) = 31104 * q + 28097 := by
  rw [step4_m8192_7399 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 18731) + 1 = 2 ^ 1 * (31104 * q + 28097) := by ring
  have h_odd : (31104 * q + 28097) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 18731) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 28097) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 28097) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 28097) (by positivity)]

theorem step6_m8192_7399 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7399)))))) = 23328 * q + 21073 := by
  rw [step5_m8192_7399 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 28097) + 1 = 2 ^ 2 * (23328 * q + 21073) := by ring
  have h_odd : (23328 * q + 21073) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 28097) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 21073) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 21073) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 21073) (by positivity)]

theorem step7_m8192_7399 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7399))))))) = 17496 * q + 15805 := by
  rw [step6_m8192_7399 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 21073) + 1 = 2 ^ 2 * (17496 * q + 15805) := by ring
  have h_odd : (17496 * q + 15805) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 21073) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 15805) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 15805) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 15805) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7399 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7399 (q : ℕ) (hq : 8192 * q + 7399 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7399)))))))) < 8192 * q + 7399 := by
  rw [step7_m8192_7399 q]
  have h_bound : step (17496 * q + 15805) ≤ 6561 * q + 5927 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 15805) + 1 = 2 ^ 3 * (6561 * q + 5927) := by ring
    have hne : (6561 * q + 5927) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 15805) + 1) = 3 + ν₂ (6561 * q + 5927) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 5927) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 5927) (2 ^ ν₂ (6561 * q + 5927)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7495 (q : ℕ) : step (8192 * q + 7495) = 12288 * q + 11243 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7495) + 1 = 2 ^ 1 * (12288 * q + 11243) := by ring
  have h_odd : (12288 * q + 11243) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7495) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11243) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11243) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11243) (by positivity)]

theorem step2_m8192_7495 (q : ℕ) : step (step (8192 * q + 7495)) = 18432 * q + 16865 := by
  rw [step_m8192_7495 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11243) + 1 = 2 ^ 1 * (18432 * q + 16865) := by ring
  have h_odd : (18432 * q + 16865) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11243) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 16865) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 16865) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 16865) (by positivity)]

theorem step3_m8192_7495 (q : ℕ) : step (step (step (8192 * q + 7495))) = 13824 * q + 12649 := by
  rw [step2_m8192_7495 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 16865) + 1 = 2 ^ 2 * (13824 * q + 12649) := by ring
  have h_odd : (13824 * q + 12649) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 16865) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 12649) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 12649) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 12649) (by positivity)]

theorem step4_m8192_7495 (q : ℕ) : step (step (step (step (8192 * q + 7495)))) = 10368 * q + 9487 := by
  rw [step3_m8192_7495 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 12649) + 1 = 2 ^ 2 * (10368 * q + 9487) := by ring
  have h_odd : (10368 * q + 9487) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 12649) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 9487) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 9487) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 9487) (by positivity)]

theorem step5_m8192_7495 (q : ℕ) : step (step (step (step (step (8192 * q + 7495))))) = 15552 * q + 14231 := by
  rw [step4_m8192_7495 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 9487) + 1 = 2 ^ 1 * (15552 * q + 14231) := by ring
  have h_odd : (15552 * q + 14231) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 9487) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 14231) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 14231) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 14231) (by positivity)]

theorem step6_m8192_7495 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7495)))))) = 23328 * q + 21347 := by
  rw [step5_m8192_7495 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 14231) + 1 = 2 ^ 1 * (23328 * q + 21347) := by ring
  have h_odd : (23328 * q + 21347) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 14231) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 21347) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 21347) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 21347) (by positivity)]

theorem step7_m8192_7495 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7495))))))) = 34992 * q + 32021 := by
  rw [step6_m8192_7495 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 21347) + 1 = 2 ^ 1 * (34992 * q + 32021) := by ring
  have h_odd : (34992 * q + 32021) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 21347) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 32021) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 32021) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 32021) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7495 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7495 (q : ℕ) (hq : 8192 * q + 7495 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7495)))))))) < 8192 * q + 7495 := by
  rw [step7_m8192_7495 q]
  have h_bound : step (34992 * q + 32021) ≤ 6561 * q + 6004 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 32021) + 1 = 2 ^ 4 * (6561 * q + 6004) := by ring
    have hne : (6561 * q + 6004) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 32021) + 1) = 4 + ν₂ (6561 * q + 6004) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 6004) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6004) (2 ^ ν₂ (6561 * q + 6004)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7631 (q : ℕ) : step (8192 * q + 7631) = 12288 * q + 11447 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7631) + 1 = 2 ^ 1 * (12288 * q + 11447) := by ring
  have h_odd : (12288 * q + 11447) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7631) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11447) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11447) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11447) (by positivity)]

theorem step2_m8192_7631 (q : ℕ) : step (step (8192 * q + 7631)) = 18432 * q + 17171 := by
  rw [step_m8192_7631 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11447) + 1 = 2 ^ 1 * (18432 * q + 17171) := by ring
  have h_odd : (18432 * q + 17171) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11447) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 17171) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 17171) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 17171) (by positivity)]

theorem step3_m8192_7631 (q : ℕ) : step (step (step (8192 * q + 7631))) = 27648 * q + 25757 := by
  rw [step2_m8192_7631 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 17171) + 1 = 2 ^ 1 * (27648 * q + 25757) := by ring
  have h_odd : (27648 * q + 25757) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 17171) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 25757) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 25757) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 25757) (by positivity)]

theorem step4_m8192_7631 (q : ℕ) : step (step (step (step (8192 * q + 7631)))) = 10368 * q + 9659 := by
  rw [step3_m8192_7631 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 25757) + 1 = 2 ^ 3 * (10368 * q + 9659) := by ring
  have h_odd : (10368 * q + 9659) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 25757) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (10368 * q + 9659) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (10368 * q + 9659) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 9659) (by positivity)]

theorem step5_m8192_7631 (q : ℕ) : step (step (step (step (step (8192 * q + 7631))))) = 15552 * q + 14489 := by
  rw [step4_m8192_7631 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 9659) + 1 = 2 ^ 1 * (15552 * q + 14489) := by ring
  have h_odd : (15552 * q + 14489) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 9659) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (15552 * q + 14489) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (15552 * q + 14489) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 14489) (by positivity)]

theorem step6_m8192_7631 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7631)))))) = 11664 * q + 10867 := by
  rw [step5_m8192_7631 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 14489) + 1 = 2 ^ 2 * (11664 * q + 10867) := by ring
  have h_odd : (11664 * q + 10867) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 14489) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 10867) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 10867) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 10867) (by positivity)]

theorem step7_m8192_7631 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7631))))))) = 17496 * q + 16301 := by
  rw [step6_m8192_7631 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 10867) + 1 = 2 ^ 1 * (17496 * q + 16301) := by ring
  have h_odd : (17496 * q + 16301) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 10867) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 16301) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 16301) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 16301) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7631 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7631 (q : ℕ) (hq : 8192 * q + 7631 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7631)))))))) < 8192 * q + 7631 := by
  rw [step7_m8192_7631 q]
  have h_bound : step (17496 * q + 16301) ≤ 6561 * q + 6113 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 16301) + 1 = 2 ^ 3 * (6561 * q + 6113) := by ring
    have hne : (6561 * q + 6113) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 16301) + 1) = 3 + ν₂ (6561 * q + 6113) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 6113) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6113) (2 ^ ν₂ (6561 * q + 6113)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7657 (q : ℕ) : step (8192 * q + 7657) = 6144 * q + 5743 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7657) + 1 = 2 ^ 2 * (6144 * q + 5743) := by ring
  have h_odd : (6144 * q + 5743) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7657) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 5743) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 5743) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5743) (by positivity)]

theorem step2_m8192_7657 (q : ℕ) : step (step (8192 * q + 7657)) = 9216 * q + 8615 := by
  rw [step_m8192_7657 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5743) + 1 = 2 ^ 1 * (9216 * q + 8615) := by ring
  have h_odd : (9216 * q + 8615) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5743) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 8615) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 8615) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 8615) (by positivity)]

theorem step3_m8192_7657 (q : ℕ) : step (step (step (8192 * q + 7657))) = 13824 * q + 12923 := by
  rw [step2_m8192_7657 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 8615) + 1 = 2 ^ 1 * (13824 * q + 12923) := by ring
  have h_odd : (13824 * q + 12923) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 8615) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 12923) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 12923) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 12923) (by positivity)]

theorem step4_m8192_7657 (q : ℕ) : step (step (step (step (8192 * q + 7657)))) = 20736 * q + 19385 := by
  rw [step3_m8192_7657 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 12923) + 1 = 2 ^ 1 * (20736 * q + 19385) := by ring
  have h_odd : (20736 * q + 19385) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 12923) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 19385) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 19385) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 19385) (by positivity)]

theorem step5_m8192_7657 (q : ℕ) : step (step (step (step (step (8192 * q + 7657))))) = 15552 * q + 14539 := by
  rw [step4_m8192_7657 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 19385) + 1 = 2 ^ 2 * (15552 * q + 14539) := by ring
  have h_odd : (15552 * q + 14539) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 19385) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 14539) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 14539) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 14539) (by positivity)]

theorem step6_m8192_7657 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7657)))))) = 23328 * q + 21809 := by
  rw [step5_m8192_7657 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 14539) + 1 = 2 ^ 1 * (23328 * q + 21809) := by ring
  have h_odd : (23328 * q + 21809) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 14539) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 21809) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 21809) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 21809) (by positivity)]

theorem step7_m8192_7657 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7657))))))) = 17496 * q + 16357 := by
  rw [step6_m8192_7657 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 21809) + 1 = 2 ^ 2 * (17496 * q + 16357) := by ring
  have h_odd : (17496 * q + 16357) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 21809) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (17496 * q + 16357) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (17496 * q + 16357) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 16357) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7657 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7657 (q : ℕ) (hq : 8192 * q + 7657 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7657)))))))) < 8192 * q + 7657 := by
  rw [step7_m8192_7657 q]
  have h_bound : step (17496 * q + 16357) ≤ 6561 * q + 6134 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 16357) + 1 = 2 ^ 3 * (6561 * q + 6134) := by ring
    have hne : (6561 * q + 6134) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 16357) + 1) = 3 + ν₂ (6561 * q + 6134) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 6134) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6134) (2 ^ ν₂ (6561 * q + 6134)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7791 (q : ℕ) : step (8192 * q + 7791) = 12288 * q + 11687 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7791) + 1 = 2 ^ 1 * (12288 * q + 11687) := by ring
  have h_odd : (12288 * q + 11687) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7791) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11687) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11687) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11687) (by positivity)]

theorem step2_m8192_7791 (q : ℕ) : step (step (8192 * q + 7791)) = 18432 * q + 17531 := by
  rw [step_m8192_7791 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11687) + 1 = 2 ^ 1 * (18432 * q + 17531) := by ring
  have h_odd : (18432 * q + 17531) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11687) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 17531) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 17531) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 17531) (by positivity)]

theorem step3_m8192_7791 (q : ℕ) : step (step (step (8192 * q + 7791))) = 27648 * q + 26297 := by
  rw [step2_m8192_7791 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 17531) + 1 = 2 ^ 1 * (27648 * q + 26297) := by ring
  have h_odd : (27648 * q + 26297) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 17531) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 26297) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 26297) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 26297) (by positivity)]

theorem step4_m8192_7791 (q : ℕ) : step (step (step (step (8192 * q + 7791)))) = 20736 * q + 19723 := by
  rw [step3_m8192_7791 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 26297) + 1 = 2 ^ 2 * (20736 * q + 19723) := by ring
  have h_odd : (20736 * q + 19723) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 26297) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 19723) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 19723) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 19723) (by positivity)]

theorem step5_m8192_7791 (q : ℕ) : step (step (step (step (step (8192 * q + 7791))))) = 31104 * q + 29585 := by
  rw [step4_m8192_7791 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 19723) + 1 = 2 ^ 1 * (31104 * q + 29585) := by ring
  have h_odd : (31104 * q + 29585) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 19723) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 29585) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 29585) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 29585) (by positivity)]

theorem step6_m8192_7791 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7791)))))) = 23328 * q + 22189 := by
  rw [step5_m8192_7791 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 29585) + 1 = 2 ^ 2 * (23328 * q + 22189) := by ring
  have h_odd : (23328 * q + 22189) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 29585) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 22189) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 22189) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 22189) (by positivity)]

theorem step7_m8192_7791 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7791))))))) = 8748 * q + 8321 := by
  rw [step6_m8192_7791 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 22189) + 1 = 2 ^ 3 * (8748 * q + 8321) := by ring
  have h_odd : (8748 * q + 8321) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 22189) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 8321) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 8321) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 8321) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7791 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7791 (q : ℕ) (hq : 8192 * q + 7791 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7791)))))))) < 8192 * q + 7791 := by
  rw [step7_m8192_7791 q]
  have h_bound : step (8748 * q + 8321) ≤ 6561 * q + 6241 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 8321) + 1 = 2 ^ 2 * (6561 * q + 6241) := by ring
    have hne : (6561 * q + 6241) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 8321) + 1) = 2 + ν₂ (6561 * q + 6241) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 6241) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6241) (2 ^ ν₂ (6561 * q + 6241)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7847 (q : ℕ) : step (8192 * q + 7847) = 12288 * q + 11771 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7847) + 1 = 2 ^ 1 * (12288 * q + 11771) := by ring
  have h_odd : (12288 * q + 11771) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7847) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11771) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11771) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11771) (by positivity)]

theorem step2_m8192_7847 (q : ℕ) : step (step (8192 * q + 7847)) = 18432 * q + 17657 := by
  rw [step_m8192_7847 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11771) + 1 = 2 ^ 1 * (18432 * q + 17657) := by ring
  have h_odd : (18432 * q + 17657) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11771) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 17657) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 17657) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 17657) (by positivity)]

theorem step3_m8192_7847 (q : ℕ) : step (step (step (8192 * q + 7847))) = 13824 * q + 13243 := by
  rw [step2_m8192_7847 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 17657) + 1 = 2 ^ 2 * (13824 * q + 13243) := by ring
  have h_odd : (13824 * q + 13243) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 17657) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 13243) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 13243) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 13243) (by positivity)]

theorem step4_m8192_7847 (q : ℕ) : step (step (step (step (8192 * q + 7847)))) = 20736 * q + 19865 := by
  rw [step3_m8192_7847 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 13243) + 1 = 2 ^ 1 * (20736 * q + 19865) := by ring
  have h_odd : (20736 * q + 19865) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 13243) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 19865) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 19865) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 19865) (by positivity)]

theorem step5_m8192_7847 (q : ℕ) : step (step (step (step (step (8192 * q + 7847))))) = 15552 * q + 14899 := by
  rw [step4_m8192_7847 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 19865) + 1 = 2 ^ 2 * (15552 * q + 14899) := by ring
  have h_odd : (15552 * q + 14899) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 19865) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 14899) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 14899) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 14899) (by positivity)]

theorem step6_m8192_7847 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7847)))))) = 23328 * q + 22349 := by
  rw [step5_m8192_7847 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 14899) + 1 = 2 ^ 1 * (23328 * q + 22349) := by ring
  have h_odd : (23328 * q + 22349) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 14899) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 22349) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 22349) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 22349) (by positivity)]

theorem step7_m8192_7847 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7847))))))) = 8748 * q + 8381 := by
  rw [step6_m8192_7847 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 22349) + 1 = 2 ^ 3 * (8748 * q + 8381) := by ring
  have h_odd : (8748 * q + 8381) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 22349) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (8748 * q + 8381) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (8748 * q + 8381) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 8381) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7847 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7847 (q : ℕ) (hq : 8192 * q + 7847 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7847)))))))) < 8192 * q + 7847 := by
  rw [step7_m8192_7847 q]
  have h_bound : step (8748 * q + 8381) ≤ 6561 * q + 6286 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 8381) + 1 = 2 ^ 2 * (6561 * q + 6286) := by ring
    have hne : (6561 * q + 6286) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 8381) + 1) = 2 + ν₂ (6561 * q + 6286) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 6286) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6286) (2 ^ ν₂ (6561 * q + 6286)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7911 (q : ℕ) : step (8192 * q + 7911) = 12288 * q + 11867 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7911) + 1 = 2 ^ 1 * (12288 * q + 11867) := by ring
  have h_odd : (12288 * q + 11867) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7911) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11867) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11867) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11867) (by positivity)]

theorem step2_m8192_7911 (q : ℕ) : step (step (8192 * q + 7911)) = 18432 * q + 17801 := by
  rw [step_m8192_7911 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11867) + 1 = 2 ^ 1 * (18432 * q + 17801) := by ring
  have h_odd : (18432 * q + 17801) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11867) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 17801) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 17801) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 17801) (by positivity)]

theorem step3_m8192_7911 (q : ℕ) : step (step (step (8192 * q + 7911))) = 13824 * q + 13351 := by
  rw [step2_m8192_7911 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 17801) + 1 = 2 ^ 2 * (13824 * q + 13351) := by ring
  have h_odd : (13824 * q + 13351) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 17801) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 13351) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 13351) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 13351) (by positivity)]

theorem step4_m8192_7911 (q : ℕ) : step (step (step (step (8192 * q + 7911)))) = 20736 * q + 20027 := by
  rw [step3_m8192_7911 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 13351) + 1 = 2 ^ 1 * (20736 * q + 20027) := by ring
  have h_odd : (20736 * q + 20027) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 13351) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 20027) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 20027) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 20027) (by positivity)]

theorem step5_m8192_7911 (q : ℕ) : step (step (step (step (step (8192 * q + 7911))))) = 31104 * q + 30041 := by
  rw [step4_m8192_7911 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 20027) + 1 = 2 ^ 1 * (31104 * q + 30041) := by ring
  have h_odd : (31104 * q + 30041) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 20027) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 30041) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 30041) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 30041) (by positivity)]

theorem step6_m8192_7911 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7911)))))) = 23328 * q + 22531 := by
  rw [step5_m8192_7911 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 30041) + 1 = 2 ^ 2 * (23328 * q + 22531) := by ring
  have h_odd : (23328 * q + 22531) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 30041) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (23328 * q + 22531) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (23328 * q + 22531) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 22531) (by positivity)]

theorem step7_m8192_7911 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7911))))))) = 34992 * q + 33797 := by
  rw [step6_m8192_7911 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 22531) + 1 = 2 ^ 1 * (34992 * q + 33797) := by ring
  have h_odd : (34992 * q + 33797) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 22531) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 33797) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 33797) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 33797) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7911 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7911 (q : ℕ) (hq : 8192 * q + 7911 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7911)))))))) < 8192 * q + 7911 := by
  rw [step7_m8192_7911 q]
  have h_bound : step (34992 * q + 33797) ≤ 6561 * q + 6337 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 33797) + 1 = 2 ^ 4 * (6561 * q + 6337) := by ring
    have hne : (6561 * q + 6337) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 33797) + 1) = 4 + ν₂ (6561 * q + 6337) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 6337) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6337) (2 ^ ν₂ (6561 * q + 6337)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7945 (q : ℕ) : step (8192 * q + 7945) = 6144 * q + 5959 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7945) + 1 = 2 ^ 2 * (6144 * q + 5959) := by ring
  have h_odd : (6144 * q + 5959) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7945) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 5959) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 5959) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 5959) (by positivity)]

theorem step2_m8192_7945 (q : ℕ) : step (step (8192 * q + 7945)) = 9216 * q + 8939 := by
  rw [step_m8192_7945 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 5959) + 1 = 2 ^ 1 * (9216 * q + 8939) := by ring
  have h_odd : (9216 * q + 8939) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 5959) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 8939) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 8939) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 8939) (by positivity)]

theorem step3_m8192_7945 (q : ℕ) : step (step (step (8192 * q + 7945))) = 13824 * q + 13409 := by
  rw [step2_m8192_7945 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 8939) + 1 = 2 ^ 1 * (13824 * q + 13409) := by ring
  have h_odd : (13824 * q + 13409) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 8939) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 13409) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 13409) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 13409) (by positivity)]

theorem step4_m8192_7945 (q : ℕ) : step (step (step (step (8192 * q + 7945)))) = 10368 * q + 10057 := by
  rw [step3_m8192_7945 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 13409) + 1 = 2 ^ 2 * (10368 * q + 10057) := by ring
  have h_odd : (10368 * q + 10057) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 13409) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (10368 * q + 10057) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (10368 * q + 10057) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (10368 * q + 10057) (by positivity)]

theorem step5_m8192_7945 (q : ℕ) : step (step (step (step (step (8192 * q + 7945))))) = 7776 * q + 7543 := by
  rw [step4_m8192_7945 q]
  unfold step
  have h3n1 : 3 * (10368 * q + 10057) + 1 = 2 ^ 2 * (7776 * q + 7543) := by ring
  have h_odd : (7776 * q + 7543) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (10368 * q + 10057) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (7776 * q + 7543) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (7776 * q + 7543) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (7776 * q + 7543) (by positivity)]

theorem step6_m8192_7945 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7945)))))) = 11664 * q + 11315 := by
  rw [step5_m8192_7945 q]
  unfold step
  have h3n1 : 3 * (7776 * q + 7543) + 1 = 2 ^ 1 * (11664 * q + 11315) := by ring
  have h_odd : (11664 * q + 11315) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (7776 * q + 7543) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (11664 * q + 11315) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (11664 * q + 11315) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 11315) (by positivity)]

theorem step7_m8192_7945 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7945))))))) = 17496 * q + 16973 := by
  rw [step6_m8192_7945 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 11315) + 1 = 2 ^ 1 * (17496 * q + 16973) := by ring
  have h_odd : (17496 * q + 16973) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 11315) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 16973) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 16973) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 16973) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7945 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7945 (q : ℕ) (hq : 8192 * q + 7945 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7945)))))))) < 8192 * q + 7945 := by
  rw [step7_m8192_7945 q]
  have h_bound : step (17496 * q + 16973) ≤ 6561 * q + 6365 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 16973) + 1 = 2 ^ 3 * (6561 * q + 6365) := by ring
    have hne : (6561 * q + 6365) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 16973) + 1) = 3 + ν₂ (6561 * q + 6365) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 6365) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6365) (2 ^ ν₂ (6561 * q + 6365)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_7967 (q : ℕ) : step (8192 * q + 7967) = 12288 * q + 11951 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 7967) + 1 = 2 ^ 1 * (12288 * q + 11951) := by ring
  have h_odd : (12288 * q + 11951) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 7967) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 11951) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 11951) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 11951) (by positivity)]

theorem step2_m8192_7967 (q : ℕ) : step (step (8192 * q + 7967)) = 18432 * q + 17927 := by
  rw [step_m8192_7967 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 11951) + 1 = 2 ^ 1 * (18432 * q + 17927) := by ring
  have h_odd : (18432 * q + 17927) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 11951) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 17927) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 17927) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 17927) (by positivity)]

theorem step3_m8192_7967 (q : ℕ) : step (step (step (8192 * q + 7967))) = 27648 * q + 26891 := by
  rw [step2_m8192_7967 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 17927) + 1 = 2 ^ 1 * (27648 * q + 26891) := by ring
  have h_odd : (27648 * q + 26891) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 17927) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 26891) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 26891) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 26891) (by positivity)]

theorem step4_m8192_7967 (q : ℕ) : step (step (step (step (8192 * q + 7967)))) = 41472 * q + 40337 := by
  rw [step3_m8192_7967 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 26891) + 1 = 2 ^ 1 * (41472 * q + 40337) := by ring
  have h_odd : (41472 * q + 40337) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 26891) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (41472 * q + 40337) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (41472 * q + 40337) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (41472 * q + 40337) (by positivity)]

theorem step5_m8192_7967 (q : ℕ) : step (step (step (step (step (8192 * q + 7967))))) = 31104 * q + 30253 := by
  rw [step4_m8192_7967 q]
  unfold step
  have h3n1 : 3 * (41472 * q + 40337) + 1 = 2 ^ 2 * (31104 * q + 30253) := by ring
  have h_odd : (31104 * q + 30253) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (41472 * q + 40337) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (31104 * q + 30253) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (31104 * q + 30253) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 30253) (by positivity)]

theorem step6_m8192_7967 (q : ℕ) : step (step (step (step (step (step (8192 * q + 7967)))))) = 11664 * q + 11345 := by
  rw [step5_m8192_7967 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 30253) + 1 = 2 ^ 3 * (11664 * q + 11345) := by ring
  have h_odd : (11664 * q + 11345) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 30253) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 11345) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 11345) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 11345) (by positivity)]

theorem step7_m8192_7967 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 7967))))))) = 8748 * q + 8509 := by
  rw [step6_m8192_7967 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 11345) + 1 = 2 ^ 2 * (8748 * q + 8509) := by ring
  have h_odd : (8748 * q + 8509) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 11345) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (8748 * q + 8509) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (8748 * q + 8509) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (8748 * q + 8509) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 7967 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_7967 (q : ℕ) (hq : 8192 * q + 7967 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 7967)))))))) < 8192 * q + 7967 := by
  rw [step7_m8192_7967 q]
  have h_bound : step (8748 * q + 8509) ≤ 6561 * q + 6382 := by
    unfold step
    have h3n1 : 3 * (8748 * q + 8509) + 1 = 2 ^ 2 * (6561 * q + 6382) := by ring
    have hne : (6561 * q + 6382) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (8748 * q + 8509) + 1) = 2 + ν₂ (6561 * q + 6382) := by
      rw [h3n1, ν₂_mul (2 ^ 2) (6561 * q + 6382) (by positivity) hne, ν₂_pow_two' 2]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6382) (2 ^ ν₂ (6561 * q + 6382)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_8047 (q : ℕ) : step (8192 * q + 8047) = 12288 * q + 12071 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 8047) + 1 = 2 ^ 1 * (12288 * q + 12071) := by ring
  have h_odd : (12288 * q + 12071) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 8047) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 12071) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 12071) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 12071) (by positivity)]

theorem step2_m8192_8047 (q : ℕ) : step (step (8192 * q + 8047)) = 18432 * q + 18107 := by
  rw [step_m8192_8047 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 12071) + 1 = 2 ^ 1 * (18432 * q + 18107) := by ring
  have h_odd : (18432 * q + 18107) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 12071) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 18107) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 18107) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 18107) (by positivity)]

theorem step3_m8192_8047 (q : ℕ) : step (step (step (8192 * q + 8047))) = 27648 * q + 27161 := by
  rw [step2_m8192_8047 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 18107) + 1 = 2 ^ 1 * (27648 * q + 27161) := by ring
  have h_odd : (27648 * q + 27161) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 18107) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (27648 * q + 27161) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (27648 * q + 27161) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (27648 * q + 27161) (by positivity)]

theorem step4_m8192_8047 (q : ℕ) : step (step (step (step (8192 * q + 8047)))) = 20736 * q + 20371 := by
  rw [step3_m8192_8047 q]
  unfold step
  have h3n1 : 3 * (27648 * q + 27161) + 1 = 2 ^ 2 * (20736 * q + 20371) := by ring
  have h_odd : (20736 * q + 20371) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (27648 * q + 27161) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (20736 * q + 20371) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (20736 * q + 20371) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 20371) (by positivity)]

theorem step5_m8192_8047 (q : ℕ) : step (step (step (step (step (8192 * q + 8047))))) = 31104 * q + 30557 := by
  rw [step4_m8192_8047 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 20371) + 1 = 2 ^ 1 * (31104 * q + 30557) := by ring
  have h_odd : (31104 * q + 30557) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 20371) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (31104 * q + 30557) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (31104 * q + 30557) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (31104 * q + 30557) (by positivity)]

theorem step6_m8192_8047 (q : ℕ) : step (step (step (step (step (step (8192 * q + 8047)))))) = 11664 * q + 11459 := by
  rw [step5_m8192_8047 q]
  unfold step
  have h3n1 : 3 * (31104 * q + 30557) + 1 = 2 ^ 3 * (11664 * q + 11459) := by ring
  have h_odd : (11664 * q + 11459) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (31104 * q + 30557) + 1) = 3 := by
    rw [h3n1, ν₂_mul (2 ^ 3) (11664 * q + 11459) (by positivity) (by omega),
        ν₂_pow_two' 3, ν₂_odd (11664 * q + 11459) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 11459) (by positivity)]

theorem step7_m8192_8047 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 8047))))))) = 17496 * q + 17189 := by
  rw [step6_m8192_8047 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 11459) + 1 = 2 ^ 1 * (17496 * q + 17189) := by ring
  have h_odd : (17496 * q + 17189) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 11459) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 17189) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 17189) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 17189) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 8047 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_8047 (q : ℕ) (hq : 8192 * q + 8047 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 8047)))))))) < 8192 * q + 8047 := by
  rw [step7_m8192_8047 q]
  have h_bound : step (17496 * q + 17189) ≤ 6561 * q + 6446 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 17189) + 1 = 2 ^ 3 * (6561 * q + 6446) := by ring
    have hne : (6561 * q + 6446) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 17189) + 1) = 3 + ν₂ (6561 * q + 6446) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 6446) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6446) (2 ^ ν₂ (6561 * q + 6446)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_8103 (q : ℕ) : step (8192 * q + 8103) = 12288 * q + 12155 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 8103) + 1 = 2 ^ 1 * (12288 * q + 12155) := by ring
  have h_odd : (12288 * q + 12155) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 8103) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (12288 * q + 12155) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (12288 * q + 12155) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 12155) (by positivity)]

theorem step2_m8192_8103 (q : ℕ) : step (step (8192 * q + 8103)) = 18432 * q + 18233 := by
  rw [step_m8192_8103 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 12155) + 1 = 2 ^ 1 * (18432 * q + 18233) := by ring
  have h_odd : (18432 * q + 18233) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 12155) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (18432 * q + 18233) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (18432 * q + 18233) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (18432 * q + 18233) (by positivity)]

theorem step3_m8192_8103 (q : ℕ) : step (step (step (8192 * q + 8103))) = 13824 * q + 13675 := by
  rw [step2_m8192_8103 q]
  unfold step
  have h3n1 : 3 * (18432 * q + 18233) + 1 = 2 ^ 2 * (13824 * q + 13675) := by ring
  have h_odd : (13824 * q + 13675) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (18432 * q + 18233) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (13824 * q + 13675) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (13824 * q + 13675) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 13675) (by positivity)]

theorem step4_m8192_8103 (q : ℕ) : step (step (step (step (8192 * q + 8103)))) = 20736 * q + 20513 := by
  rw [step3_m8192_8103 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 13675) + 1 = 2 ^ 1 * (20736 * q + 20513) := by ring
  have h_odd : (20736 * q + 20513) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 13675) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 20513) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 20513) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 20513) (by positivity)]

theorem step5_m8192_8103 (q : ℕ) : step (step (step (step (step (8192 * q + 8103))))) = 15552 * q + 15385 := by
  rw [step4_m8192_8103 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 20513) + 1 = 2 ^ 2 * (15552 * q + 15385) := by ring
  have h_odd : (15552 * q + 15385) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 20513) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 15385) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 15385) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 15385) (by positivity)]

theorem step6_m8192_8103 (q : ℕ) : step (step (step (step (step (step (8192 * q + 8103)))))) = 11664 * q + 11539 := by
  rw [step5_m8192_8103 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 15385) + 1 = 2 ^ 2 * (11664 * q + 11539) := by ring
  have h_odd : (11664 * q + 11539) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 15385) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (11664 * q + 11539) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (11664 * q + 11539) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (11664 * q + 11539) (by positivity)]

theorem step7_m8192_8103 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 8103))))))) = 17496 * q + 17309 := by
  rw [step6_m8192_8103 q]
  unfold step
  have h3n1 : 3 * (11664 * q + 11539) + 1 = 2 ^ 1 * (17496 * q + 17309) := by ring
  have h_odd : (17496 * q + 17309) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (11664 * q + 11539) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (17496 * q + 17309) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (17496 * q + 17309) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (17496 * q + 17309) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 8103 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_8103 (q : ℕ) (hq : 8192 * q + 8103 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 8103)))))))) < 8192 * q + 8103 := by
  rw [step7_m8192_8103 q]
  have h_bound : step (17496 * q + 17309) ≤ 6561 * q + 6491 := by
    unfold step
    have h3n1 : 3 * (17496 * q + 17309) + 1 = 2 ^ 3 * (6561 * q + 6491) := by ring
    have hne : (6561 * q + 6491) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (17496 * q + 17309) + 1) = 3 + ν₂ (6561 * q + 6491) := by
      rw [h3n1, ν₂_mul (2 ^ 3) (6561 * q + 6491) (by positivity) hne, ν₂_pow_two' 3]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6491) (2 ^ ν₂ (6561 * q + 6491)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m8192_8169 (q : ℕ) : step (8192 * q + 8169) = 6144 * q + 6127 := by
  unfold step
  have h3n1 : 3 * (8192 * q + 8169) + 1 = 2 ^ 2 * (6144 * q + 6127) := by ring
  have h_odd : (6144 * q + 6127) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (8192 * q + 8169) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6144 * q + 6127) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6144 * q + 6127) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6144 * q + 6127) (by positivity)]

theorem step2_m8192_8169 (q : ℕ) : step (step (8192 * q + 8169)) = 9216 * q + 9191 := by
  rw [step_m8192_8169 q]
  unfold step
  have h3n1 : 3 * (6144 * q + 6127) + 1 = 2 ^ 1 * (9216 * q + 9191) := by ring
  have h_odd : (9216 * q + 9191) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6144 * q + 6127) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (9216 * q + 9191) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (9216 * q + 9191) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 9191) (by positivity)]

theorem step3_m8192_8169 (q : ℕ) : step (step (step (8192 * q + 8169))) = 13824 * q + 13787 := by
  rw [step2_m8192_8169 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 9191) + 1 = 2 ^ 1 * (13824 * q + 13787) := by ring
  have h_odd : (13824 * q + 13787) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 9191) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (13824 * q + 13787) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (13824 * q + 13787) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (13824 * q + 13787) (by positivity)]

theorem step4_m8192_8169 (q : ℕ) : step (step (step (step (8192 * q + 8169)))) = 20736 * q + 20681 := by
  rw [step3_m8192_8169 q]
  unfold step
  have h3n1 : 3 * (13824 * q + 13787) + 1 = 2 ^ 1 * (20736 * q + 20681) := by ring
  have h_odd : (20736 * q + 20681) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (13824 * q + 13787) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (20736 * q + 20681) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (20736 * q + 20681) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (20736 * q + 20681) (by positivity)]

theorem step5_m8192_8169 (q : ℕ) : step (step (step (step (step (8192 * q + 8169))))) = 15552 * q + 15511 := by
  rw [step4_m8192_8169 q]
  unfold step
  have h3n1 : 3 * (20736 * q + 20681) + 1 = 2 ^ 2 * (15552 * q + 15511) := by ring
  have h_odd : (15552 * q + 15511) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (20736 * q + 20681) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (15552 * q + 15511) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (15552 * q + 15511) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (15552 * q + 15511) (by positivity)]

theorem step6_m8192_8169 (q : ℕ) : step (step (step (step (step (step (8192 * q + 8169)))))) = 23328 * q + 23267 := by
  rw [step5_m8192_8169 q]
  unfold step
  have h3n1 : 3 * (15552 * q + 15511) + 1 = 2 ^ 1 * (23328 * q + 23267) := by ring
  have h_odd : (23328 * q + 23267) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (15552 * q + 15511) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (23328 * q + 23267) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (23328 * q + 23267) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (23328 * q + 23267) (by positivity)]

theorem step7_m8192_8169 (q : ℕ) : step (step (step (step (step (step (step (8192 * q + 8169))))))) = 34992 * q + 34901 := by
  rw [step6_m8192_8169 q]
  unfold step
  have h3n1 : 3 * (23328 * q + 23267) + 1 = 2 ^ 1 * (34992 * q + 34901) := by ring
  have h_odd : (34992 * q + 34901) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (23328 * q + 23267) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (34992 * q + 34901) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (34992 * q + 34901) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (34992 * q + 34901) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 8169 (mod 8192) ⇒ step^8(n) < n. -/
theorem descent_m8192_8169 (q : ℕ) (hq : 8192 * q + 8169 > 1) :
    step (step (step (step (step (step (step (step (8192 * q + 8169)))))))) < 8192 * q + 8169 := by
  rw [step7_m8192_8169 q]
  have h_bound : step (34992 * q + 34901) ≤ 6561 * q + 6544 := by
    unfold step
    have h3n1 : 3 * (34992 * q + 34901) + 1 = 2 ^ 4 * (6561 * q + 6544) := by ring
    have hne : (6561 * q + 6544) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (34992 * q + 34901) + 1) = 4 + ν₂ (6561 * q + 6544) := by
      rw [h3n1, ν₂_mul (2 ^ 4) (6561 * q + 6544) (by positivity) hne, ν₂_pow_two' 4]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 6544) (2 ^ ν₂ (6561 * q + 6544)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


theorem step_m16384_8193 (q : ℕ) : step (16384 * q + 8193) = 12288 * q + 6145 := by
  unfold step
  have h3n1 : 3 * (16384 * q + 8193) + 1 = 2 ^ 2 * (12288 * q + 6145) := by ring
  have h_odd : (12288 * q + 6145) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (16384 * q + 8193) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (12288 * q + 6145) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (12288 * q + 6145) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (12288 * q + 6145) (by positivity)]

theorem step2_m16384_8193 (q : ℕ) : step (step (16384 * q + 8193)) = 9216 * q + 4609 := by
  rw [step_m16384_8193 q]
  unfold step
  have h3n1 : 3 * (12288 * q + 6145) + 1 = 2 ^ 2 * (9216 * q + 4609) := by ring
  have h_odd : (9216 * q + 4609) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (12288 * q + 6145) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (9216 * q + 4609) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (9216 * q + 4609) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (9216 * q + 4609) (by positivity)]

theorem step3_m16384_8193 (q : ℕ) : step (step (step (16384 * q + 8193))) = 6912 * q + 3457 := by
  rw [step2_m16384_8193 q]
  unfold step
  have h3n1 : 3 * (9216 * q + 4609) + 1 = 2 ^ 2 * (6912 * q + 3457) := by ring
  have h_odd : (6912 * q + 3457) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (9216 * q + 4609) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (6912 * q + 3457) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (6912 * q + 3457) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (6912 * q + 3457) (by positivity)]

theorem step4_m16384_8193 (q : ℕ) : step (step (step (step (16384 * q + 8193)))) = 5184 * q + 2593 := by
  rw [step3_m16384_8193 q]
  unfold step
  have h3n1 : 3 * (6912 * q + 3457) + 1 = 2 ^ 2 * (5184 * q + 2593) := by ring
  have h_odd : (5184 * q + 2593) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (6912 * q + 3457) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (5184 * q + 2593) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (5184 * q + 2593) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (5184 * q + 2593) (by positivity)]

theorem step5_m16384_8193 (q : ℕ) : step (step (step (step (step (16384 * q + 8193))))) = 3888 * q + 1945 := by
  rw [step4_m16384_8193 q]
  unfold step
  have h3n1 : 3 * (5184 * q + 2593) + 1 = 2 ^ 2 * (3888 * q + 1945) := by ring
  have h_odd : (3888 * q + 1945) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (5184 * q + 2593) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (3888 * q + 1945) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (3888 * q + 1945) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (3888 * q + 1945) (by positivity)]

theorem step6_m16384_8193 (q : ℕ) : step (step (step (step (step (step (16384 * q + 8193)))))) = 2916 * q + 1459 := by
  rw [step5_m16384_8193 q]
  unfold step
  have h3n1 : 3 * (3888 * q + 1945) + 1 = 2 ^ 2 * (2916 * q + 1459) := by ring
  have h_odd : (2916 * q + 1459) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (3888 * q + 1945) + 1) = 2 := by
    rw [h3n1, ν₂_mul (2 ^ 2) (2916 * q + 1459) (by positivity) (by omega),
        ν₂_pow_two' 2, ν₂_odd (2916 * q + 1459) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (2916 * q + 1459) (by positivity)]

theorem step7_m16384_8193 (q : ℕ) : step (step (step (step (step (step (step (16384 * q + 8193))))))) = 4374 * q + 2189 := by
  rw [step6_m16384_8193 q]
  unfold step
  have h3n1 : 3 * (2916 * q + 1459) + 1 = 2 ^ 1 * (4374 * q + 2189) := by ring
  have h_odd : (4374 * q + 2189) % 2 = 1 := by omega
  have hν₂ : ν₂ (3 * (2916 * q + 1459) + 1) = 1 := by
    rw [h3n1, ν₂_mul (2 ^ 1) (4374 * q + 2189) (by positivity) (by omega),
        ν₂_pow_two' 1, ν₂_odd (4374 * q + 2189) (by omega)]
  rw [hν₂, h3n1, Nat.mul_div_cancel_left (4374 * q + 2189) (by positivity)]

/-- Discovered by microscope, verified to 10^7, auto-formalized: n ≡ 8193 (mod 16384) ⇒ step^8(n) < n. -/
theorem descent_m16384_8193 (q : ℕ) (hq : 16384 * q + 8193 > 1) :
    step (step (step (step (step (step (step (step (16384 * q + 8193)))))))) < 16384 * q + 8193 := by
  rw [step7_m16384_8193 q]
  have h_bound : step (4374 * q + 2189) ≤ 6561 * q + 3284 := by
    unfold step
    have h3n1 : 3 * (4374 * q + 2189) + 1 = 2 ^ 1 * (6561 * q + 3284) := by ring
    have hne : (6561 * q + 3284) ≠ 0 := by omega
    have hν_split : ν₂ (3 * (4374 * q + 2189) + 1) = 1 + ν₂ (6561 * q + 3284) := by
      rw [h3n1, ν₂_mul (2 ^ 1) (6561 * q + 3284) (by positivity) hne, ν₂_pow_two' 1]
    rw [hν_split, h3n1, pow_add,
        Nat.mul_div_mul_left (6561 * q + 3284) (2 ^ ν₂ (6561 * q + 3284)) (by positivity)]
    exact Nat.div_le_self _ _
  omega


end CollatzProof
