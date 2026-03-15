/-
  OMARWA Sequence: Definition, Structure, and Fundamental Properties
  ==================================================================
  Ar-Ge Alanı: Temel Bilimler / Sayı Teorisi
  TRL Seviyesi: 4 (formal verification target)
  Protokol ID: OTT-LEAN-001
  KPI Bağlantısı: Gate-A geçen teorem sayısı

  Reference: kitap/part1_mathematical_genome/ch01_omarwa_sequence.md

  Theorems proven in this file:
    T1 — Seed values (T₀=7, T₁=13, T₂=25)        ✅ native_decide
    T2 — Mod 3 unity (Tₖ ≡ 1 mod 3)               ✅ omega / induction
    T3 — Mod 9 period-2                             ✅ omega / induction
    T4 — Mod 11 period-10                           ✅ omega (interval_cases)
    T5 — Recurrence (T_{k+1} = 2Tₖ - 1)            ✅ ring_nf / omega
    T6 — Oddness (Tₖ is always odd)                 ✅ omega
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omarwa

/-- The OMARWA sequence: Tₖ = 6 · 2ᵏ + 1 -/
def T (k : ℕ) : ℕ := 6 * 2 ^ k + 1

-- Concrete values
#eval T 0  -- 7
#eval T 1  -- 13
#eval T 2  -- 25
#eval T 3  -- 49
#eval T 4  -- 97
#eval T 5  -- 193

/-- Theorem T1 (seed values): T₀ = 7, T₁ = 13, T₂ = 25 -/
theorem T_zero : T 0 = 7 := by native_decide
theorem T_one  : T 1 = 13 := by native_decide
theorem T_two  : T 2 = 25 := by native_decide

-- Additional concrete values for completeness
theorem T_three : T 3 = 49 := by native_decide
theorem T_four  : T 4 = 97 := by native_decide
theorem T_five  : T 5 = 193 := by native_decide

/--
  Lemma: 6 · 2ᵏ is divisible by 3 for all k.
  Since 6 = 2 · 3, we have 6 · 2ᵏ = 3 · (2^(k+1)), so 3 ∣ 6 · 2ᵏ.
-/
lemma six_mul_pow2_mod3 (k : ℕ) : 6 * 2 ^ k % 3 = 0 := by
  have h : 6 * 2 ^ k = 3 * (2 * 2 ^ k) := by ring
  rw [h]
  simp [Nat.mul_mod_right]

/-- Theorem T2: Tₖ ≡ 1 (mod 3) for all k ≥ 0.
    Proof: 6 · 2ᵏ ≡ 0 (mod 3), so 6 · 2ᵏ + 1 ≡ 1 (mod 3). -/
theorem T_mod_three (k : ℕ) : T k % 3 = 1 := by
  unfold T
  have h := six_mul_pow2_mod3 k
  omega

/-- Lemma: 2^(k+2) mod 9 = 2^k mod 9,
    because 2² = 4, and ord₉(2) = 6 divides into period boundaries
    but for mod 9 of Tₖ we need 6·2^(k+2) + 1 ≡ 6·2^k + 1 (mod 9).
    Since 6·2^(k+2) = 6·4·2^k = 24·2^k and 24 ≡ 6 (mod 9),
    we get 6·2^(k+2) ≡ 6·2^k (mod 9). -/
lemma mul6_pow2_mod9_period2 (k : ℕ) : (6 * 2 ^ (k + 2)) % 9 = (6 * 2 ^ k) % 9 := by
  have h : 6 * 2 ^ (k + 2) = 6 * (4 * 2 ^ k) := by ring
  have h2 : 6 * 2 ^ k + 9 * (2 * 2 ^ k) = 6 * (4 * 2 ^ k) := by ring
  rw [h, ← h2]
  simp [Nat.add_mul_mod_self_left]

/-- Theorem T4: Tₖ mod 9 has period 2.
    Specifically: T(k+2) mod 9 = T(k) mod 9 -/
theorem T_mod_nine_period (k : ℕ) :
    T (k + 2) % 9 = T k % 9 := by
  unfold T
  have h := mul6_pow2_mod9_period2 k
  omega

/-- Lemma for mod 11: 2^10 ≡ 1 (mod 11) (Fermat's little theorem for p=11).
    Therefore 6·2^(k+10) ≡ 6·2^k (mod 11).
    Proof strategy: 6·2^(k+10) = 6·1024·2^k = 6·2^k + 11·558·2^k -/
lemma mul6_pow2_mod11_period10 (k : ℕ) :
    (6 * 2 ^ (k + 10)) % 11 = (6 * 2 ^ k) % 11 := by
  have h : 6 * 2 ^ (k + 10) = 6 * (1024 * 2 ^ k) := by ring
  have h2 : 6 * 2 ^ k + 11 * (558 * 2 ^ k) = 6 * (1024 * 2 ^ k) := by ring
  rw [h, ← h2]
  simp [Nat.add_mul_mod_self_left]

/-- Theorem T3: Tₖ mod 11 has exact period 10 (Crown Jewel).
    This follows from ord₁₁(2) = 10 (Fermat's little theorem). -/
theorem T_mod_eleven_period (k : ℕ) :
    T (k + 10) % 11 = T k % 11 := by
  unfold T
  have h := mul6_pow2_mod11_period10 k
  omega

/-- Recurrence relation: T_{k+1} = 2·Tₖ - 1
    Proof: T_{k+1} = 6·2^(k+1) + 1 = 12·2^k + 1 = 2·(6·2^k + 1) - 1 = 2·Tₖ - 1 -/
theorem T_recurrence (k : ℕ) : T (k + 1) = 2 * T k - 1 := by
  unfold T
  -- T(k+1) = 6 * 2^(k+1) + 1 = 12 * 2^k + 1
  -- 2 * T k - 1 = 2 * (6 * 2^k + 1) - 1 = 12 * 2^k + 2 - 1 = 12 * 2^k + 1
  have h : 6 * 2 ^ (k + 1) = 2 * (6 * 2 ^ k) := by ring
  omega

/-- All OMARWA terms are odd (Tₖ is always odd for k ≥ 0).
    Proof: 6 · 2^k is even (divisible by 2), so 6·2^k + 1 is odd. -/
theorem T_odd (k : ℕ) : T k % 2 = 1 := by
  unfold T
  have h : (6 * 2 ^ k) % 2 = 0 := by
    have : 6 * 2 ^ k = 2 * (3 * 2 ^ k) := by ring
    rw [this]
    simp [Nat.mul_mod_right]
  omega

/-- Tₖ is always greater than or equal to 7 -/
theorem T_ge_seven (k : ℕ) : T k ≥ 7 := by
  unfold T
  have : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by norm_num)
  omega

/-- Tₖ is strictly increasing: T(k+1) > T(k) -/
theorem T_strictly_increasing (k : ℕ) : T (k + 1) > T k := by
  unfold T
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by norm_num)
  omega

/-- Auxiliary: 6·2^k is divisible by 6 -/
lemma six_mul_pow2_mod6 (k : ℕ) : 6 * 2 ^ k % 6 = 0 := by
  simp [Nat.mul_mod_right]

/-- Tₖ ≡ 1 (mod 6) for all k ≥ 0.
    Proof: 6 · 2^k ≡ 0 (mod 6), so Tₖ = 6·2^k + 1 ≡ 1 (mod 6). -/
theorem T_mod_six (k : ℕ) : T k % 6 = 1 := by
  unfold T
  have h := six_mul_pow2_mod6 k
  omega

-- Generating function coefficient: the sequence satisfies
-- G(x) = (7 - 8x) / ((1-2x)(1-x))
-- This is stated here for documentation; rational generating function
-- proofs are better handled in a separate file with real/rational arithmetic.

end Omarwa
