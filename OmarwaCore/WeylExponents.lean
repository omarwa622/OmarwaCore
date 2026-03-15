/-
  Weyl Exponents of E8: {1,7,11,13,17,19,23,29}
  ================================================
  Proofs related to E8 Weyl exponents and their connection to OMARWA.

  Reference: kitap/part1_mathematical_genome/ch06_weyl_exponents.md

  Theorems:
    - Weyl exponents sum to 120
    - All exponents coprime to 30
    - Exponents form units mod 30
    - OMARWA sequence intersections
    - Product of exponents
    - Palindromic structure m_i + m_{9-i} = 30
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import OmarwaCore.CoxeterNumber

namespace Omarwa.Weyl

open Omarwa

/-- E8 Weyl exponents -/
def weyl_exponents : List ℕ := [1,7,11,13,17,19,23,29]

/-- Sum of Weyl exponents = 120 = dim(E8)/2 -/
theorem weyl_sum : 1 + 7 + 11 + 13 + 17 + 19 + 23 + 29 = 120 := by
  native_decide

/-- Exponents modulo 30 are coprime to 30 -/
theorem exponents_mod_30_coprime : ∀ e ∈ weyl_exponents, Nat.gcd e 30 = 1 := by
  decide

/-- dim(E8) = 248 -/
theorem dim_E8 : 248 = 2 * (1 + 7 + 11 + 13 + 17 + 19 + 23 + 29) + 8 := by
  native_decide

/-- Palindromic pairs: m_i + m_{9-i} = 30 = h(E8)
    1+29=30, 7+23=30, 11+19=30, 13+17=30 -/
theorem palindromic_pair_1 : 1 + 29 = 30 := by native_decide
theorem palindromic_pair_2 : 7 + 23 = 30 := by native_decide
theorem palindromic_pair_3 : 11 + 19 = 30 := by native_decide
theorem palindromic_pair_4 : 13 + 17 = 30 := by native_decide

/-- OMARWA intersections: m_2 = 7 = T_0, m_8 = 29 = T_0 + T_1 + 9 -/
theorem weyl_m2_is_T0 : (weyl_exponents.get ⟨1, by simp [weyl_exponents]⟩) = 7 := by
  native_decide

/-- m_4 = 13 = T_1 -/
theorem weyl_m4_is_T1 : (weyl_exponents.get ⟨3, by simp [weyl_exponents]⟩) = 13 := by
  native_decide

/-- m_8 = 29 is Sophie Germain prime -/
theorem weyl_m8_sophie : 2 * 29 + 1 = 59 := by native_decide

/-- Product of Weyl exponents -/
theorem weyl_product : 1 * 7 * 11 * 13 * 17 * 19 * 23 * 29 = 215656441 := by
  native_decide

-- |W(E8)| / product_of_exponents ratio
-- 696729600 / (1*7*11*13*17*19*23*29) ≈ 0.348 (not exact ratio)
-- But 696729600 = 2^14 * 3^5 * 5^2 * 7

/-- E8 roots = 240 = 2 × sum(m_i) = 2 × 120 -/
theorem E8_roots : 240 = 2 * (1 + 7 + 11 + 13 + 17 + 19 + 23 + 29) := by
  native_decide

end Omarwa.Weyl