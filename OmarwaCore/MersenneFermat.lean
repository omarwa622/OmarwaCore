/-
  Mersenne/Fermat Period Laws for OMARWA Sequence (Step-1 Formalization)
  ======================================================================
  Ar-Ge Alanı: Temel Bilimler / Sayı Teorisi
  TRL Seviyesi: 4
  Protokol ID: OTT-LEAN-002

  Bu dosya T8/T9 için "NOT_STARTED" → "IN_PROGRESS" geçişinin
  Lean tarafındaki ilk formal adımıdır.

  Kapsam (Step-1):
    - Mersenne özel durumları için periodiklik:
        m=7  (n=3), m=31 (n=5), m=127 (n=7)
    - Fermat özel durumu için periodiklik:
        m=17 (n=4, 2n=8)

  Not:
    Bu sürümde özel durumlar için exact period (minimalite)
    ispatları da eklendi (m=7,31,127,17).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import OmarwaCore.Sequence

namespace Omarwa.MersenneFermat

open Omarwa

/-- Mod m altında periodiklik tanımı. -/
def PeriodMod (m p : ℕ) : Prop :=
  ∀ k : ℕ, T (k + p) % m = T k % m

/-- Exact periyot: p periodiktir ve 1..(p-1) arası period olamaz. -/
def ExactPeriodMod (m p : ℕ) : Prop :=
  PeriodMod m p ∧ ∀ d : ℕ, 0 < d → d < p → ¬ PeriodMod m d

/-! ## Modular Period Lemmas — needed before T8 proof -/

lemma mul6_pow2_mod7_period3 (k : ℕ) :
    (6 * 2 ^ (k + 3)) % 7 = (6 * 2 ^ k) % 7 := by
  have h : 6 * 2 ^ (k + 3) = 6 * 2 ^ k + 7 * (6 * 2 ^ k) := by ring
  rw [h]; simp [Nat.add_mul_mod_self_left]

/-- Mersenne özel durumu: m=7 (2^3-1) için period 3. -/
theorem period_mod_7_3 : PeriodMod 7 3 := by
  intro k
  unfold T
  have h := mul6_pow2_mod7_period3 k
  omega

/-! ## T8 Genel-n Kanıtı

`PeriodMod 7 3` özel durumundan hareketle `7 ∣ T k ↔ k % 3 = 0` eşdeğerliğini
genel n için türetiyoruz. Bu, T8'in "bölünebilirlik ↔ indeks mod 3" formunu
Lean tarafında kapatır (Gate-A, TRL 4 → 5 geçişi). -/

lemma period_mod_7_rewrite (n q : ℕ) : T (n + 3 * q) % 7 = T n % 7 := by
  have hper := period_mod_7_3
  induction q with
  | zero => simpa using (rfl : n + 0 = n)
  | succ q ih =>
      have : n + 3 * (Nat.succ q) = (n + 3 * q) + 3 := by omega
      calc
        T (n + 3 * (Nat.succ q)) % 7
            = T ((n + 3 * q) + 3) % 7 := by simpa [this]
        _ = T (n + 3 * q) % 7 := hper (n + 3 * q)
        _ = T n % 7 := ih

theorem T8_divisible_by_seven (k : ℕ) : 7 ∣ T k ↔ k % 3 = 0 := by
  let r := k % 3
  let q := k / 3
  have hk : k = r + 3 * q := by omega
  have hreduce : T k % 7 = T r % 7 := by
    nth_rewrite 1 [hk]
    exact period_mod_7_rewrite r q
  have hrange : r < 3 := by
    dsimp [r]
    exact Nat.mod_lt _ (by decide)
  constructor
  · intro hdiv
    have hmodk : T k % 7 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hmodr : T r % 7 = 0 := by rw [← hreduce]; exact hmodk
    interval_cases r <;> simp_all [T]
  · intro hkmod
    have hr0 : r = 0 := by omega
    rw [hr0] at hreduce
    have hbase : T 0 % 7 = 0 := by native_decide
    exact Nat.dvd_of_mod_eq_zero (by omega)

/-! ## Other Mersenne/Fermat Period Lemmas -/

lemma mul6_pow2_mod31_period5 (k : ℕ) :
    (6 * 2 ^ (k + 5)) % 31 = (6 * 2 ^ k) % 31 := by
  have h : 6 * 2 ^ (k + 5) = 6 * 2 ^ k + 31 * (6 * 2 ^ k) := by ring
  rw [h]; simp [Nat.add_mul_mod_self_left]

lemma mul6_pow2_mod127_period7 (k : ℕ) :
    (6 * 2 ^ (k + 7)) % 127 = (6 * 2 ^ k) % 127 := by
  have h : 6 * 2 ^ (k + 7) = 6 * 2 ^ k + 127 * (6 * 2 ^ k) := by ring
  rw [h]; simp [Nat.add_mul_mod_self_left]

lemma mul6_pow2_mod17_period8 (k : ℕ) :
    (6 * 2 ^ (k + 8)) % 17 = (6 * 2 ^ k) % 17 := by
  have h : 6 * 2 ^ (k + 8) = 6 * 2 ^ k + 17 * (90 * 2 ^ k) := by ring
  rw [h]; simp [Nat.add_mul_mod_self_left]

/-- Mersenne özel durumu: m=31 (2^5-1) için period 5. -/
theorem period_mod_31_5 : PeriodMod 31 5 := by
  intro k
  unfold T
  have h := mul6_pow2_mod31_period5 k
  omega

/-- Mersenne özel durumu: m=127 (2^7-1) için period 7. -/
theorem period_mod_127_7 : PeriodMod 127 7 := by
  intro k
  unfold T
  have h := mul6_pow2_mod127_period7 k
  omega

/-- Fermat özel durumu: m=17 (2^4+1) için period 8 (=2n). -/
theorem period_mod_17_8 : PeriodMod 17 8 := by
  intro k
  unfold T
  have h := mul6_pow2_mod17_period8 k
  omega

/-- Minimalite ispatı için örnek karşılaştırma (T(1) ve T(0) farklı). -/
theorem mod31_k1_ne_k0 : T 1 % 31 ≠ T 0 % 31 := by
  native_decide

theorem mod17_k1_ne_k0 : T 1 % 17 ≠ T 0 % 17 := by
  native_decide

theorem not_period_mod7_1 : ¬ PeriodMod 7 1 := by
  intro h
  have h0 := h 0
  have hneq : T 1 % 7 ≠ T 0 % 7 := by native_decide
  exact hneq h0

theorem not_period_mod7_2 : ¬ PeriodMod 7 2 := by
  intro h
  have h0 := h 0
  have hneq : T 2 % 7 ≠ T 0 % 7 := by native_decide
  exact hneq h0

theorem exact_period_mod_7_3 : ExactPeriodMod 7 3 := by
  refine ⟨period_mod_7_3, ?_⟩
  intro d hd0 hdl
  interval_cases d
  · exact not_period_mod7_1
  · exact not_period_mod7_2

theorem not_period_mod31_1 : ¬ PeriodMod 31 1 := by
  intro h
  have h0 := h 0
  have hneq : T 1 % 31 ≠ T 0 % 31 := by native_decide
  exact hneq h0

theorem not_period_mod31_2 : ¬ PeriodMod 31 2 := by
  intro h
  have h0 := h 0
  have hneq : T 2 % 31 ≠ T 0 % 31 := by native_decide
  exact hneq h0

theorem not_period_mod31_3 : ¬ PeriodMod 31 3 := by
  intro h
  have h0 := h 0
  have hneq : T 3 % 31 ≠ T 0 % 31 := by native_decide
  exact hneq h0

theorem not_period_mod31_4 : ¬ PeriodMod 31 4 := by
  intro h
  have h0 := h 0
  have hneq : T 4 % 31 ≠ T 0 % 31 := by native_decide
  exact hneq h0

theorem exact_period_mod_31_5 : ExactPeriodMod 31 5 := by
  refine ⟨period_mod_31_5, ?_⟩
  intro d hd0 hdl
  interval_cases d <;> simp at hd0
  · exact not_period_mod31_1
  · exact not_period_mod31_2
  · exact not_period_mod31_3
  · exact not_period_mod31_4

theorem not_period_mod127_1 : ¬ PeriodMod 127 1 := by
  intro h
  have h0 := h 0
  have hneq : T 1 % 127 ≠ T 0 % 127 := by native_decide
  exact hneq h0

theorem not_period_mod127_2 : ¬ PeriodMod 127 2 := by
  intro h
  have h0 := h 0
  have hneq : T 2 % 127 ≠ T 0 % 127 := by native_decide
  exact hneq h0

theorem not_period_mod127_3 : ¬ PeriodMod 127 3 := by
  intro h
  have h0 := h 0
  have hneq : T 3 % 127 ≠ T 0 % 127 := by native_decide
  exact hneq h0

theorem not_period_mod127_4 : ¬ PeriodMod 127 4 := by
  intro h
  have h0 := h 0
  have hneq : T 4 % 127 ≠ T 0 % 127 := by native_decide
  exact hneq h0

theorem not_period_mod127_5 : ¬ PeriodMod 127 5 := by
  intro h
  have h0 := h 0
  have hneq : T 5 % 127 ≠ T 0 % 127 := by native_decide
  exact hneq h0

theorem not_period_mod127_6 : ¬ PeriodMod 127 6 := by
  intro h
  have h0 := h 0
  have hneq : T 6 % 127 ≠ T 0 % 127 := by native_decide
  exact hneq h0

theorem exact_period_mod_127_7 : ExactPeriodMod 127 7 := by
  refine ⟨period_mod_127_7, ?_⟩
  intro d hd0 hdl
  interval_cases d <;> simp at hd0
  · exact not_period_mod127_1
  · exact not_period_mod127_2
  · exact not_period_mod127_3
  · exact not_period_mod127_4
  · exact not_period_mod127_5
  · exact not_period_mod127_6

theorem not_period_mod17_1 : ¬ PeriodMod 17 1 := by
  intro h
  have h0 := h 0
  have hneq : T 1 % 17 ≠ T 0 % 17 := by native_decide
  exact hneq h0

theorem not_period_mod17_2 : ¬ PeriodMod 17 2 := by
  intro h
  have h0 := h 0
  have hneq : T 2 % 17 ≠ T 0 % 17 := by native_decide
  exact hneq h0

theorem not_period_mod17_3 : ¬ PeriodMod 17 3 := by
  intro h
  have h0 := h 0
  have hneq : T 3 % 17 ≠ T 0 % 17 := by native_decide
  exact hneq h0

theorem not_period_mod17_4 : ¬ PeriodMod 17 4 := by
  intro h
  have h0 := h 0
  have hneq : T 4 % 17 ≠ T 0 % 17 := by native_decide
  exact hneq h0

theorem not_period_mod17_5 : ¬ PeriodMod 17 5 := by
  intro h
  have h0 := h 0
  have hneq : T 5 % 17 ≠ T 0 % 17 := by native_decide
  exact hneq h0

theorem not_period_mod17_6 : ¬ PeriodMod 17 6 := by
  intro h
  have h0 := h 0
  have hneq : T 6 % 17 ≠ T 0 % 17 := by native_decide
  exact hneq h0

theorem not_period_mod17_7 : ¬ PeriodMod 17 7 := by
  intro h
  have h0 := h 0
  have hneq : T 7 % 17 ≠ T 0 % 17 := by native_decide
  exact hneq h0

theorem exact_period_mod_17_8 : ExactPeriodMod 17 8 := by
  refine ⟨period_mod_17_8, ?_⟩
  intro d hd0 hdl
  interval_cases d <;> simp at hd0
  · exact not_period_mod17_1
  · exact not_period_mod17_2
  · exact not_period_mod17_3
  · exact not_period_mod17_4
  · exact not_period_mod17_5
  · exact not_period_mod17_6
  · exact not_period_mod17_7

/-- Yardımcı: j ≤ i varsayımı altında `gcd(T i, T j)` değeri `2^(i-j) - 1`'i
    böler. Bu, T9 (GCD Law) genel-n kanıtının çekirdeğidir. -/
lemma gcd_dvd_pow_sub_one_of_ge {i j : ℕ} (h : j ≤ i) :
    Nat.gcd (T i) (T j) ∣ 2 ^ (i - j) - 1 := by
  set g := Nat.gcd (T i) (T j)
  have hgi : g ∣ T i := Nat.gcd_dvd_left _ _
  have hgj : g ∣ T j := Nat.gcd_dvd_right _ _
  have hsub : g ∣ 2 ^ (i - j) * T j - T i :=
    Nat.dvd_sub (dvd_mul_of_dvd_right hgj _) hgi
  have hdiff : 2 ^ (i - j) * T j - T i = 2 ^ (i - j) - 1 := by
    unfold T
    -- (6·2^i + 2^(i-j)) - (6·2^i + 1) = 2^(i-j) - 1
    have : 2 ^ (i - j) * (6 * 2 ^ j + 1) = 6 * 2 ^ i + 2 ^ (i - j) := by
      have hexp : 2 ^ (i - j) * 2 ^ j = 2 ^ i := by
        rw [← pow_add, Nat.sub_add_cancel h]
      have h1 : 2 ^ (i - j) * (6 * 2 ^ j + 1) = 6 * (2 ^ (i - j) * 2 ^ j) + 2 ^ (i - j) := by ring
      rw [hexp] at h1
      exact h1
    have hsub' : (6 * 2 ^ i + 2 ^ (i - j)) - (6 * 2 ^ i + 1) = 2 ^ (i - j) - 1 :=
      by simpa using (Nat.add_sub_add_left (6 * 2 ^ i) (2 ^ (i - j)) 1)
    simpa [this] using hsub'
  simpa [hdiff] using hsub

/-- T9 (GCD Law) — Genel-n Lean kanıtı: tüm i,j için `gcd(T i, T j)` değeri
    `2^{|i-j|} - 1`'i böler. -/
theorem T9_gcd_dvd_pow_sub_one (i j : ℕ) :
    Nat.gcd (T i) (T j) ∣ 2 ^ (Nat.dist i j) - 1 := by
  by_cases h : j ≤ i
  · have h' := gcd_dvd_pow_sub_one_of_ge (i := i) (j := j) h
    have hdist : Nat.dist i j = i - j := by
      simp [Nat.dist, Nat.sub_eq_zero_of_le h]
    rw [hdist]
    exact h'
  · have h' : i ≤ j := Nat.le_of_not_ge h
    have h'' := gcd_dvd_pow_sub_one_of_ge (i := j) (j := i) h'
    have hdist : Nat.dist i j = j - i := by
      simp [Nat.dist, Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)]
    rw [hdist, Nat.gcd_comm]
    exact h''

end Omarwa.MersenneFermat
