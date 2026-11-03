import SetCover.Certificate

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section

def beta (k : ℕ) : ℝ := 4 / k
def q (k : ℕ) : ℝ := 1 - beta k

/-- The manuscript's displayed definition of `h`, with real division and the literal
binomial coefficients. -/
def bias (k c : ℕ) : ℝ :=
  if c ≤ 4 then (-1 : ℝ) ^ c * Nat.choose 4 c /
    ((Nat.choose k c : ℝ) * (beta k / q k) ^ c)
  else 0

@[simp] theorem bias_zero (k : ℕ) : bias k 0 = 1 := by
  simp [bias]

theorem beta_pos {k : ℕ} (hk : 8 ≤ k) : 0 < beta k := by
  unfold beta
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  positivity

theorem q_pos {k : ℕ} (hk : 8 ≤ k) : 0 < q k := by
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk
  unfold q beta
  have hk0 : (0 : ℝ) < k := by linarith
  have : (4 : ℝ) / k < 1 := (div_lt_one hk0).2 (by linarith)
  linarith

theorem beta_div_q {k : ℕ} (hk : 8 ≤ k) :
    beta k / q k = 4 / ((k : ℝ) - 4) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  have hk4 : (k : ℝ) - 4 ≠ 0 := by
    have : (8 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  simp only [q, beta]
  field_simp

theorem weighted_choose_ge {k c : ℕ} (hk : 8 ≤ k) (hc : c ≤ 4) :
    (Nat.choose 4 c : ℝ) ≤ (Nat.choose k c : ℝ) * (beta k / q k) ^ c := by
  have hk4 : 4 ≤ k := by omega
  have hdesc : (k - 4) ^ c ≤ k.descFactorial c := by
    rw [Nat.descFactorial_eq_prod_range]
    calc
      (k - 4) ^ c = ∏ _i ∈ range c, (k - 4) := by simp
      _ ≤ ∏ i ∈ range c, (k - i) := by
        apply Finset.prod_le_prod'
        intro i hi
        have : i < c := Finset.mem_range.mp hi
        omega
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hdescR : ((k : ℝ) - 4) ^ c ≤ (c.factorial : ℝ) * Nat.choose k c := by
    exact_mod_cast hdesc
  have hsmall : (c.factorial : ℝ) * Nat.choose 4 c ≤ (4 : ℝ) ^ c := by
    interval_cases c <;> norm_num [Nat.choose]
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (k : ℝ) - 4 := by linarith
  rw [beta_div_q hk]
  have hm := mul_le_mul_of_nonneg_right hdescR
    (pow_nonneg (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 4) hpos)) c)
  have he : ((k : ℝ) - 4) ^ c * (4 / ((k : ℝ) - 4)) ^ c = (4 : ℝ) ^ c := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [he] at hm
  have hfact : (0 : ℝ) < c.factorial := by exact_mod_cast Nat.factorial_pos c
  apply (mul_le_mul_left hfact).mp
  calc
    (c.factorial : ℝ) * Nat.choose 4 c ≤ (4 : ℝ) ^ c := hsmall
    _ ≤ (c.factorial : ℝ) * Nat.choose k c * (4 / ((k : ℝ) - 4)) ^ c := hm
    _ = (c.factorial : ℝ) *
      ((Nat.choose k c : ℝ) * (4 / ((k : ℝ) - 4)) ^ c) := by ring

theorem abs_bias_le_one {k : ℕ} (hk : 8 ≤ k) (c : ℕ) : |bias k c| ≤ 1 := by
  by_cases hc : c ≤ 4
  · have hnum : (0 : ℝ) < Nat.choose 4 c := by exact_mod_cast Nat.choose_pos hc
    have hden := weighted_choose_ge hk hc
    have hden0 : 0 < (Nat.choose k c : ℝ) * (beta k / q k) ^ c := lt_of_lt_of_le hnum hden
    simp only [bias, if_pos hc, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, Nat.abs_cast, abs_of_pos hden0]
    exact (div_le_one hden0).2 hden
  · simp [bias, hc]

def binomialMass (k c : ℕ) : ℝ :=
  (Nat.choose k c : ℝ) * beta k ^ c * q k ^ (k - c)

theorem binomial_bias_cancel {k c : ℕ} (hk : 8 ≤ k) (hc : c ≤ 4) :
    binomialMass k c * bias k c = q k ^ k * ((-1 : ℝ) ^ c * Nat.choose 4 c) := by
  have hck : c ≤ k := by omega
  have hchoose : (Nat.choose k c : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.choose_pos hck)
  have hb : beta k ≠ 0 := ne_of_gt (beta_pos hk)
  have hq : q k ≠ 0 := ne_of_gt (q_pos hk)
  have hpow : q k ^ (k - c) * q k ^ c = q k ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hck]
  simp only [binomialMass, bias, if_pos hc, div_pow]
  field_simp
  rw [← hpow]
  ring

theorem fourth_difference (a₀ a₁ a₂ a₃ : ℝ) :
    ∑ c ∈ range 5, (-1 : ℝ) ^ c * Nat.choose 4 c *
      (a₀ + a₁ * c + a₂ * (c : ℝ)^2 + a₃ * (c : ℝ)^3) = 0 := by
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

theorem binomial_cubic_cancellation {k : ℕ} (hk : 8 ≤ k)
    (a₀ a₁ a₂ a₃ : ℝ) :
    ∑ c ∈ range (k + 1), binomialMass k c * bias k c *
      (a₀ + a₁ * c + a₂ * (c : ℝ)^2 + a₃ * (c : ℝ)^3) = 0 := by
  have hsub : range 5 ⊆ range (k + 1) := Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · calc
      ∑ c ∈ range 5, binomialMass k c * bias k c *
          (a₀ + a₁ * c + a₂ * (c : ℝ)^2 + a₃ * (c : ℝ)^3)
          = q k ^ k * ∑ c ∈ range 5, (-1 : ℝ)^c * Nat.choose 4 c *
            (a₀ + a₁ * c + a₂ * (c : ℝ)^2 + a₃ * (c : ℝ)^3) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c hc
              rw [binomial_bias_cancel hk (by have := Finset.mem_range.mp hc; omega)]
              ring
      _ = 0 := by rw [fourth_difference, mul_zero]
  · intro c _ hc
    have : ¬ c ≤ 4 := by simpa [Finset.mem_range] using hc
    simp [bias, this]

abbrev CheapMatrix (v M : ℕ) := Fin v → Fin M → Bool
abbrev RepairChoices (M k : ℕ) := {K : Finset (Fin M) // K.card = k}

def count {v M : ℕ} (A : CheapMatrix v M) (K : Finset (Fin M)) (e : Fin v) : ℕ :=
  (K.filter fun j => A e j = true).card

def maskBitMass (k c : ℕ) (b : Bool) : ℝ :=
  if b then (1 - bias k c) / 2 else (1 + bias k c) / 2

def componentMass {v M k : ℕ} (A : CheapMatrix v M) (K : RepairChoices M k)
    (z : Cube v) : ℝ :=
  ∏ e, maskBitMass k (count A K.val e) (z e)

def noiseMass {v M : ℕ} (k : ℕ) (A : CheapMatrix v M) (z : Cube v) : ℝ :=
  average (fun K : RepairChoices M k => componentMass A K z)

def Repairable {v M : ℕ} (k : ℕ) (A : CheapMatrix v M) (z : Cube v) : Prop :=
  ∃ K : Finset (Fin M), K.card ≤ k ∧
    ∀ e, z e = true → ∃ j ∈ K, A e j = true

theorem repairChoices_nonempty {M k : ℕ} (hkM : k ≤ M) :
    Nonempty (RepairChoices M k) := by
  obtain ⟨K, _, hK⟩ := Finset.exists_subset_card_eq
    (show k ≤ (univ : Finset (Fin M)).card by simpa using hkM)
  exact ⟨⟨K, hK⟩⟩

theorem maskBitMass_nonneg {k : ℕ} (hk : 8 ≤ k) (c : ℕ) (b : Bool) :
    0 ≤ maskBitMass k c b := by
  have h := abs_le.mp (abs_bias_le_one hk c)
  cases b <;> dsimp [maskBitMass] <;> linarith

@[simp] theorem maskBitMass_sum (k c : ℕ) :
    ∑ b : Bool, maskBitMass k c b = 1 := by
  simp [Fintype.sum_bool, maskBitMass]
  ring

theorem componentMass_probability {v M k : ℕ} (hk : 8 ≤ k)
    (A : CheapMatrix v M) (K : RepairChoices M k) :
    IsProbability (componentMass A K) := by
  constructor
  · intro z
    exact Finset.prod_nonneg fun e _ => maskBitMass_nonneg hk _ _
  · simp only [componentMass, ← Fintype.prod_sum, maskBitMass_sum, Finset.prod_const_one]

theorem noiseMass_probability {v M k : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M)
    (A : CheapMatrix v M) : IsProbability (noiseMass k A) := by
  letI := repairChoices_nonempty hkM
  constructor
  · intro z
    exact average_nonneg fun K => (componentMass_probability hk A K).1 z
  · unfold noiseMass
    rw [← average_sum]
    simp_rw [(componentMass_probability hk A _).2]
    exact average_const 1

theorem noiseMass_repairable {v M k : ℕ} (hkM : k ≤ M)
    (A : CheapMatrix v M) (z : Cube v) (hz : 0 < noiseMass k A z) :
    Repairable k A z := by
  classical
  letI := repairChoices_nonempty hkM
  obtain ⟨K, hK⟩ : ∃ K : RepairChoices M k, 0 < componentMass A K z := by
    by_contra hn
    push_neg at hn
    have hm := average_mono hn
    simp only [average_const] at hm
    exact (not_lt_of_ge hm) hz
  refine ⟨K.val, le_of_eq K.property, ?_⟩
  intro e he
  by_contra hn
  have hcount : count A K.val e = 0 := by
    unfold count
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simpa using hn
  have hzero : maskBitMass k (count A K.val e) (z e) = 0 := by
    simp [hcount, he, maskBitMass]
  have hproduct : componentMass A K z = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ e) hzero
  linarith

end
end SetCover
