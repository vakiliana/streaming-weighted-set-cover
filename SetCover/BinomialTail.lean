import SetCover.BlockIndependence
import SetCover.AsymptoticBudget

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem binomialExpectation_nonneg {k n : ℕ} (hk : 8 ≤ k) {f : ℕ → ℝ}
    (hf : ∀ c, 0 ≤ f c) : 0 ≤ binomialExpectation k n f := by
  apply Finset.sum_nonneg
  intro c _
  have hb := le_of_lt (beta_pos hk)
  have hq := le_of_lt (q_pos hk)
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg hb _)) (pow_nonneg hq _)) (hf c)

theorem binomialExpectation_mono {k n : ℕ} (hk : 8 ≤ k) {f g : ℕ → ℝ}
    (hfg : ∀ c, f c ≤ g c) :
    binomialExpectation k n f ≤ binomialExpectation k n g := by
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left (hfg c)
  have hb := le_of_lt (beta_pos hk)
  have hq := le_of_lt (q_pos hk)
  positivity

@[simp] theorem binomialExpectation_one (k n : ℕ) :
    binomialExpectation k n (fun _ => 1) = 1 := by
  have h := iidExpectation_count (ι := Fin n) k (fun _ => (1 : ℝ))
  simp only [Fintype.card_fin, iidExpectation_one] at h
  exact h.symm

theorem binomialExpectation_add (k n : ℕ) (f g : ℕ → ℝ) :
    binomialExpectation k n (fun c => f c + g c) =
      binomialExpectation k n f + binomialExpectation k n g := by
  simp [binomialExpectation, mul_add, Finset.sum_add_distrib]

theorem binomial_append_zero {k n N : ℕ} (hk : 8 ≤ k) (hnN : n ≤ N)
    {f : ℕ → ℝ} (hf : ∀ c, 0 ≤ f c) :
    binomialExpectation k n f * q k ^ (N - n) ≤ binomialExpectation k N f := by
  have hq := le_of_lt (q_pos hk)
  have hb := le_of_lt (beta_pos hk)
  unfold binomialExpectation
  rw [Finset.sum_mul]
  calc
    ∑ c ∈ range (n + 1),
        ((Nat.choose n c : ℝ) * beta k ^ c * q k ^ (n - c) * f c) * q k ^ (N - n)
        ≤ ∑ c ∈ range (n + 1),
          (Nat.choose N c : ℝ) * beta k ^ c * q k ^ (N - c) * f c := by
      apply Finset.sum_le_sum
      intro c hc
      have hcn : c ≤ n := by have := Finset.mem_range.mp hc; omega
      have hp : q k ^ (n - c) * q k ^ (N - n) = q k ^ (N - c) := by
        rw [← pow_add]
        congr 1
        omega
      have hchoose : (Nat.choose n c : ℝ) ≤ Nat.choose N c := by
        exact_mod_cast Nat.choose_le_choose c hnN
      calc
        _ = (Nat.choose n c : ℝ) * beta k ^ c * q k ^ (N - c) * f c := by
          rw [← hp]
          ring
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hchoose (pow_nonneg hb _))
              (pow_nonneg hq _)) (hf c)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro c _ _
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg hb _)) (pow_nonneg hq _)) (hf c)

def smallCountProbability (k n : ℕ) : ℝ :=
  binomialExpectation k n (fun c => if c ≤ 4 then 1 else 0)

theorem smallCountProbability_nonneg {k n : ℕ} (hk : 8 ≤ k) :
    0 ≤ smallCountProbability k n := by
  apply binomialExpectation_nonneg hk
  intro c
  split_ifs <;> norm_num

theorem smallCountProbability_deleted {k n : ℕ} (hk : 8 ≤ k) (hn : n ≤ k) :
    smallCountProbability k n ≤ smallCountProbability k k / q k ^ (k - n) := by
  apply (le_div_iff₀ (pow_pos (q_pos hk) _)).mpr
  apply binomial_append_zero hk hn
  intro c
  split_ifs <;> norm_num

theorem smallCountProbability_exp {k : ℕ} (hk : 20 ≤ k) :
    smallCountProbability k k ≤ Real.exp (-(1 : ℝ) / 30) := by
  have hk8 : 8 ≤ k := by omega
  have hsum : smallCountProbability k k + binomialMass k 5 ≤ 1 := by
    have h := binomialExpectation_mono (n := k) hk8
      (f := fun c => (if c ≤ 4 then (1 : ℝ) else 0) +
        (if c = 5 then 1 else 0))
      (g := fun _ => 1) (by
        intro c
        dsimp only
        split_ifs <;> norm_num
        omega)
    rw [binomialExpectation_add, binomialExpectation_one] at h
    have hsingle : binomialExpectation k k (fun c => if c = 5 then 1 else 0) =
        binomialMass k 5 := by
      unfold binomialExpectation
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_range, show 5 < k + 1 by omega, binomialMass]
    rw [hsingle] at h
    exact h
  have hmass := binomial_mass_five_lower_bound hk
  have he := Real.add_one_le_exp (-(1 : ℝ) / 30)
  linarith

end
end SetCover
