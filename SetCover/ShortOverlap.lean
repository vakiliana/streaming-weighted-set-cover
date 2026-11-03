import SetCover.ShortRow

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

theorem short_average_count {Ω : Type*} [Fintype Ω] (J : Ω → ℕ)
    (n : ℕ) (hJ : ∀ x, J x ≤ n) (f : ℕ → ℝ) :
    average (fun x => f (J x)) =
      ∑ j ∈ range (n + 1), f j *
        average (fun x => if J x = j then (1 : ℝ) else 0) := by
  have he (x : Ω) : f (J x) =
      ∑ j ∈ range (n + 1), f j * (if J x = j then (1 : ℝ) else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_iff, hJ x]
  simp_rw [he, average_finset_sum, average_mul]

theorem short_overlap_event_le {M k : ℕ} (hM : 0 < M) (hkM : k ≤ M)
    (U : Finset (Fin M)) (hU : U.card = k) (j : ℕ) :
    average (fun K : RepairChoices M k =>
      if (K.val ∩ U).card = j then (1 : ℝ) else 0) ≤
        lambda k M ^ j / j.factorial := by
  letI := repairChoices_nonempty hkM
  have hpoint (K : RepairChoices M k) :
      (if (K.val ∩ U).card = j then (1 : ℝ) else 0) ≤
        ∑ S ∈ U.powersetCard j, if S ⊆ K.val then (1 : ℝ) else 0 := by
    by_cases hj : (K.val ∩ U).card = j
    · rw [if_pos hj]
      have hmem : K.val ∩ U ∈ U.powersetCard j :=
        Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hj⟩
      calc
        (1 : ℝ) = if K.val ∩ U ⊆ K.val then 1 else 0 := by
          rw [if_pos Finset.inter_subset_left]
        _ ≤ _ := by
          exact Finset.single_le_sum (f := fun S : Finset (Fin M) =>
            if S ⊆ K.val then (1 : ℝ) else 0)
            (fun S _ => by dsimp only; split_ifs <;> norm_num) hmem
    · rw [if_neg hj]
      exact Finset.sum_nonneg fun S _ => by split_ifs <;> norm_num
  calc
    _ ≤ average (fun K : RepairChoices M k =>
        ∑ S ∈ U.powersetCard j, if S ⊆ K.val then (1 : ℝ) else 0) :=
      average_mono hpoint
    _ = ∑ S ∈ U.powersetCard j,
        average (fun K : RepairChoices M k => if S ⊆ K.val then (1 : ℝ) else 0) :=
      average_finset_sum _ _
    _ ≤ ∑ _S ∈ U.powersetCard j, ((k : ℝ) / M) ^ j := by
      apply Finset.sum_le_sum
      intro S hS
      simpa only [(Finset.mem_powersetCard.mp hS).2] using average_subset_le hM hkM S
    _ = (Nat.choose k j : ℝ) * ((k : ℝ) / M) ^ j := by simp [hU]
    _ ≤ ((k : ℝ) ^ j / j.factorial) * ((k : ℝ) / M) ^ j := by
      exact mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j k) (by positivity)
    _ = _ := by
      rw [div_mul_eq_mul_div, ← mul_pow]
      congr 2
      unfold lambda
      ring

theorem short_exp_exp_one_le : Real.exp (Real.exp 1) ≤ 64 := by
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  calc
    Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr he
    _ = Real.exp 1 ^ 3 := by norm_num [← Real.exp_nat_mul]
    _ ≤ (3 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
    _ ≤ 64 := by norm_num

theorem short_overlap_exp_tail_le {M k : ℕ} (hM : 0 < M) (hkM : k ≤ M)
    (hlam : lambda k M ≤ 1) (U : Finset (Fin M)) (hU : U.card = k) :
    average (fun K : RepairChoices M k =>
      if 4 ≤ (K.val ∩ U).card then Real.exp ((K.val ∩ U).card : ℝ) else 0) ≤
        64 * lambda k M ^ 4 := by
  letI := repairChoices_nonempty hkM
  have hlam0 : 0 ≤ lambda k M := by unfold lambda; positivity
  rw [short_average_count (fun K : RepairChoices M k => (K.val ∩ U).card)
    k (fun K => by
      calc
        (K.val ∩ U).card ≤ K.val.card := Finset.card_le_card Finset.inter_subset_left
        _ = k := K.property)
    (fun j => if 4 ≤ j then Real.exp (j : ℝ) else 0)]
  calc
    _ ≤ ∑ j ∈ range (k + 1), lambda k M ^ 4 * (Real.exp 1 ^ j / j.factorial) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : 4 ≤ j
      · rw [if_pos hj]
        calc
          _ ≤ Real.exp (j : ℝ) * (lambda k M ^ j / j.factorial) :=
            mul_le_mul_of_nonneg_left (short_overlap_event_le hM hkM U hU j)
              (Real.exp_pos _).le
          _ ≤ Real.exp (j : ℝ) * (lambda k M ^ 4 / j.factorial) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            exact div_le_div_of_nonneg_right
              (pow_le_pow_of_le_one hlam0 hlam hj) (by positivity)
          _ = _ := by
            have he : Real.exp (j : ℝ) = Real.exp 1 ^ j := by
              simp [← Real.exp_nat_mul]
            rw [he]
            ring
      · rw [if_neg hj, zero_mul]
        positivity
    _ = lambda k M ^ 4 * ∑ j ∈ range (k + 1), Real.exp 1 ^ j / j.factorial := by
      rw [Finset.mul_sum]
    _ ≤ lambda k M ^ 4 * Real.exp (Real.exp 1) :=
      mul_le_mul_of_nonneg_left
        (Real.sum_le_exp_of_nonneg (Real.exp_pos _).le _) (pow_nonneg hlam0 _)
    _ ≤ 64 * lambda k M ^ 4 := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left short_exp_exp_one_le (pow_nonneg hlam0 4)

theorem short_overlap_moment_tail_le {M k : ℕ} (hM : 0 < M) (hkM : k ≤ M)
    (hlam : lambda k M ≤ 1) (U : Finset (Fin M)) (hU : U.card = k) (s : ℕ) :
    average (fun K : RepairChoices M k =>
      if 4 ≤ (K.val ∩ U).card then ((K.val ∩ U).card : ℝ) ^ s else 0) ≤
        64 * (s.factorial : ℝ) * lambda k M ^ 4 := by
  letI := repairChoices_nonempty hkM
  have hf : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  calc
    _ ≤ average (fun K : RepairChoices M k =>
        (s.factorial : ℝ) *
          (if 4 ≤ (K.val ∩ U).card then Real.exp ((K.val ∩ U).card : ℝ) else 0)) := by
      apply average_mono
      intro K
      split_ifs
      · have h := Real.pow_div_factorial_le_exp ((K.val ∩ U).card : ℝ)
          (by positivity : (0 : ℝ) ≤ (K.val ∩ U).card) s
        simpa [mul_comm] using (div_le_iff₀ hf).mp h
      · simp
    _ = (s.factorial : ℝ) * average (fun K : RepairChoices M k =>
        if 4 ≤ (K.val ∩ U).card then Real.exp ((K.val ∩ U).card : ℝ) else 0) :=
      average_mul _ _
    _ ≤ (s.factorial : ℝ) * (64 * lambda k M ^ 4) :=
      mul_le_mul_of_nonneg_left (short_overlap_exp_tail_le hM hkM hlam U hU) hf.le
    _ = _ := by ring

theorem short_row_moment_le {M k : ℕ} (hk : 64 ≤ k) (hkM : k ≤ M)
    (hlam : lambda k M ≤ 1) (U : Finset (Fin M)) (hU : U.card = k)
    {t : ℕ} (ht : 0 < t) :
    average (fun K : RepairChoices M k => shortRowCorrelation k U K.val ^ t) ≤
      64 * lambda k M ^ 4 * ((4 * (t : ℝ)) / k) ^ (4 * t) := by
  letI := repairChoices_nonempty hkM
  have hk8 : 8 ≤ k := by omega
  have hM : 0 < M := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpoint (K : RepairChoices M k) :
      shortRowCorrelation k U K.val ^ t ≤
        (if 4 ≤ (K.val ∩ U).card then ((K.val ∩ U).card : ℝ) ^ (4 * t) else 0) /
          (k : ℝ) ^ (4 * t) := by
    by_cases hj : 4 ≤ (K.val ∩ U).card
    · rw [if_pos hj]
      have h := pow_le_pow_left₀
        (short_row_correlation_nonneg hk8 U K.val hU K.property)
        (short_row_correlation_le hk U K.val hU K.property) t
      simpa [← pow_mul, div_pow, Finset.inter_comm] using h
    · have hzero := short_row_correlation_zero hk8 U K.val hU K.property
        (by simpa [Finset.inter_comm] using Nat.lt_of_not_ge hj)
      simp [if_neg hj, hzero, Nat.ne_of_gt ht]
  calc
    _ ≤ average (fun K : RepairChoices M k =>
        (if 4 ≤ (K.val ∩ U).card then ((K.val ∩ U).card : ℝ) ^ (4 * t) else 0) /
          (k : ℝ) ^ (4 * t)) := average_mono hpoint
    _ = average (fun K : RepairChoices M k =>
        if 4 ≤ (K.val ∩ U).card then ((K.val ∩ U).card : ℝ) ^ (4 * t) else 0) /
          (k : ℝ) ^ (4 * t) := by
      simp [average, Finset.sum_div, div_div, mul_comm]
    _ ≤ (64 * ((4 * t).factorial : ℝ) * lambda k M ^ 4) / (k : ℝ) ^ (4 * t) :=
      div_le_div_of_nonneg_right
        (short_overlap_moment_tail_le hM hkM hlam U hU (4 * t)) (pow_nonneg hk0.le _)
    _ ≤ (64 * ((4 * (t : ℝ)) ^ (4 * t)) * lambda k M ^ 4) /
        (k : ℝ) ^ (4 * t) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hk0.le _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact_mod_cast Nat.factorial_le_pow (4 * t)
    _ = _ := by rw [div_pow]; ring

end
end SetCover
