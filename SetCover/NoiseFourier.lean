import SetCover.Sampler

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section

theorem maskBitMass_character_sum (k c : ℕ) (t : Bool) :
    ∑ b : Bool, maskBitMass k c b * bitCharacter t b =
      if t then bias k c else 1 := by
  cases t <;> simp [Fintype.sum_bool, maskBitMass, bitCharacter] <;> ring

theorem noiseFourier_product {v M k : ℕ}
    (A : CheapMatrix v M) (t : Cube v) :
    noiseFourier (noiseMass k A) t =
      average (fun K : RepairChoices M k =>
        ∏ e, if t e then bias k (count A K.val e) else 1) := by
  calc
    noiseFourier (noiseMass k A) t
        = average (fun K : RepairChoices M k =>
          ∑ z : Cube v, componentMass A K z * character t z) := by
            unfold noiseFourier noiseMass
            simp_rw [← average_mul_right]
            exact (average_sum _).symm
    _ = _ := by
      congr 1
      funext K
      simp only [componentMass, character, ← Finset.prod_mul_distrib]
      rw [← Fintype.prod_sum (fun (e : Fin v) (b : Bool) =>
        maskBitMass k (count A K.val e) b * bitCharacter (t e) b)]
      simp only [maskBitMass_character_sum]

def sparseProbability {v M : ℕ} (k : ℕ) (A : CheapMatrix v M)
    (D : Finset (Fin v)) : ℝ :=
  average (fun K : RepairChoices M k =>
    if ∀ e ∈ D, count A K.val e ≤ 4 then 1 else 0)

theorem sparseProbability_nonneg {v M k : ℕ} (hkM : k ≤ M)
    (A : CheapMatrix v M) (D : Finset (Fin v)) :
    0 ≤ sparseProbability k A D := by
  letI := repairChoices_nonempty hkM
  apply average_nonneg
  intro K
  split_ifs <;> norm_num

theorem noiseFourier_dominated {v M k : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M)
    (A : CheapMatrix v M) (t : Cube v) (D : Finset (Fin v))
    (hD : ∀ e ∈ D, t e = true) :
    |noiseFourier (noiseMass k A) t| ≤ sparseProbability k A D := by
  classical
  letI := repairChoices_nonempty hkM
  rw [noiseFourier_product]
  apply (abs_average_le _).trans
  apply average_mono
  intro K
  by_cases hall : ∀ e ∈ D, count A K.val e ≤ 4
  · rw [if_pos hall, Finset.abs_prod]
    apply Finset.prod_le_one
    · intro e _
      exact abs_nonneg _
    · intro e _
      cases ht : t e
      · simp
      · simp only [Bool.true_eq, if_true]
        exact abs_bias_le_one hk _
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨e, he, hc⟩ := hall
    have hzero :
        (if t e then bias k (count A K.val e) else 1 : ℝ) = 0 := by
      simp [hD e he, bias, not_le.mpr hc]
    rw [Finset.prod_eq_zero (Finset.mem_univ e) hzero, abs_zero]

end
end SetCover
