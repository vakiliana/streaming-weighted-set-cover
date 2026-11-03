import SetCover.Probability

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

theorem sum_repairChoices {M k : ℕ} (f : Finset (Fin M) → ℝ) :
    (∑ K : RepairChoices M k, f K.val) =
      ∑ K ∈ (univ : Finset (Fin M)).powersetCard k, f K := by
  exact (Finset.sum_subtype _ (fun K => Finset.mem_powersetCard_univ) f).symm

theorem supersets_card {M k : ℕ} (S : Finset (Fin M)) (hSk : S.card ≤ k) :
    (((univ : Finset (Fin M)).powersetCard k).filter (S ⊆ ·)).card =
      (M - S.card).choose (k - S.card) := by
  classical
  let R := (univ \ S).powersetCard (k - S.card)
  have heq : ((univ : Finset (Fin M)).powersetCard k).filter (S ⊆ ·) =
      R.image (fun T => S ∪ T) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powersetCard_univ, Finset.mem_image]
    constructor
    · rintro ⟨hK, hSK⟩
      refine ⟨K \ S, ?_, Finset.union_sdiff_of_subset hSK⟩
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      · rw [Finset.card_sdiff hSK, hK]
    · rintro ⟨T, hT, rfl⟩
      have hT' := Finset.mem_powersetCard.mp hT
      have hdis : Disjoint S T := by
        apply Finset.disjoint_left.mpr
        intro x hxS hxT
        exact (Finset.mem_sdiff.mp (hT'.1 hxT)).2 hxS
      constructor
      · rw [Finset.card_union_of_disjoint hdis, hT'.2]
        omega
      · exact Finset.subset_union_left
  rw [heq, Finset.card_image_of_injOn]
  · simp [R, Finset.card_sdiff (Finset.subset_univ S)]
  · intro T hT U hU h
    change S ∪ T = S ∪ U at h
    have hT' := (Finset.mem_powersetCard.mp hT).1
    have hU' := (Finset.mem_powersetCard.mp hU).1
    apply Finset.ext
    intro x
    have hS (hx : x ∈ T ∨ x ∈ U) : x ∉ S := by
      rcases hx with hx | hx
      · exact (Finset.mem_sdiff.mp (hT' hx)).2
      · exact (Finset.mem_sdiff.mp (hU' hx)).2
    constructor
    · intro hx
      have hx' : x ∈ S ∪ U := by
        rw [← h]
        exact Finset.mem_union_right S hx
      exact (Finset.mem_union.mp hx').resolve_left (hS (Or.inl hx))
    · intro hx
      have hx' : x ∈ S ∪ T := by
        rw [h]
        exact Finset.mem_union_right S hx
      exact (Finset.mem_union.mp hx').resolve_left (hS (Or.inr hx))

theorem average_subset_eq {M k : ℕ} (S : Finset (Fin M))
    (hSk : S.card ≤ k) :
    average (fun K : RepairChoices M k => if S ⊆ K.val then (1 : ℝ) else 0) =
      (Nat.choose (M - S.card) (k - S.card) : ℝ) / Nat.choose M k := by
  unfold average
  rw [sum_repairChoices (M := M) (k := k) (fun K => if S ⊆ K then (1 : ℝ) else 0),
    Finset.sum_boole, supersets_card S hSk]
  simp [RepairChoices, Fintype.card_finset_len]

theorem choose_times_factorial {n j : ℕ} (hj : j ≤ n) :
    (Nat.choose n j : ℝ) * (j.factorial : ℝ) =
      ∏ i ∈ range j, ((n : ℝ) - i) := by
  calc
    (Nat.choose n j : ℝ) * (j.factorial : ℝ) =
        (n.descFactorial j : ℝ) := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
          ring
    _ = ∏ i ∈ range j, ((n : ℝ) - i) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      exact Nat.cast_sub (by have := Finset.mem_range.mp hi; omega)

theorem choose_ratio_le_pow {M k j : ℕ} (hM : 0 < M) (hkM : k ≤ M) (hjk : j ≤ k) :
    (Nat.choose k j : ℝ) / Nat.choose M j ≤ ((k : ℝ) / M) ^ j := by
  have hfact : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hr : (Nat.choose k j : ℝ) / Nat.choose M j =
      ∏ i ∈ range j, (((k : ℝ) - i) / ((M : ℝ) - i)) := by
    rw [Finset.prod_div_distrib, ← choose_times_factorial hjk,
      ← choose_times_factorial (hjk.trans hkM)]
    exact (mul_div_mul_right _ _ hfact).symm
  rw [hr]
  have he : ((k : ℝ) / M) ^ j = ∏ _i ∈ range j, ((k : ℝ) / M) := by
    simp only [Finset.prod_const, Finset.card_range]
  rw [he]
  apply Finset.prod_le_prod
  · intro i hi
    have hiN : i < j := Finset.mem_range.mp hi
    have hiR : (i : ℝ) ≤ k := by exact_mod_cast (show i ≤ k by omega)
    have hiM : (i : ℝ) < M := by exact_mod_cast (show i < M by omega)
    exact div_nonneg (sub_nonneg.mpr hiR) (by linarith)
  · intro i hi
    have hiN : i < j := Finset.mem_range.mp hi
    have hiM : (i : ℝ) < M := by exact_mod_cast (show i < M by omega)
    have hkR : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    apply (div_le_div_iff₀ (by linarith : 0 < (M : ℝ) - i) hMR).mpr
    nlinarith

theorem average_subset_le {M k : ℕ} (hM : 0 < M) (hkM : k ≤ M)
    (S : Finset (Fin M)) :
    average (fun K : RepairChoices M k => if S ⊆ K.val then (1 : ℝ) else 0) ≤
      ((k : ℝ) / M) ^ S.card := by
  letI := repairChoices_nonempty hkM
  by_cases hSk : S.card ≤ k
  · rw [average_subset_eq S hSk]
    have hchooseM : (Nat.choose M k : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast Nat.choose_pos hkM)
    have hchooseS : (Nat.choose M S.card : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast Nat.choose_pos (hSk.trans hkM))
    have he : (Nat.choose (M - S.card) (k - S.card) : ℝ) / Nat.choose M k =
        (Nat.choose k S.card : ℝ) / Nat.choose M S.card := by
      apply (div_eq_div_iff hchooseM hchooseS).mpr
      have hh := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_mul hkM hSk)
      push_cast at hh
      nlinarith
    rw [he]
    exact choose_ratio_le_pow hM hkM hSk
  · have hn (K : RepairChoices M k) : ¬ S ⊆ K.val := by
      intro hs
      have := Finset.card_le_card hs
      rw [K.property] at this
      exact hSk this
    simp_rw [if_neg (hn _)]
    rw [average_const]
    positivity

theorem average_finset_sum {Ω ι : Type*} [Fintype Ω] (s : Finset ι)
    (f : ι → Ω → ℝ) :
    average (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, average (f i) := by
  simp only [average, Finset.sum_div]
  rw [Finset.sum_comm]

theorem overlap_power_expansion {M : ℕ} (U K : Finset (Fin M)) (z : ℝ) :
    z ^ (K ∩ U).card =
      ∑ S ∈ U.powerset, (z - 1) ^ S.card * (if S ⊆ K then (1 : ℝ) else 0) := by
  have hfilter : U.powerset.filter (fun S => S ⊆ K) = (K ∩ U).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => Finset.subset_inter h.2 h.1,
      fun h => ⟨Finset.Subset.trans h Finset.inter_subset_right,
        Finset.Subset.trans h Finset.inter_subset_left⟩⟩
  have hsum : (∑ S ∈ U.powerset,
      (z - 1) ^ S.card * (if S ⊆ K then (1 : ℝ) else 0)) =
      ∑ S ∈ (K ∩ U).powerset, (z - 1) ^ S.card := by
    simp_rw [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    rw [hfilter]
  rw [hsum]
  simpa using (Finset.sum_pow_mul_eq_add_pow (z - 1) (1 : ℝ) (K ∩ U)).symm

theorem overlap_mgf_le {M k : ℕ} (hM : 0 < M) (hkM : k ≤ M)
    (U : Finset (Fin M)) {z : ℝ} (hz : 1 ≤ z) :
    average (fun K : RepairChoices M k => z ^ (K.val ∩ U).card) ≤
      Real.exp ((k : ℝ) * U.card / M * (z - 1)) := by
  letI := repairChoices_nonempty hkM
  have hz0 : 0 ≤ z - 1 := by linarith
  have ha0 : 0 ≤ (z - 1) * ((k : ℝ) / M) := by positivity
  calc
    average (fun K : RepairChoices M k => z ^ (K.val ∩ U).card)
        = ∑ S ∈ U.powerset, (z - 1) ^ S.card *
          average (fun K : RepairChoices M k => if S ⊆ K.val then (1 : ℝ) else 0) := by
            simp_rw [overlap_power_expansion, average_finset_sum, average_mul]
    _ ≤ ∑ S ∈ U.powerset, (z - 1) ^ S.card * ((k : ℝ) / M) ^ S.card := by
          apply Finset.sum_le_sum
          intro S _
          exact mul_le_mul_of_nonneg_left (average_subset_le hM hkM S) (pow_nonneg hz0 _)
    _ = (1 + (z - 1) * ((k : ℝ) / M)) ^ U.card := by
      simp_rw [← mul_pow]
      simpa [add_comm] using Finset.sum_pow_mul_eq_add_pow
        ((z - 1) * ((k : ℝ) / M)) (1 : ℝ) U
    _ ≤ Real.exp ((z - 1) * ((k : ℝ) / M)) ^ U.card := by
      apply pow_le_pow_left₀ (by linarith : 0 ≤ 1 + (z - 1) * ((k : ℝ) / M))
      simpa [add_comm] using Real.add_one_le_exp ((z - 1) * ((k : ℝ) / M))
    _ = Real.exp ((k : ℝ) * U.card / M * (z - 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end
end SetCover
