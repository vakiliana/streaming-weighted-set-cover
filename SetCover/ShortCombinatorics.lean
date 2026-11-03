import SetCover.UniformSubsets

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section

theorem short_supersets_card {α : Type*} [DecidableEq α]
    (U S : Finset α) (hSU : S ⊆ U) {n : ℕ} (hSn : S.card ≤ n) :
    ((U.powersetCard n).filter (S ⊆ ·)).card =
      (U.card - S.card).choose (n - S.card) := by
  let R := (U \ S).powersetCard (n - S.card)
  have heq : (U.powersetCard n).filter (S ⊆ ·) = R.image (fun T => S ∪ T) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image]
    constructor
    · rintro ⟨⟨hKU, hK⟩, hSK⟩
      refine ⟨K \ S, ?_, Finset.union_sdiff_of_subset hSK⟩
      exact Finset.mem_powersetCard.mpr
        ⟨fun x hx => Finset.mem_sdiff.mpr
          ⟨hKU (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩,
          by rw [Finset.card_sdiff hSK, hK]⟩
    · rintro ⟨T, hT, rfl⟩
      have hT' := Finset.mem_powersetCard.mp hT
      have hdis : Disjoint S T := by
        apply Finset.disjoint_left.mpr
        intro x hxS hxT
        exact (Finset.mem_sdiff.mp (hT'.1 hxT)).2 hxS
      refine ⟨⟨Finset.union_subset hSU (hT'.1.trans Finset.sdiff_subset), ?_⟩,
        Finset.subset_union_left⟩
      rw [Finset.card_union_of_disjoint hdis, hT'.2, Nat.add_sub_of_le hSn]
  rw [heq, Finset.card_image_of_injOn]
  · simp [R, Finset.card_sdiff hSU]
  · intro T hT V hV h
    change S ∪ T = S ∪ V at h
    have hT' := (Finset.mem_powersetCard.mp hT).1
    have hV' := (Finset.mem_powersetCard.mp hV).1
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hx' : x ∈ S ∪ V := h ▸ Finset.mem_union_right S hx
      exact (Finset.mem_union.mp hx').resolve_left
        (Finset.mem_sdiff.mp (hT' hx)).2
    · intro hx
      have hx' : x ∈ S ∪ T := h.symm ▸ Finset.mem_union_right S hx
      exact (Finset.mem_union.mp hx').resolve_left
        (Finset.mem_sdiff.mp (hV' hx)).2

theorem short_binomial_first_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    a ^ (n + 1) + (n + 1 : ℝ) * b * a ^ n ≤ (a + b) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right ih (add_nonneg ha hb)
    have hz : 0 ≤ (n + 1 : ℝ) * b ^ 2 * a ^ n := by positivity
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at *
    nlinarith

theorem short_esymm_insert {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (ha : a ∉ s) (w : α → ℝ) (n : ℕ) :
    (∑ T ∈ (insert a s).powersetCard (n + 1), ∏ i ∈ T, w i) =
      (∑ T ∈ s.powersetCard (n + 1), ∏ i ∈ T, w i) +
        w a * ∑ T ∈ s.powersetCard n, ∏ i ∈ T, w i := by
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union, Finset.sum_image]
  · rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro T hT
    exact Finset.prod_insert (fun h => ha ((Finset.mem_powersetCard.mp hT).1 h))
  · intro T hT V hV h
    have hTa : a ∉ T := fun ht => ha ((Finset.mem_powersetCard.mp hT).1 ht)
    have hVa : a ∉ V := fun hv => ha ((Finset.mem_powersetCard.mp hV).1 hv)
    simpa [hTa, hVa] using congrArg (fun U : Finset α => U.erase a) h
  · apply Finset.disjoint_left.mpr
    intro T hT h
    obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp h
    exact ha ((Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self _ _))

theorem short_esymm_factorial_le {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (n : ℕ) :
    (n.factorial : ℝ) * (∑ T ∈ s.powersetCard n, ∏ i ∈ T, w i) ≤
      (∑ i ∈ s, w i) ^ n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert a s ha ih =>
    have hwa := hw a (Finset.mem_insert_self _ _)
    have hws : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    cases n with
    | zero => simp
    | succ n =>
      rw [short_esymm_insert s a ha, Finset.sum_insert ha]
      have h₁ := ih hws (n + 1)
      have h₂ := mul_le_mul_of_nonneg_left (ih hws n)
        (mul_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) hwa)
      have h₃ := short_binomial_first_two
        (Finset.sum_nonneg hws) hwa n
      have hf : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * n.factorial := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hf] at h₁ ⊢
      rw [add_comm (w a)]
      nlinarith

theorem short_esymm_le {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (n : ℕ) :
    (∑ T ∈ s.powersetCard n, ∏ i ∈ T, w i) ≤
      (∑ i ∈ s, w i) ^ n / n.factorial := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact (le_div_iff₀ hf).mpr (by
    simpa [mul_comm] using short_esymm_factorial_le s w hw n)

end
end SetCover
