import SetCover.Paper.Basic

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def boundedFamilyCode {ι : Type*} (n : ℕ) (F : Finset ι) : Fin n → Option ι :=
  fun j => if h : j.val < F.card then some ((F.equivFin.symm ⟨j.val, h⟩).val) else none

theorem mem_iff_boundedFamilyCode {ι : Type*} {n : ℕ} (F : Finset ι)
    (hF : F.card ≤ n) (i : ι) :
    i ∈ F ↔ ∃ j, boundedFamilyCode n F j = some i := by
  constructor
  · intro hi
    let u := F.equivFin ⟨i, hi⟩
    refine ⟨⟨u.val, lt_of_lt_of_le u.isLt hF⟩, ?_⟩
    simp only [boundedFamilyCode, dif_pos u.isLt]
    change some (F.equivFin.symm (F.equivFin ⟨i, hi⟩)).val = some i
    rw [Equiv.symm_apply_apply]
  · rintro ⟨j, hj⟩
    unfold boundedFamilyCode at hj
    split_ifs at hj with h
    · rw [← Option.some.inj hj]
      exact (F.equivFin.symm ⟨j.val, h⟩).property

theorem boundedFamilies_card_le {ι : Type*} [Fintype ι] (n : ℕ) :
    Fintype.card {F : Finset ι // F.card ≤ n} ≤ (Fintype.card ι + 1) ^ n := by
  calc
    Fintype.card {F : Finset ι // F.card ≤ n} ≤ Fintype.card (Fin n → Option ι) := by
      apply Fintype.card_le_of_injective
        (fun F : {F : Finset ι // F.card ≤ n} => boundedFamilyCode n F.val)
      intro F G h
      change boundedFamilyCode n F.val = boundedFamilyCode n G.val at h
      apply Subtype.ext
      ext i
      rw [mem_iff_boundedFamilyCode F.val F.property i,
        mem_iff_boundedFamilyCode G.val G.property i, h]
    _ = (Fintype.card ι + 1) ^ n := by simp

theorem family_card_le_cost {M r s k : ℕ} (hk : 1 ≤ k)
    (F : Finset (SetId M r s)) : F.card ≤ cost k F := by
  calc
    F.card = ∑ _i ∈ F, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ F, weight k i := by
      apply Finset.sum_le_sum
      intro i _
      cases i with
      | inl j => exact le_rfl
      | inr j => exact hk

abbrev AffordableFamily (k M r s : ℕ) (B : ℝ) :=
  {F : Finset (SetId M r s) // (cost k F : ℝ) ≤ B}

theorem affordableFamilies_card_le {M r s k : ℕ} {B : ℝ}
    (hk : 1 ≤ k) (hB : 0 ≤ B) :
    Fintype.card (AffordableFamily k M r s B) ≤
      (Fintype.card (SetId M r s) + 1) ^ ⌊B⌋₊ := by
  let f : AffordableFamily k M r s B →
      {F : Finset (SetId M r s) // F.card ≤ ⌊B⌋₊} := fun F =>
    ⟨F.val, (Nat.le_floor_iff hB).mpr
      ((Nat.cast_le.mpr (family_card_le_cost hk F.val)).trans F.property)⟩
  exact (Fintype.card_le_of_injective f (fun F G h => Subtype.ext
    (congrArg (fun H : {F : Finset (SetId M r s) // F.card ≤ ⌊B⌋₊} => H.val) h))).trans
      (boundedFamilies_card_le _)

theorem affordableFamilies_card_le_exp {M r s k : ℕ} {B : ℝ}
    (hk : 1 ≤ k) (hB : 0 ≤ B) :
    (Fintype.card (AffordableFamily k M r s B) : ℝ) ≤
      Real.exp (B * Real.log (Fintype.card (SetId M r s) + 1)) := by
  let N := Fintype.card (SetId M r s)
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  calc
    (Fintype.card (AffordableFamily k M r s B) : ℝ) ≤ ((N : ℝ) + 1) ^ ⌊B⌋₊ := by
      exact_mod_cast affordableFamilies_card_le (M := M) (r := r) (s := s) hk hB
    _ = Real.exp ((⌊B⌋₊ : ℝ) * Real.log ((N : ℝ) + 1)) := by
      rw [Real.exp_nat_mul, Real.exp_log hN]
    _ ≤ Real.exp (B * Real.log ((N : ℝ) + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.floor_le hB) hlog)

theorem hasCoverAtMost_iff_affordable {v M r s k : ℕ} (A : CheapMatrix v M)
    (x : Input v r s) (B : ℝ) :
    HasCoverAtMost k A x B ↔
      ∃ F : AffordableFamily k M r s B, IsCover A x F.val := by
  constructor
  · rintro ⟨F, hF, hcost⟩
    exact ⟨⟨F, hcost⟩, hF⟩
  · rintro ⟨F, hF⟩
    exact ⟨F.val, hF, F.property⟩

end
end SetCover.Paper
