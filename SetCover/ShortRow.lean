import SetCover.ShortKernel

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

theorem short_expectation_sum {Ω ι : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (s : Finset ι) (f : ι → Ω → ℝ) :
    expectation μ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, expectation μ (f i) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem short_expectation_div {Ω : Type*} [Fintype Ω]
    (μ f : Ω → ℝ) (c : ℝ) :
    expectation μ (fun x => f x / c) = expectation μ f / c := by
  simp [expectation, mul_div_assoc, Finset.sum_div]

def shortRowCorrelation {M : ℕ} (k : ℕ) (K L : Finset (Fin M)) : ℝ :=
  expectation (rowMass k) (fun row =>
    bias k (K.filter (fun i => row i = true)).card *
      bias k (L.filter (fun i => row i = true)).card)

theorem short_row_correlation_eq {M k : ℕ} (hk : 8 ≤ k)
    (K L : Finset (Fin M)) (hK : K.card = k) (hL : L.card = k) :
    shortRowCorrelation k K L =
      (q k ^ (K ∪ L).card *
        ∑ S ∈ (K ∩ L).powersetCard 4, ∑ T ∈ (K ∩ L).powersetCard 4,
          ∏ i ∈ T, (if i ∈ S then (beta k)⁻¹ else 1)) /
        (Nat.choose k 4 : ℝ) ^ 2 := by
  let F := fun S T => expectation (rowMass k)
    (fun row => shortMarked k K S row * shortMarked k L T row)
  have hfull : shortRowCorrelation k K L =
      (∑ S ∈ K.powersetCard 4, ∑ T ∈ L.powersetCard 4, F S T) /
        (Nat.choose k 4 : ℝ) ^ 2 := by
    unfold shortRowCorrelation
    simp_rw [short_bias_marked hk K hK, short_bias_marked hk L hL,
      div_mul_div_comm, ← pow_two, short_expectation_div,
      Finset.sum_mul, Finset.mul_sum, short_expectation_sum]
    rfl
  rw [hfull]
  congr 1
  have hS : (∑ S ∈ K.powersetCard 4, ∑ T ∈ L.powersetCard 4, F S T) =
      ∑ S ∈ (K ∩ L).powersetCard 4, ∑ T ∈ L.powersetCard 4, F S T := by
    symm
    apply Finset.sum_subset (Finset.powersetCard_mono Finset.inter_subset_left)
    intro S hSK hSJ
    have hS := Finset.mem_powersetCard.mp hSK
    have hSL : ¬ S ⊆ L := by
      intro h
      exact hSJ (Finset.mem_powersetCard.mpr ⟨Finset.subset_inter hS.1 h, hS.2⟩)
    apply Finset.sum_eq_zero
    intro T _
    exact short_marked_cross_zero hk K L S T hS.1 hSL
  rw [hS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hSJ
  have hS := (Finset.mem_powersetCard.mp hSJ).1
  have hT : (∑ T ∈ L.powersetCard 4, F S T) =
      ∑ T ∈ (K ∩ L).powersetCard 4, F S T := by
    symm
    apply Finset.sum_subset (Finset.powersetCard_mono Finset.inter_subset_right)
    intro T hTL hTJ
    have hT := Finset.mem_powersetCard.mp hTL
    have hTK : ¬ T ⊆ K := by
      intro h
      exact hTJ (Finset.mem_powersetCard.mpr ⟨Finset.subset_inter h hT.1, hT.2⟩)
    simpa [F, mul_comm] using short_marked_cross_zero hk L K T S hT.1 hTK
  rw [hT, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hTJ
  have hT := (Finset.mem_powersetCard.mp hTJ).1
  exact short_marked_cross hk K L S T
    (hS.trans Finset.inter_subset_left) (hT.trans Finset.inter_subset_right)
    (hS.trans Finset.inter_subset_right) (hT.trans Finset.inter_subset_left)

theorem short_row_correlation_nonneg {M k : ℕ} (hk : 8 ≤ k)
    (K L : Finset (Fin M)) (hK : K.card = k) (hL : L.card = k) :
    0 ≤ shortRowCorrelation k K L := by
  rw [short_row_correlation_eq hk K L hK hL]
  apply div_nonneg
  · apply mul_nonneg (pow_nonneg (q_pos hk).le _)
    apply Finset.sum_nonneg
    intro S _
    apply Finset.sum_nonneg
    intro T _
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact inv_nonneg.mpr (beta_pos hk).le
    · norm_num
  · positivity

theorem short_row_correlation_zero {M k : ℕ} (hk : 8 ≤ k)
    (K L : Finset (Fin M)) (hK : K.card = k) (hL : L.card = k)
    (hJ : (K ∩ L).card < 4) :
    shortRowCorrelation k K L = 0 := by
  rw [short_row_correlation_eq hk K L hK hL,
    Finset.powersetCard_eq_empty.mpr hJ]
  simp

theorem short_four_weight_sum {M k : ℕ} (_hk : 8 ≤ k)
    (J S : Finset (Fin M)) (hJ : J.card ≤ k)
    (hS : S ∈ J.powersetCard 4) :
    (∑ i ∈ J, if i ∈ S then (beta k)⁻¹ else 1) ≤ 2 * k := by
  have hS' := Finset.mem_powersetCard.mp hS
  have he (i : Fin M) : (if i ∈ S then (beta k)⁻¹ else (1 : ℝ)) =
      1 + (if i ∈ S then (beta k)⁻¹ - 1 else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hS'.1]
  simp only [Finset.sum_const, nsmul_eq_mul, hS'.2, Nat.cast_ofNat]
  have hJR : (J.card : ℝ) ≤ k := by exact_mod_cast hJ
  have hb : (beta k)⁻¹ = (k : ℝ) / 4 := by simp [beta]
  rw [hb]
  linarith

theorem short_q_pow_le {k : ℕ} (hk : 8 ≤ k) :
    q k ^ k ≤ (1 / 32 : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hq : q k ≤ Real.exp (-beta k) := by
    simpa [q, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-beta k)
  have h := pow_le_pow_left₀ (q_pos hk).le hq k
  rw [← Real.exp_nat_mul] at h
  have he : (k : ℝ) * -beta k = -4 := by
    unfold beta
    field_simp
    ring
  rw [he] at h
  apply h.trans
  have hlow : (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) hlow 4
  have h32 : (32 : ℝ) ≤ Real.exp 4 := by
    have he4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      norm_num [← Real.exp_nat_mul]
    rw [he4]
    norm_num at hpow
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h32

theorem short_choose_four_lower {k : ℕ} (hk : 64 ≤ k) :
    (k : ℝ) ^ 4 ≤ 32 * (Nat.choose k 4 : ℝ) := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod : ((15 / 16 : ℝ) * k) ^ 4 ≤
      ∏ i ∈ range 4, ((k : ℝ) - i) := by
    calc
      ((15 / 16 : ℝ) * k) ^ 4 = ∏ _i ∈ range 4, ((15 / 16 : ℝ) * k) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro i _
          positivity
        · intro i hi
          have hiR : (i : ℝ) ≤ 3 := by
            exact_mod_cast (show i ≤ 3 by have := Finset.mem_range.mp hi; omega)
          linarith
  rw [← choose_times_factorial (show 4 ≤ k by omega)] at hprod
  norm_num [Nat.factorial] at hprod
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ k) 4]

theorem short_row_correlation_le {M k : ℕ} (hk : 64 ≤ k)
    (K L : Finset (Fin M)) (hK : K.card = k) (hL : L.card = k) :
    shortRowCorrelation k K L ≤ ((K ∩ L).card / (k : ℝ)) ^ 4 := by
  have hk8 : 8 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc0 : (0 : ℝ) < Nat.choose k 4 :=
    by exact_mod_cast Nat.choose_pos (show 4 ≤ k by omega)
  let J := K ∩ L
  have hJ : J.card ≤ k := by
    exact hK ▸ Finset.card_le_card Finset.inter_subset_left
  have hw (S : Finset (Fin M)) (i : Fin M) :
      0 ≤ (if i ∈ S then (beta k)⁻¹ else (1 : ℝ)) := by
    split_ifs
    · exact inv_nonneg.mpr (beta_pos hk8).le
    · norm_num
  have hinner (S : Finset (Fin M)) (hS : S ∈ J.powersetCard 4) :
      (∑ T ∈ J.powersetCard 4, ∏ i ∈ T, if i ∈ S then (beta k)⁻¹ else 1) ≤
        (2 * (k : ℝ)) ^ 4 / 24 := by
    calc
      _ ≤ (∑ i ∈ J, if i ∈ S then (beta k)⁻¹ else 1) ^ 4 / (Nat.factorial 4 : ℝ) :=
        short_esymm_le J _ (fun i _ => hw S i) 4
      _ ≤ _ := by
        norm_num [Nat.factorial]
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => hw S i))
            (short_four_weight_sum hk8 J S hJ hS) 4) (by norm_num)
  have hsum : (∑ S ∈ J.powersetCard 4, ∑ T ∈ J.powersetCard 4,
      ∏ i ∈ T, if i ∈ S then (beta k)⁻¹ else 1) ≤
      (J.card : ℝ) ^ 4 / 24 * ((2 * (k : ℝ)) ^ 4 / 24) := by
    calc
      _ ≤ ∑ _S ∈ J.powersetCard 4, (2 * (k : ℝ)) ^ 4 / 24 :=
        Finset.sum_le_sum hinner
      _ = (Nat.choose J.card 4 : ℝ) * ((2 * (k : ℝ)) ^ 4 / 24) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa [Nat.factorial] using (Nat.choose_le_pow_div 4 J.card : _ ≤ (_ : ℝ))
  have hqpow : q k ^ (K ∪ L).card ≤ (1 / 32 : ℝ) := by
    apply le_trans _ (short_q_pow_le hk8)
    apply pow_le_pow_of_le_one (q_pos hk8).le
      (by have := beta_pos hk8; unfold q; linarith)
    exact hK ▸ Finset.card_le_card Finset.subset_union_left
  have hsum0 : 0 ≤ (∑ S ∈ J.powersetCard 4, ∑ T ∈ J.powersetCard 4,
      ∏ i ∈ T, if i ∈ S then (beta k)⁻¹ else 1) := by
    exact Finset.sum_nonneg fun S _ =>
      Finset.sum_nonneg fun T _ => Finset.prod_nonneg fun i _ => hw S i
  rw [short_row_correlation_eq hk8 K L hK hL]
  change _ ≤ ((J.card : ℝ) / k) ^ 4
  calc
    _ ≤ ((1 / 32 : ℝ) *
        ((J.card : ℝ) ^ 4 / 24 * ((2 * (k : ℝ)) ^ 4 / 24))) /
        (Nat.choose k 4 : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hqpow hsum hsum0 (by norm_num)
    _ ≤ _ := by
      have hchoose := short_choose_four_lower hk
      have hsquare := pow_le_pow_left₀ (pow_nonneg hk0.le 4) hchoose 2
      rw [div_pow]
      apply (div_le_div_iff₀ (sq_pos_of_pos hc0) (pow_pos hk0 4)).mpr
      have hJ4 : (0 : ℝ) ≤ (J.card : ℝ) ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsquare hJ4]

end
end SetCover
