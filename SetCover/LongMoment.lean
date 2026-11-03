import SetCover.BinomialTail
import SetCover.SharedColumns

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def jointCountProbability {M k L : ℕ} (ks : Fin L → RepairChoices M k) : ℝ :=
  iidExpectation k (fun x : Fin M → Bool =>
    ∏ a, if supportCount (ks a).val x ≤ 4 then 1 else 0)

theorem jointCountProbability_nonneg {M k L : ℕ} (hk : 8 ≤ k)
    (ks : Fin L → RepairChoices M k) : 0 ≤ jointCountProbability ks := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j _ => matrixBitMass_nonneg hk (x j)
  · apply Finset.prod_nonneg
    intro a _
    split_ifs <;> norm_num

theorem jointCountProbability_deleted {M k L : ℕ} (hk : 8 ≤ k)
    (ks : Fin L → RepairChoices M k) :
    jointCountProbability ks ≤
      smallCountProbability k k ^ L * (q k)⁻¹ ^ (2 * replicaExcess ks) := by
  have hq : 0 < q k := q_pos hk
  have hq1 : q k ≤ 1 := by unfold q; have := beta_pos hk; linarith
  have hqi : 1 ≤ (q k)⁻¹ := (one_le_inv₀ hq).mpr hq1
  have hb : 0 ≤ smallCountProbability k k := smallCountProbability_nonneg hk
  calc
    jointCountProbability ks ≤ iidExpectation k (fun x : Fin M → Bool =>
        ∏ a, if supportCount (uniqueColumns ks a) x ≤ 4 then 1 else 0) := by
      apply iidExpectation_mono hk
      intro x
      apply Finset.prod_le_prod
      · intro a _
        split_ifs <;> norm_num
      · intro a _
        have hcnt : supportCount (uniqueColumns ks a) x ≤ supportCount (ks a).val x := by
          apply Finset.card_le_card
          exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
        split_ifs <;> norm_num
        omega
    _ = ∏ a, smallCountProbability k (uniqueColumns ks a).card := by
      exact iidExpectation_disjoint_counts k (uniqueColumns ks) (uniqueColumns_pairwise ks)
        (fun _ c => if c ≤ 4 then 1 else 0)
    _ ≤ ∏ a, smallCountProbability k k / q k ^ sharedCount ks a := by
      apply Finset.prod_le_prod
      · intro a _
        exact smallCountProbability_nonneg hk
      · intro a _
        have hcard := unique_shared_card ks a
        have hn : (uniqueColumns ks a).card ≤ k := by omega
        have hh := smallCountProbability_deleted hk hn
        rwa [show k - (uniqueColumns ks a).card = sharedCount ks a by omega] at hh
    _ = smallCountProbability k k ^ L * (q k)⁻¹ ^ (∑ a, sharedCount ks a) := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_pow_eq_pow_sum, div_eq_mul_inv, inv_pow]
    _ ≤ smallCountProbability k k ^ L * (q k)⁻¹ ^ (2 * replicaExcess ks) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb L)
      exact pow_le_pow_right₀ hqi (shared_counts_le_twice_excess ks)

theorem average_power {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (L : ℕ) :
    average f ^ L = average (fun ks : Fin L → Ω => ∏ a, f (ks a)) := by
  classical
  simp only [average, div_pow, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [Fintype.sum_pow]

theorem expectation_average_comm {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (ν : Ω → ℝ) (F : Ω → Γ → ℝ) :
    expectation ν (fun x => average (F x)) =
      average (fun y => expectation ν (fun x => F x y)) := by
  simp only [expectation, average, ← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem iidExpectation_fin_eq {M : ℕ} (k : ℕ) (f : (Fin M → Bool) → ℝ) :
    iidExpectation k f = expectation (rowMass k) f := by
  unfold iidExpectation expectation iidMass rowMass
  congr 1
  ext x
  simp

theorem matrix_product_rows {v M : ℕ} (k : ℕ) (D : Finset (Fin v))
    (f : (Fin M → Bool) → ℝ) :
    expectation (matrixMass k) (fun A : CheapMatrix v M => ∏ e ∈ D, f (A e)) =
      iidExpectation k f ^ D.card := by
  calc
    expectation (matrixMass k) (fun A : CheapMatrix v M => ∏ e ∈ D, f (A e))
        = ∑ A : CheapMatrix v M, ∏ e, rowMass k (A e) *
          (if e ∈ D then f (A e) else 1) := by
          unfold expectation matrixMass rowMass
          apply Finset.sum_congr rfl
          intro A _
          rw [Finset.prod_mul_distrib]
          simp
    _ = ∏ e : Fin v, ∑ row : Fin M → Bool, rowMass k row *
          (if e ∈ D then f row else 1) := by
          rw [← Fintype.prod_sum (fun (e : Fin v) (row : Fin M → Bool) =>
            rowMass k row * (if e ∈ D then f row else 1))]
    _ = ∏ e : Fin v, if e ∈ D then iidExpectation k f else 1 := by
          apply Finset.prod_congr rfl
          intro e _
          by_cases he : e ∈ D
          · simp only [he, ite_true]
            exact (iidExpectation_fin_eq k f).symm
          · simp [he, rowMass_sum]
    _ = iidExpectation k f ^ D.card := by simp

theorem sparse_moment_replicas {v M k : ℕ} (D : Finset (Fin v)) (L : ℕ) :
    expectation (matrixMass k) (fun A : CheapMatrix v M => sparseProbability k A D ^ L) =
      average (fun ks : Fin L → RepairChoices M k => jointCountProbability ks ^ D.card) := by
  unfold sparseProbability
  simp_rw [average_power]
  rw [expectation_average_comm]
  congr 1
  funext ks
  have hind (A : CheapMatrix v M) :
      (∏ a : Fin L, if ∀ e ∈ D, count A (ks a).val e ≤ 4 then (1 : ℝ) else 0) =
        ∏ e ∈ D, ∏ a : Fin L, if supportCount (ks a).val (A e) ≤ 4 then 1 else 0 := by
    simp only [count, supportCount, Fintype.prod_ite_zero, Finset.prod_const_one,
      Finset.prod_ite_zero]
    congr 1
    aesop
  simp_rw [hind]
  exact matrix_product_rows k D
    (fun x => ∏ a : Fin L, if supportCount (ks a).val x ≤ 4 then 1 else 0)

theorem sparse_moment_bound {v M k : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M)
    (D : Finset (Fin v)) (L : ℕ) :
    expectation (matrixMass k) (fun A : CheapMatrix v M => sparseProbability k A D ^ L) ≤
      smallCountProbability k k ^ (L * D.card) *
        Real.exp (lambda k M * L * (L - 1 : ℝ) / 2 *
          (((q k)⁻¹) ^ (2 * D.card) - 1)) := by
  letI := repairChoices_nonempty hkM
  have hM : 0 < M := by omega
  have hq : 0 < q k := q_pos hk
  have hq1 : q k ≤ 1 := by unfold q; have := beta_pos hk; linarith
  have hqi : 1 ≤ (q k)⁻¹ := (one_le_inv₀ hq).mpr hq1
  have hb : 0 ≤ smallCountProbability k k := smallCountProbability_nonneg hk
  let z := ((q k)⁻¹) ^ (2 * D.card)
  have hz : 1 ≤ z := one_le_pow₀ hqi
  rw [sparse_moment_replicas]
  calc
    average (fun ks : Fin L → RepairChoices M k => jointCountProbability ks ^ D.card)
        ≤ average (fun ks : Fin L → RepairChoices M k =>
            smallCountProbability k k ^ (L * D.card) * z ^ replicaExcess ks) := by
          apply average_mono
          intro ks
          have hpow := pow_le_pow_left₀ (jointCountProbability_nonneg hk ks)
            (jointCountProbability_deleted hk ks) D.card
          convert hpow using 1
          simp only [mul_pow, ← pow_mul, z]
          congr 1
          ring
    _ = smallCountProbability k k ^ (L * D.card) *
        average (fun ks : Fin L → RepairChoices M k => z ^ replicaExcess ks) := average_mul _ _
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (replica_overlap_mgf hM hkM hz L) (pow_nonneg hb _)

theorem sparse_moment_exponential {v M k L : ℕ} (hk : 20 ≤ k) (hkM : k ≤ M)
    (D : Finset (Fin v))
    (hcorrection : lambda k M * L * (L - 1 : ℝ) / 2 *
      (((q k)⁻¹) ^ (2 * D.card) - 1) ≤ (L : ℝ) * D.card / 120) :
    expectation (matrixMass k) (fun A : CheapMatrix v M => sparseProbability k A D ^ L) ≤
      Real.exp (-(L : ℝ) * D.card / 40) := by
  have hk8 : 8 ≤ k := by omega
  apply (sparse_moment_bound hk8 hkM D L).trans
  have hb := pow_le_pow_left₀ (smallCountProbability_nonneg hk8)
    (smallCountProbability_exp hk) (L * D.card)
  have hc := Real.exp_le_exp.mpr hcorrection
  have hmul := mul_le_mul hb hc (le_of_lt (Real.exp_pos _))
    (by positivity : 0 ≤ Real.exp (-(1 : ℝ) / 30) ^ (L * D.card))
  apply hmul.trans_eq
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

end
end SetCover
