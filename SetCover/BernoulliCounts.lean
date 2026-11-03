import SetCover.ProductMeasure

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def bitSupport {ι : Type*} [Fintype ι] (x : ι → Bool) : Finset ι :=
  univ.filter (fun i => x i = true)

def bitSetEquiv (ι : Type*) [Fintype ι] : (ι → Bool) ≃ Finset ι where
  toFun := bitSupport
  invFun S i := decide (i ∈ S)
  left_inv x := by
    funext i
    simp only [bitSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> rfl
  right_inv S := by
    ext i
    simp [bitSupport]

theorem iidMass_of_set {ι : Type*} [Fintype ι] (k : ℕ) (S : Finset ι) :
    iidMass k ((bitSetEquiv ι).symm S) =
      beta k ^ S.card * q k ^ (Fintype.card ι - S.card) := by
  simp only [iidMass, bitSetEquiv, Equiv.coe_fn_symm_mk, matrixBitMass,
    decide_eq_true_eq]
  rw [Finset.prod_ite]
  have hyes : (univ : Finset ι).filter (fun i => i ∈ S) = S := by ext; simp
  have hno : (univ : Finset ι).filter (fun i => i ∉ S) = univ \ S := by ext; simp
  rw [hyes, hno, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff (Finset.subset_univ S), Finset.card_univ]

theorem sum_finset_card {ι : Type*} [Fintype ι] (f : ℕ → ℝ) :
    (∑ S : Finset ι, f S.card) =
      ∑ c ∈ range (Fintype.card ι + 1), (Nat.choose (Fintype.card ι) c : ℝ) * f c := by
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp only [Finset.sum_powersetCard, Finset.card_univ, nsmul_eq_mul]

theorem iidExpectation_count {ι : Type*} [Fintype ι] (k : ℕ) (f : ℕ → ℝ) :
    iidExpectation k (fun x : ι → Bool => f (bitSupport x).card) =
      ∑ c ∈ range (Fintype.card ι + 1),
        (Nat.choose (Fintype.card ι) c : ℝ) *
          beta k ^ c * q k ^ (Fintype.card ι - c) * f c := by
  unfold iidExpectation
  rw [← (bitSetEquiv ι).symm.sum_comp]
  have hsupport (S : Finset ι) :
      bitSupport ((bitSetEquiv ι).symm S) = S := (bitSetEquiv ι).apply_symm_apply S
  simp_rw [hsupport, iidMass_of_set]
  rw [sum_finset_card (ι := ι)
    (fun c => beta k ^ c * q k ^ (Fintype.card ι - c) * f c)]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem count_cubic_cancellation {k : ℕ} (hk : 8 ≤ k) (a₀ a₁ a₂ a₃ : ℝ) :
    iidExpectation k (fun x : Fin k → Bool =>
      let c := (bitSupport x).card
      bias k c * (a₀ + a₁ * c + a₂ * (c : ℝ)^2 + a₃ * (c : ℝ)^3)) = 0 := by
  change iidExpectation k (fun x : Fin k → Bool =>
    bias k (bitSupport x).card *
      (a₀ + a₁ * (bitSupport x).card + a₂ * ((bitSupport x).card : ℝ)^2 +
        a₃ * ((bitSupport x).card : ℝ)^3)) = 0
  rw [iidExpectation_count (ι := Fin k) k
    (fun c => bias k c * (a₀ + a₁ * c + a₂ * (c : ℝ)^2 + a₃ * (c : ℝ)^3))]
  simp only [Fintype.card_fin]
  have h := binomial_cubic_cancellation hk a₀ a₁ a₂ a₃
  unfold binomialMass at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro c _
  ring

end
end SetCover
