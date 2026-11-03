import SetCover.ReplicaOverlap

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def iidMass {ι : Type*} [Fintype ι] (k : ℕ) (x : ι → Bool) : ℝ :=
  ∏ i, matrixBitMass k (x i)

def iidExpectation {ι : Type*} [Fintype ι] (k : ℕ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, iidMass k x * f x

theorem iidMass_sum {ι : Type*} [Fintype ι] (k : ℕ) :
    ∑ x : ι → Bool, iidMass k x = 1 := by
  unfold iidMass
  rw [← Fintype.prod_sum (fun (_ : ι) (b : Bool) => matrixBitMass k b)]
  simp only [matrixBitMass_sum, Finset.prod_const_one]

@[simp] theorem iidExpectation_one {ι : Type*} [Fintype ι] (k : ℕ) :
    iidExpectation (ι := ι) k (fun _ => 1) = 1 := by
  simp [iidExpectation, iidMass_sum]

theorem iidExpectation_mono {ι : Type*} [Fintype ι] {k : ℕ}
    (hk : 8 ≤ k) {f g : (ι → Bool) → ℝ} (h : ∀ x, f x ≤ g x) :
    iidExpectation k f ≤ iidExpectation k g := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left (h x)
  exact Finset.prod_nonneg (fun i _ => matrixBitMass_nonneg hk (x i))

def coordinateReindex {ι κ : Type*} (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun x := fun j => x (e.symm j)
  invFun y := fun i => y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

theorem iidExpectation_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (e : ι ≃ κ) (f : (κ → Bool) → ℝ) :
    iidExpectation k (fun x => f (coordinateReindex e x)) = iidExpectation k f := by
  unfold iidExpectation
  apply Fintype.sum_equiv (coordinateReindex e)
  intro x
  congr 1
  unfold iidMass
  apply Fintype.prod_equiv e
  intro i
  simp [coordinateReindex]

def partitionRows {ι κ : Type*} (owner : ι → κ) :
    ((a : κ) → {i : ι // owner i = a} → Bool) ≃ (ι → Bool) where
  toFun x i := x (owner i) ⟨i, rfl⟩
  invFun y a i := y i.val
  left_inv x := by
    funext a i
    rcases i with ⟨i, hi⟩
    subst a
    rfl
  right_inv y := rfl

theorem product_partition {ι κ : Type*} [Fintype ι] [Fintype κ]
    (owner : ι → κ) (f : ι → ℝ) :
    (∏ i, f i) = ∏ a : κ, ∏ i : {i : ι // owner i = a}, f i.val := by
  rw [← Fintype.prod_sigma (fun i : Σ a, {i : ι // owner i = a} => f i.2.val)]
  exact (Fintype.prod_equiv (Equiv.sigmaFiberEquiv owner) _ _ (by intro i; rfl)).symm

theorem iidExpectation_partition {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (owner : ι → κ)
    (F : (a : κ) → ({i : ι // owner i = a} → Bool) → ℝ) :
    iidExpectation k (fun x => ∏ a, F a (fun i => x i.val)) =
      ∏ a, iidExpectation k (F a) := by
  unfold iidExpectation
  rw [← (partitionRows owner).sum_comp]
  calc
    (∑ x : (a : κ) → {i : ι // owner i = a} → Bool,
        iidMass k (partitionRows owner x) *
          ∏ a, F a (fun i => partitionRows owner x i.val))
        = ∑ x : (a : κ) → {i : ι // owner i = a} → Bool,
          ∏ a, iidMass k (x a) * F a (x a) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
      have hmass : iidMass k (partitionRows owner x) =
          ∏ a, iidMass k (x a) := by
        unfold iidMass
        rw [product_partition owner]
        apply Finset.prod_congr rfl
        intro a _
        apply Finset.prod_congr rfl
        intro i _
        rcases i with ⟨i, hi⟩
        subst a
        rfl
      rw [hmass]
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      congr 1
      funext i
      rcases i with ⟨i, hi⟩
      subst a
      rfl
    _ = ∏ a, ∑ x, iidMass k x * F a x := by
      exact (Fintype.prod_sum (fun a x => iidMass k x * F a x)).symm
    _ = _ := by
      congr 1
      funext a
      congr 1
      ext x
      simp

end
end SetCover
