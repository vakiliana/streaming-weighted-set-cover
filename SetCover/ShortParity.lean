import SetCover.ShortOverlap

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

theorem short_expectation_average {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (μ : Ω → ℝ) (f : ι → Ω → ℝ) :
    expectation μ (fun x => average (fun i => f i x)) =
      average (fun i => expectation μ (f i)) := by
  simp only [expectation, average, ← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem short_average_mul_average {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (f : Ω → ℝ) (g : ι → ℝ) :
    average f * average g = average (fun x => average (fun y => f x * g y)) := by
  simp_rw [average_mul, average_mul_right]

theorem short_matrix_product {v M : ℕ} (k : ℕ)
    (f : Fin v → (Fin M → Bool) → ℝ) :
    expectation (matrixMass k) (fun A : CheapMatrix v M => ∏ e, f e (A e)) =
      ∏ e, expectation (rowMass k) (f e) := by
  simp only [expectation, matrixMass, rowMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (e : Fin v) (row : Fin M → Bool) =>
    (∏ j, matrixBitMass k (row j)) * f e row)).symm

theorem short_noise_second_moment_eq {v M k : ℕ} (t : Cube v) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      noiseFourier (noiseMass k A) t ^ 2) =
      average (fun K : RepairChoices M k => average (fun L : RepairChoices M k =>
        shortRowCorrelation k K.val L.val ^ degree t)) := by
  have hpoint (A : CheapMatrix v M) :
      noiseFourier (noiseMass k A) t ^ 2 =
        average (fun K : RepairChoices M k => average (fun L : RepairChoices M k =>
          ∏ e, if t e then
            bias k (K.val.filter (fun i => A e i = true)).card *
              bias k (L.val.filter (fun i => A e i = true)).card else 1)) := by
    rw [noiseFourier_product, pow_two, short_average_mul_average]
    congr 1
    funext K
    congr 1
    funext L
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    cases t e <;> simp [count]
  simp_rw [hpoint, short_expectation_average]
  congr 1
  funext K
  congr 1
  funext L
  rw [short_matrix_product k (fun e row => if t e then
    bias k (K.val.filter (fun i => row i = true)).card *
      bias k (L.val.filter (fun i => row i = true)).card else 1)]
  have he (e : Fin v) :
      expectation (rowMass k) (fun row => if t e then
        bias k (K.val.filter (fun i => row i = true)).card *
          bias k (L.val.filter (fun i => row i = true)).card else 1) =
      if t e then shortRowCorrelation k K.val L.val else 1 := by
    cases ht : t e
    · simpa only [Bool.false_eq_true, if_false, expectation, mul_one] using rowMass_sum (M := M) k
    · rfl
  simp_rw [he]
  rw [← Finset.prod_filter]
  simp [degree]

theorem short_noise_second_moment_le {v M k : ℕ}
    (hk : 64 ≤ k) (hkM : k ≤ M) (hlam : lambda k M ≤ 1)
    (t : Cube v) (ht : 0 < degree t) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      noiseFourier (noiseMass k A) t ^ 2) ≤
      64 * lambda k M ^ 4 * (4 * (degree t : ℝ) / k) ^ (4 * degree t) := by
  letI := repairChoices_nonempty hkM
  rw [short_noise_second_moment_eq]
  calc
    _ ≤ average (fun _K : RepairChoices M k =>
        64 * lambda k M ^ 4 * (4 * (degree t : ℝ) / k) ^ (4 * degree t)) := by
      apply average_mono
      intro K
      exact short_row_moment_le hk hkM hlam K.val K.property ht
    _ = _ := average_const _

theorem short_expectation_abs_sq_le {Ω : Type*} [Fintype Ω]
    {μ : Ω → ℝ} (hμ : IsProbability μ) (f : Ω → ℝ) :
    expectation μ (fun x => |f x|) ^ 2 ≤ expectation μ (fun x => f x ^ 2) := by
  let c := expectation μ (fun x => |f x|)
  have hnonneg : 0 ≤ ∑ x, μ x * (|f x| - c) ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hμ.1 x) (sq_nonneg _)
  have heq : (∑ x, μ x * (|f x| - c) ^ 2) =
      expectation μ (fun x => f x ^ 2) - c ^ 2 := by
    calc
      _ = ∑ x, (μ x * f x ^ 2 - 2 * c * (μ x * |f x|) + c ^ 2 * μ x) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [sub_sq, sq_abs]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hμ.2, mul_one]
        change expectation μ (fun x => f x ^ 2) - 2 * c * c + c ^ 2 = _
        ring
  rw [heq] at hnonneg
  exact sub_nonneg.mp hnonneg

theorem short_parity_expectation_le {v M k : ℕ}
    (hk : 64 ≤ k) (hkM : k ≤ M) (hlam : lambda k M ≤ 1)
    (t : Cube v) (ht : 0 < degree t) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      |noiseFourier (noiseMass k A) t|) ≤
      8 * lambda k M ^ 2 * (4 * (degree t : ℝ) / k) ^ (2 * degree t) := by
  have hcs := short_expectation_abs_sq_le
    (matrixMass_probability (v := v) (M := M) (show 8 ≤ k by omega))
    (fun A : CheapMatrix v M => noiseFourier (noiseMass k A) t)
  have hsecond := short_noise_second_moment_le hk hkM hlam t ht
  have hp :
      ((4 * (degree t : ℝ) / k) ^ (2 * degree t)) ^ 2 =
        (4 * (degree t : ℝ) / k) ^ (4 * degree t) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsquare :
      (8 * lambda k M ^ 2 * (4 * (degree t : ℝ) / k) ^ (2 * degree t)) ^ 2 =
        64 * lambda k M ^ 4 * (4 * (degree t : ℝ) / k) ^ (4 * degree t) := by
    rw [mul_pow, hp]
    ring
  have hrhs : 0 ≤ 8 * lambda k M ^ 2 * (4 * (degree t : ℝ) / k) ^ (2 * degree t) := by
    positivity
  nlinarith

end
end SetCover
