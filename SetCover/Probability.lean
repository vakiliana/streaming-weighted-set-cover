import SetCover.Statement

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

def expectation {Ω : Type*} [Fintype Ω] (μ f : Ω → ℝ) : ℝ :=
  ∑ x, μ x * f x

theorem eventMass_eq_expectation {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (P : Ω → Prop) :
    eventMass μ P = expectation μ (fun x => if P x then 1 else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> simp [hp]

theorem eventMass_compl {Ω : Type*} [Fintype Ω]
    {μ : Ω → ℝ} (hμ : IsProbability μ) (P : Ω → Prop) :
    eventMass μ (fun x => ¬ P x) = 1 - eventMass μ P := by
  classical
  have h : eventMass μ P + eventMass μ (fun x => ¬ P x) = 1 := by
    rw [eventMass, eventMass, ← Finset.sum_add_distrib, ← hμ.2]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : P x <;> simp [hp]
  linarith

theorem eventMass_union_le {Ω : Type*} [Fintype Ω]
    {μ : Ω → ℝ} (hμ : ∀ x, 0 ≤ μ x) (P Q : Ω → Prop) :
    eventMass μ (fun x => P x ∨ Q x) ≤ eventMass μ P + eventMass μ Q := by
  classical
  rw [eventMass, eventMass, eventMass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq, hμ x]

theorem eventMass_exists_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    {μ : Ω → ℝ} (hμ : ∀ x, 0 ≤ μ x) (P : ι → Ω → Prop) :
    eventMass μ (fun x => ∃ i, P i x) ≤ ∑ i, eventMass μ (P i) := by
  classical
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ i, P i x
  · rw [if_pos hx]
    obtain ⟨i, hi⟩ := hx
    calc
      μ x = if P i x then μ x else 0 := (if_pos hi).symm
      _ ≤ ∑ j, if P j x then μ x else 0 := by
        apply Finset.single_le_sum _ (Finset.mem_univ i)
        intro j _
        split_ifs
        · exact hμ x
        · exact le_rfl
  · rw [if_neg hx]
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hμ x
    · exact le_rfl

theorem finite_markov {Ω : Type*} [Fintype Ω]
    {μ F : Ω → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x)
    {a : ℝ} (ha : 0 < a) :
    eventMass μ (fun x => a < F x) ≤ expectation μ F / a := by
  classical
  apply (le_div_iff₀ ha).2
  unfold eventMass expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : a < F x
  · rw [if_pos hx]
    exact mul_le_mul_of_nonneg_left (le_of_lt hx) (hμ x)
  · rw [if_neg hx, zero_mul]
    exact mul_nonneg (hμ x) (hF x)

def rowMass {M : ℕ} (k : ℕ) (row : Fin M → Bool) : ℝ :=
  ∏ j, matrixBitMass k (row j)

theorem rowMass_sum {M : ℕ} (k : ℕ) :
    ∑ row : Fin M → Bool, rowMass k row = 1 := by
  unfold rowMass
  rw [← Fintype.prod_sum (fun (_ : Fin M) (b : Bool) => matrixBitMass k b)]
  simp only [matrixBitMass_sum, Finset.prod_const_one]

theorem matrix_row_expectation {v M : ℕ} (k : ℕ) (e : Fin v)
    (F : (Fin M → Bool) → ℝ) :
    expectation (matrixMass k) (fun A : CheapMatrix v M => F (A e)) =
      expectation (rowMass k) F := by
  classical
  calc
    expectation (matrixMass k) (fun A : CheapMatrix v M => F (A e))
        = ∑ A : CheapMatrix v M, ∏ i, rowMass k (A i) *
            (if i = e then F (A i) else 1) := by
          unfold expectation matrixMass rowMass
          apply Finset.sum_congr rfl
          intro A _
          rw [Finset.prod_mul_distrib]
          simp
    _ = ∏ i, ∑ row : Fin M → Bool,
          rowMass k row * (if i = e then F row else 1) := by
            rw [← Fintype.prod_sum (fun (i : Fin v) (row : Fin M → Bool) =>
              rowMass k row * (if i = e then F row else 1))]
    _ = ∏ i : Fin v, if i = e then expectation (rowMass k) F else 1 := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i = e
          · simp [hi, expectation]
          · simp [hi, rowMass_sum]
    _ = expectation (rowMass k) F := by simp

theorem empty_row_probability {v M : ℕ} (k : ℕ) (e : Fin v) :
    eventMass (matrixMass k) (fun A : CheapMatrix v M => A e = zeroVector) = q k ^ M := by
  classical
  let F : (Fin M → Bool) → ℝ := fun row => if row = zeroVector then 1 else 0
  have hm := matrix_row_expectation (v := v) (M := M) k e F
  calc
    eventMass (matrixMass k) (fun A : CheapMatrix v M => A e = zeroVector)
        = expectation (matrixMass k) (fun A => F (A e)) := by
          rw [eventMass_eq_expectation]
          congr 1
          funext A
          by_cases h : A e = zeroVector <;> simp [F, h]
    _ = expectation (rowMass k) F := hm
    _ = q k ^ M := by
      simp [expectation, F, rowMass, zeroVector, matrixBitMass]

theorem coverage_failure_le {v M k : ℕ} (hk : 8 ≤ k) :
    eventMass (matrixMass k) (fun A : CheapMatrix v M => ¬ Covers A)
      ≤ (v : ℝ) * q k ^ M := by
  classical
  have heq : (fun A : CheapMatrix v M => ¬ Covers A) =
      (fun A => ∃ e, A e = zeroVector) := by
    funext A
    apply propext
    simp only [Covers, not_forall, not_exists]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, funext fun j => ?_⟩
      simpa [zeroVector, Bool.not_eq_true] using he j
    · rintro ⟨e, he⟩
      refine ⟨e, ?_⟩
      intro j
      have h := congrFun he j
      simpa [zeroVector, Bool.not_eq_true] using h
  rw [heq]
  calc
    eventMass (matrixMass k) (fun A : CheapMatrix v M => ∃ e, A e = zeroVector)
        ≤ ∑ e, eventMass (matrixMass k)
          (fun A : CheapMatrix v M => A e = zeroVector) :=
          eventMass_exists_le (matrixMass_probability hk).1 _
    _ = (v : ℝ) * q k ^ M := by simp [empty_row_probability]

end
end SetCover
