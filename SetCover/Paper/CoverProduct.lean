import SetCover.Paper.Basic

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem cover_eventMass_nonneg {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (P : Ω → Prop) : 0 ≤ eventMass μ P := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hμ x
  · exact le_rfl

theorem cover_expectation_mono {Ω : Type*} [Fintype Ω] {μ f g : Ω → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hfg : ∀ x, f x ≤ g x) :
    expectation μ f ≤ expectation μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hμ x)

theorem cover_product_eventMass {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (μ : ι → Ω → ℝ) (P : ι → Ω → Prop) :
    eventMass (fun x : ι → Ω => ∏ i, μ i (x i)) (fun x => ∀ i, P i (x i)) =
      ∏ i, eventMass (μ i) (P i) := by
  unfold eventMass
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ∀ i, P i (x i)
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (h i)]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

def coverBitMass {M r s : ℕ} (k : ℕ) (i : SetId M r s) (b : Bool) : ℝ :=
  match i with
  | Sum.inl _ => matrixBitMass k b
  | Sum.inr _ => 1 / 2

def coverRowMass {M r s : ℕ} (k : ℕ) (row : SetId M r s → Bool) : ℝ :=
  ∏ i, coverBitMass k i (row i)

theorem coverBitMass_nonneg {M r s k : ℕ} (hk : 8 ≤ k)
    (i : SetId M r s) (b : Bool) : 0 ≤ coverBitMass k i b := by
  cases i with
  | inl j => exact matrixBitMass_nonneg hk b
  | inr j => norm_num [coverBitMass]

@[simp] theorem coverBitMass_sum {M r s : ℕ} (k : ℕ) (i : SetId M r s) :
    ∑ b : Bool, coverBitMass k i b = 1 := by
  cases i with
  | inl j => exact matrixBitMass_sum k
  | inr j => norm_num [coverBitMass, Fintype.sum_bool]

theorem coverRowMass_probability {M r s k : ℕ} (hk : 8 ≤ k) :
    IsProbability (coverRowMass (M := M) (r := r) (s := s) k) := by
  constructor
  · intro row
    exact Finset.prod_nonneg fun i _ => coverBitMass_nonneg hk i (row i)
  · unfold coverRowMass
    rw [← Fintype.prod_sum]
    simp only [coverBitMass_sum, Finset.prod_const_one]

/-- A sufficient obstruction: all selected identifiers omit copy `true`. -/
def rowOmission {M r s : ℕ} (F : Finset (SetId M r s))
    (row : SetId M r s → Bool) : Prop :=
  ∀ i ∈ F, row i = false

def omissionProbability {M r s : ℕ} (k : ℕ) (F : Finset (SetId M r s)) : ℝ :=
  ∏ i ∈ F, coverBitMass k i false

theorem rowOmission_probability {M r s : ℕ} (k : ℕ) (F : Finset (SetId M r s)) :
    eventMass (coverRowMass k) (rowOmission F) = omissionProbability k F := by
  trans ∏ i : SetId M r s,
      eventMass (coverBitMass k i) (fun b => i ∈ F → b = false)
  · exact cover_product_eventMass (fun i b => coverBitMass k i b)
      (fun i b => i ∈ F → b = false)
  have hbit (i : SetId M r s) :
      eventMass (coverBitMass k i) (fun b => i ∈ F → b = false) =
        if i ∈ F then coverBitMass k i false else 1 := by
    by_cases hi : i ∈ F
    · simp [eventMass, hi]
    · simpa only [eventMass, hi, false_implies, if_true, if_false] using coverBitMass_sum k i
  simp_rw [hbit]
  simp [omissionProbability, ← Finset.prod_filter]

def coverRowsEquiv (v M r s : ℕ) :
    (CheapMatrix v M × Input v r s) ≃ (Fin v → SetId M r s → Bool) where
  toFun z e i :=
    match i with
    | Sum.inl j => z.1 e j
    | Sum.inr (Sum.inl j) => z.2.1 j e
    | Sum.inr (Sum.inr j) => z.2.2 j e
  invFun y :=
    (fun e j => y e (Sum.inl j),
      (fun j e => y e (Sum.inr (Sum.inl j)), fun j e => y e (Sum.inr (Sum.inr j))))
  left_inv _ := rfl
  right_inv y := by
    funext e i
    cases i with
    | inl j => rfl
    | inr j => cases j <;> rfl

theorem cover_noMass_eq_power {v r s : ℕ} (x : Input v r s) :
    noMass v r s x = (((1 / 2 : ℝ) ^ r) * (1 / 2 : ℝ) ^ s) ^ v := by
  simp [noMass, uniformMass, Input, Block, Cube, Fintype.card_fun,
    mul_pow, ← pow_mul, Nat.mul_comm, mul_comm]

theorem coverRowsEquiv_mass {v M r s : ℕ} (k : ℕ)
    (z : CheapMatrix v M × Input v r s) :
    (∏ e, coverRowMass k (coverRowsEquiv v M r s z e)) =
      matrixMass k z.1 * noMass v r s z.2 := by
  rw [cover_noMass_eq_power]
  simp only [coverRowMass, Fintype.prod_sum_type, coverRowsEquiv,
    Equiv.coe_fn_mk, coverBitMass, Finset.prod_const, Fintype.card_fin]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    pow_add, Finset.prod_const]
  rfl

theorem cover_joint_expectation {v M r s : ℕ} (k : ℕ)
    (f : (Fin v → SetId M r s → Bool) → ℝ) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      expectation (noMass v r s) (fun x => f (coverRowsEquiv v M r s (A, x)))) =
      expectation (fun y => ∏ e, coverRowMass k (y e)) f := by
  unfold expectation
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [← Fintype.sum_prod_type (fun z : CheapMatrix v M × Input v r s =>
    matrixMass k z.1 * noMass v r s z.2 * f (coverRowsEquiv v M r s z))]
  apply Fintype.sum_equiv (coverRowsEquiv v M r s)
  intro z
  rw [coverRowsEquiv_mass]

theorem cover_joint_eventMass {v M r s : ℕ} (k : ℕ)
    (P : (Fin v → SetId M r s → Bool) → Prop) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      eventMass (noMass v r s) (fun x => P (coverRowsEquiv v M r s (A, x)))) =
      eventMass (fun y => ∏ e, coverRowMass k (y e)) P := by
  simpa only [eventMass_eq_expectation] using
    (cover_joint_expectation k (fun y => if P y then 1 else 0))

theorem isCover_no_rowOmission {v M r s : ℕ} {A : CheapMatrix v M}
    {x : Input v r s} {F : Finset (SetId M r s)} (hF : IsCover A x F) :
    ∀ e, ¬ rowOmission F (coverRowsEquiv v M r s (A, x) e) := by
  intro e he
  obtain ⟨i, hi, hc⟩ := hF (e, true)
  have hfalse := he i hi
  cases i with
  | inl j =>
    change A e j = false at hfalse
    change A e j = true at hc
    simp_all
  | inr j =>
    cases j with
    | inl j =>
      change x.1 j e = false at hfalse
      change x.1 j e = true at hc
      simp_all
    | inr j =>
      change x.2 j e = false at hfalse
      change x.2 j e = true at hc
      simp_all

end
end SetCover.Paper
