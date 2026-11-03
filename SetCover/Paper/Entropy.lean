import SetCover.Paper.Basic

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem uniformMass_probability [Nonempty X] :
    IsProbability (uniformMass : X → ℝ) := by
  constructor
  · intro x
    unfold uniformMass
    positivity
  · simp [uniformMass, ne_of_gt (card_pos (Ω := X))]

theorem expectation_uniform (f : X → ℝ) :
    expectation uniformMass f = average f := by
  simp [expectation, uniformMass, average, div_eq_mul_inv, mul_comm, sum_mul]

def pushMass (μ : X → ℝ) (f : X → Y) (y : Y) : ℝ :=
  ∑ x, if f x = y then μ x else 0

theorem pushMass_expectation (μ : X → ℝ) (f : X → Y) (g : Y → ℝ) :
    expectation (pushMass μ f) g = expectation μ (fun x => g (f x)) := by
  unfold expectation pushMass
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

theorem pushMass_probability {μ : X → ℝ} (hμ : IsProbability μ) (f : X → Y) :
    IsProbability (pushMass μ f) := by
  constructor
  · intro y
    apply sum_nonneg
    intro x _
    split_ifs
    · exact hμ.1 x
    · exact le_rfl
  · have h := pushMass_expectation μ f (fun _ => 1)
    simpa [expectation, hμ.2] using h

omit [Fintype Y] in
theorem le_pushMass {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) (f : X → Y) (x : X) :
    μ x ≤ pushMass μ f (f x) := by
  unfold pushMass
  calc
    μ x = if f x = f x then μ x else 0 := by simp
    _ ≤ ∑ z, if f z = f x then μ z else 0 := by
      apply single_le_sum (f := fun z => if f z = f x then μ z else 0) _ (mem_univ x)
      intro z _
      dsimp only
      split_ifs
      · exact hμ z
      · exact le_rfl

def shannon (μ : X → ℝ) : ℝ := -(∑ x, μ x * Real.log (μ x))

def massDensity (μ : X → ℝ) (x : X) : ℝ := Fintype.card X * μ x

theorem massDensity_isDensity [Nonempty X] {μ : X → ℝ} (hμ : IsProbability μ) :
    IsDensity (massDensity μ) := by
  refine ⟨fun x => mul_nonneg (Nat.cast_nonneg _) (hμ.1 x), ?_⟩
  simp [massDensity, average, ← mul_sum, hμ.2, ne_of_gt (card_pos (Ω := X))]

theorem entropy_massDensity [Nonempty X] {μ : X → ℝ} (hμ : IsProbability μ) :
    entropy (massDensity μ) = Real.log (Fintype.card X) - shannon μ := by
  have hN : (Fintype.card X : ℝ) ≠ 0 := ne_of_gt (card_pos (Ω := X))
  have hpoint (x : X) :
      massDensity μ x * Real.log (massDensity μ x) =
        Fintype.card X * (μ x * Real.log (Fintype.card X) + μ x * Real.log (μ x)) := by
    by_cases hx : μ x = 0
    · simp [massDensity, hx]
    · rw [massDensity, Real.log_mul hN hx]
      ring
  simp_rw [entropy, hpoint]
  rw [average_mul]
  simp only [average, sum_add_distrib, ← sum_mul, hμ.2, one_mul, shannon]
  field_simp

theorem shannon_le_log_card [Nonempty X] {μ : X → ℝ} (hμ : IsProbability μ) :
    shannon μ ≤ Real.log (Fintype.card X) := by
  have h := entropy_nonneg (massDensity_isDensity hμ)
  rw [entropy_massDensity hμ] at h
  linarith

theorem mul_log_compare {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : a ≠ 0 → b ≠ 0) :
    a * Real.log b ≤ a * Real.log a + b - a := by
  by_cases ha0 : a = 0
  · simp [ha0, hb]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb0 := hs ha0
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have h := Real.log_le_sub_one_of_pos (div_pos hb' ha')
    rw [Real.log_div hb0 ha0] at h
    have hm := mul_le_mul_of_nonneg_left h ha
    have he : a * (b / a - 1) = b - a := by field_simp
    rw [he] at hm
    nlinarith

theorem probability_log_compare {μ ν : X → ℝ}
    (hμ : IsProbability μ) (hν : IsProbability ν)
    (hs : ∀ x, μ x ≠ 0 → ν x ≠ 0) :
    (∑ x, μ x * Real.log (ν x)) ≤ ∑ x, μ x * Real.log (μ x) := by
  have h := sum_le_sum fun x (_ : x ∈ (univ : Finset X)) =>
    mul_log_compare (hμ.1 x) (hν.1 x) (hs x)
  simpa only [sum_sub_distrib, sum_add_distrib, hμ.2, hν.2, add_sub_cancel_right]
    using h

def uniformOnMass (R : Finset X) (x : X) : ℝ :=
  if x ∈ R then 1 / R.card else 0

theorem uniformOnMass_probability {R : Finset X} (hR : R.Nonempty) :
    IsProbability (uniformOnMass R) := by
  have hcard : (R.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hR.card_pos
  constructor
  · intro x
    unfold uniformOnMass
    split_ifs <;> positivity
  · simp [uniformOnMass, hcard]

theorem shannon_uniformOnMass {R : Finset X} (hR : R.Nonempty) :
    shannon (uniformOnMass R) = Real.log R.card := by
  have hcard : (R.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hR.card_pos
  have hp (x : X) :
      uniformOnMass R x * Real.log (uniformOnMass R x) =
        if x ∈ R then (1 / (R.card : ℝ)) * Real.log (1 / (R.card : ℝ)) else 0 := by
    by_cases hx : x ∈ R <;> simp [uniformOnMass, hx]
  simp_rw [shannon, hp]
  simp [Real.log_div, hcard]

def uniformEvent (R : Finset X) : ℝ := R.card / Fintype.card X

theorem uniformEvent_pos [Nonempty X] {R : Finset X} (hR : R.Nonempty) :
    0 < uniformEvent R := by
  unfold uniformEvent
  exact div_pos (by exact_mod_cast hR.card_pos) (card_pos (Ω := X))

theorem uniformEvent_le_one [Nonempty X] (R : Finset X) :
    uniformEvent R ≤ 1 := by
  unfold uniformEvent
  exact (div_le_one (card_pos (Ω := X))).2 (by exact_mod_cast R.card_le_univ)

theorem eventMass_uniform (R : Finset X) :
    eventMass uniformMass (fun x => x ∈ R) = uniformEvent R := by
  simp [eventMass, uniformMass, uniformEvent, div_eq_mul_inv]

theorem uniformEvent_mul_uniformOnMass [Nonempty X] (R : Finset X) (x : X) :
    uniformEvent R * uniformOnMass R x = if x ∈ R then uniformMass x else 0 := by
  by_cases hx : x ∈ R
  · have hcard : (R.card : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Finset.card_pos.mpr ⟨x, hx⟩)
    simp only [uniformEvent, uniformOnMass, uniformMass, if_pos hx]
    field_simp
    ring
  · simp [uniformOnMass, hx]

end
end SetCover.Paper
