import SetCover.Paper.Randomness

namespace SetCover.Paper

open scoped BigOperators
open Finset MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem expectation_const_law {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ}
    (hμ : IsProbability μ) (c : ℝ) : expectation μ (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul, hμ.2]

theorem expectation_mono_law {Ω : Type*} [Fintype Ω] {μ f g : Ω → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hfg : ∀ x, f x ≤ g x) :
    expectation μ f ≤ expectation μ g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hfg x) (hμ x)

theorem expectation_add_law {Ω : Type*} [Fintype Ω] (μ f g : Ω → ℝ) :
    expectation μ (fun x => f x + g x) = expectation μ f + expectation μ g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem acceptance_gap_from_correctness {Ω : Type*} [Fintype Ω]
    {ν₀ ν₁ a : Ω → ℝ} (hν₀ : IsProbability ν₀) (hν₁ : IsProbability ν₁)
    {yes bad : Ω → Prop}
    (hyesSupport : ∀ x, ν₁ x ≠ 0 → yes x)
    (hyes : ∀ x, yes x → (2 / 3 : ℝ) ≤ a x)
    (hno : ∀ x, ¬ bad x → a x ≤ (1 / 3 : ℝ))
    (ha : ∀ x, a x ≤ 1) (hbad : eventMass ν₀ bad ≤ (1 / 12 : ℝ)) :
    (1 / 4 : ℝ) ≤ expectation ν₁ a - expectation ν₀ a := by
  have hlower : (2 / 3 : ℝ) ≤ expectation ν₁ a := by
    rw [← expectation_const_law hν₁ (2 / 3)]
    apply Finset.sum_le_sum
    intro x _
    by_cases hz : ν₁ x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hyes x (hyesSupport x hz)) (hν₁.1 x)
  have hpoint (x : Ω) : a x ≤ (1 / 3 : ℝ) + (if bad x then 1 else 0) := by
    by_cases hb : bad x
    · rw [if_pos hb]
      have h := ha x
      linarith
    · simpa [hb] using hno x hb
  have hupper := expectation_mono_law hν₀.1 hpoint
  rw [expectation_add_law, expectation_const_law hν₀,
    ← eventMass_eq_expectation] at hupper
  linarith

theorem threshold_yes_probability {Ω : Type*} [MeasurableSpace Ω]
    {p S v r s : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → StreamingMachine p S v r s ℝ) {α low opt : ℝ}
    (hα : 0 ≤ α) (hopt : opt ≤ low) (x : Input v r s)
    (hsuccess : (2 / 3 : ℝ) ≤
      μ.real {ω | opt ≤ (code ω).run x ∧ (code ω).run x ≤ α * opt}) :
    (2 / 3 : ℝ) ≤ μ.real {ω | (code ω).run x ≤ α * low} := by
  apply hsuccess.trans
  refine measureReal_mono ?_ (by finiteness)
  intro ω hω
  exact hω.2.trans (mul_le_mul_of_nonneg_left hopt hα)

theorem threshold_no_probability {Ω : Type*} [MeasurableSpace Ω]
    {p S v r s : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → StreamingMachine p S v r s ℝ) {α T opt : ℝ}
    (hopt : T < opt) (x : Input v r s)
    (hsuccess : (2 / 3 : ℝ) ≤
      μ.real {ω | opt ≤ (code ω).run x ∧ (code ω).run x ≤ α * opt}) :
    (2 / 3 : ℝ) ≤ μ.real {ω | ¬ (code ω).run x ≤ T} := by
  apply hsuccess.trans
  refine measureReal_mono ?_ (by finiteness)
  intro ω hω
  exact not_le.mpr (hopt.trans_le hω.1)

theorem threshold_acceptance_upper {Ω : Type*} [MeasurableSpace Ω]
    {p S v r s : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → StreamingMachine p S v r s ℝ) (T : ℝ)
    (hcode : SeedMeasurable (fun ω => thresholdMachine T (code ω)))
    (x : Input v r s)
    (hno : (2 / 3 : ℝ) ≤ μ.real {ω | ¬ (code ω).run x ≤ T}) :
    machineAcceptance (seedMass μ (fun ω => thresholdMachine T (code ω))) x ≤ (1 / 3 : ℝ) := by
  have hp := seedMass_probability μ _ hcode
  have hc := eventMass_compl hp (fun m => m.run x = true)
  have he := seedMass_event μ (fun ω => thresholdMachine T (code ω)) hcode
    (fun m => ¬ m.run x = true)
  simp only [thresholdMachine_run, decide_eq_true_eq] at he
  rw [he] at hc
  unfold machineAcceptance
  linarith

/-- This keeps the final answer bit rather than assuming a positive workspace. -/
theorem work_lower_of_communication_gap {d M t b work ε : ℝ}
    (hd : 0 < d) (ht : 0 < t) (hb : 0 ≤ b)
    (hε : ε ≤ 1 / 12) (hbalance : M ≤ 3 * t)
    (hlarge : 4320 ≤ d * M) (hcost : b ≤ 2 * work + 1)
    (hgap : 1 / 4 ≤ ε + 120 * b * Real.log 2 / (d * t)) :
    d * M / 8640 ≤ work := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hratio : (1 / 6 : ℝ) ≤ 120 * b * Real.log 2 / (d * t) := by linarith
  have hscaled := (le_div_iff₀ (mul_pos hd ht)).mp hratio
  have hnum := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 120 * b by positivity)
  have hbal := mul_le_mul_of_nonneg_left hbalance (le_of_lt hd)
  have hbound : d * M ≤ 2160 * b := by nlinarith
  nlinarith

theorem work_lower_main_scale {k M v : ℕ} {work : ℝ}
    (hv : 0 < v) (hd : 0 < effectiveDimension k v) (hw : 0 ≤ work)
    (hwork : (effectiveDimension k v : ℝ) * M / 8640 ≤ work) :
    (1 / 4000000 : ℝ) * ((2 * M : ℕ) : ℝ) * (k : ℝ)^2 /
      ((2 * v : ℕ) : ℝ) ≤ work := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hdR : (1 : ℝ) ≤ effectiveDimension k v := by exact_mod_cast hd
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hfloor := Nat.lt_floor_add_one ((k : ℝ)^2 / (64 * Real.exp 1 * v))
  change (k : ℝ)^2 / (64 * Real.exp 1 * v) <
    (effectiveDimension k v : ℝ) + 1 at hfloor
  have hdim : (k : ℝ)^2 / (64 * Real.exp 1 * v) ≤
      2 * (effectiveDimension k v : ℝ) := by linarith
  have hnum := (div_le_iff₀ (show 0 < 64 * Real.exp 1 * v by positivity)).mp hdim
  have hE := mul_le_mul_of_nonneg_right (le_of_lt he)
    (show 0 ≤ 128 * (v : ℝ) * effectiveDimension k v by positivity)
  have hcore : (k : ℝ)^2 ≤ 384 * v * effectiveDimension k v := by nlinarith
  have hM := mul_le_mul_of_nonneg_left hcore (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hW := mul_le_mul_of_nonneg_left hwork (show 0 ≤ 3317760 * (v : ℝ) by positivity)
  have htotal : (M : ℝ) * (k : ℝ)^2 ≤ 4000000 * v * work := by
    nlinarith [mul_nonneg (le_of_lt hvR) hw]
  push_cast
  apply (div_le_iff₀ (show 0 < 2 * (v : ℝ) by positivity)).mpr
  nlinarith

end
end SetCover.Paper
