import SetCover.Paper.Entropy

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq ι]

def marginalMass (μ : (ι → X) → ℝ) (i : ι) : X → ℝ :=
  pushMass μ (fun x => x i)

def independentMass (μ : ι → X → ℝ) (x : ι → X) : ℝ :=
  ∏ i, μ i (x i)

theorem independentMass_probability {μ : ι → X → ℝ}
    (hμ : ∀ i, IsProbability (μ i)) :
    IsProbability (independentMass μ) := by
  constructor
  · intro x
    exact prod_nonneg fun i _ => (hμ i).1 (x i)
  · unfold independentMass
    rw [← Fintype.prod_sum]
    simp only [fun i => (hμ i).2, prod_const_one]

theorem marginalMass_probability {μ : (ι → X) → ℝ} (hμ : IsProbability μ) (i : ι) :
    IsProbability (marginalMass μ i) :=
  pushMass_probability hμ _

theorem marginalMass_expectation (μ : (ι → X) → ℝ) (i : ι) (g : X → ℝ) :
    expectation (marginalMass μ i) g = expectation μ (fun x => g (x i)) :=
  pushMass_expectation μ _ g

theorem shannon_subadditive {μ : (ι → X) → ℝ} (hμ : IsProbability μ) :
    shannon μ ≤ ∑ i, shannon (marginalMass μ i) := by
  let ν := independentMass (marginalMass μ)
  have hm := marginalMass_probability hμ
  have hs (x : ι → X) (hx : μ x ≠ 0) (i : ι) : marginalMass μ i (x i) ≠ 0 := by
    have hle := le_pushMass hμ.1 (fun z => z i) x
    have hpos : 0 < μ x := lt_of_le_of_ne (hμ.1 x) (Ne.symm hx)
    exact ne_of_gt (hpos.trans_le hle)
  have hν : IsProbability ν := independentMass_probability hm
  have hsupport (x : ι → X) (hx : μ x ≠ 0) : ν x ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => hs x hx i
  have hc := probability_log_compare hμ hν hsupport
  have hp (x : ι → X) :
      μ x * Real.log (ν x) = ∑ i, μ x * Real.log (marginalMass μ i (x i)) := by
    by_cases hx : μ x = 0
    · simp [hx]
    · dsimp [ν, independentMass]
      rw [Real.log_prod _ _ (fun i _ => hs x hx i), mul_sum]
  simp_rw [hp] at hc
  rw [sum_comm] at hc
  have he (i : ι) :
      (∑ x, μ x * Real.log (marginalMass μ i (x i))) =
        ∑ a, marginalMass μ i a * Real.log (marginalMass μ i a) :=
    (marginalMass_expectation μ i (fun a => Real.log (marginalMass μ i a))).symm
  simp_rw [he] at hc
  simpa only [shannon, sum_neg_distrib] using neg_le_neg hc

theorem average_average_comm {Y : Type*} [Fintype Y] (f : X → Y → ℝ) :
    average (fun x => average (f x)) = average (fun y => average (fun x => f x y)) := by
  simp only [average, ← sum_div, div_div]
  rw [sum_comm, mul_comm]

omit [DecidableEq ι] in
theorem average_isDensity [Nonempty ι] [Nonempty X] {f : ι → X → ℝ}
    (hf : ∀ i, IsDensity (f i)) :
    IsDensity (fun x => average (fun i => f i x)) := by
  constructor
  · intro x
    exact average_nonneg fun i => (hf i).1 x
  · rw [average_average_comm]
    simp only [fun i => (hf i).2, average_const]

omit [DecidableEq ι] in
theorem entropy_average_le [Nonempty ι] [Nonempty X] {f : ι → X → ℝ}
    (hf : ∀ i x, 0 ≤ f i x) :
    entropy (fun x => average (fun i => f i x)) ≤ average (fun i => entropy (f i)) := by
  have hp (x : X) :
      average (fun i => f i x) * Real.log (average (fun i => f i x)) ≤
        average (fun i => f i x * Real.log (f i x)) := by
    have h := Real.convexOn_mul_log.map_sum_le
      (t := (univ : Finset ι)) (w := fun _ => 1 / (Fintype.card ι : ℝ))
      (p := fun i => f i x)
      (fun _ _ => by positivity)
      (by simp [ne_of_gt (card_pos (Ω := ι))])
      (fun i _ => hf i x)
    simpa [average, smul_eq_mul, ← mul_sum, ← sum_mul, div_eq_mul_inv, mul_comm] using h
  exact (average_mono hp).trans_eq (average_average_comm _)

def conditionalDensity (R : Finset (ι → X)) (i : ι) : X → ℝ :=
  massDensity (marginalMass (uniformOnMass R) i)

def meanDensity (R : Finset (ι → X)) (x : X) : ℝ :=
  average (fun i => conditionalDensity R i x)

theorem conditionalDensity_isDensity [Nonempty X] {R : Finset (ι → X)}
    (hR : R.Nonempty) (i : ι) : IsDensity (conditionalDensity R i) :=
  massDensity_isDensity (marginalMass_probability (uniformOnMass_probability hR) i)

theorem meanDensity_isDensity [Nonempty ι] [Nonempty X] {R : Finset (ι → X)}
    (hR : R.Nonempty) : IsDensity (meanDensity R) :=
  average_isDensity (conditionalDensity_isDensity hR)

theorem conditionalDensity_entropy_sum [Nonempty X] {R : Finset (ι → X)}
    (hR : R.Nonempty) :
    (∑ i, entropy (conditionalDensity R i)) ≤
      Real.log (Fintype.card (ι → X)) - Real.log R.card := by
  have hμ := uniformOnMass_probability hR
  have hs := shannon_subadditive hμ
  rw [shannon_uniformOnMass hR] at hs
  have he (i : ι) :
      entropy (conditionalDensity R i) =
        Real.log (Fintype.card X) - shannon (marginalMass (uniformOnMass R) i) :=
    entropy_massDensity (marginalMass_probability hμ i)
  simp_rw [he]
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun,
    Nat.cast_pow, Real.log_pow]
  linarith

theorem meanDensity_entropy_le [Nonempty ι] [Nonempty X] {R : Finset (ι → X)}
    (hR : R.Nonempty) :
    entropy (meanDensity R) ≤
      Real.log (1 / uniformEvent R) / Fintype.card ι := by
  have hN : (Fintype.card (ι → X) : ℝ) ≠ 0 := ne_of_gt (card_pos (Ω := ι → X))
  have hR0 : (R.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hR.card_pos
  have he : Real.log (1 / uniformEvent R) =
      Real.log (Fintype.card (ι → X)) - Real.log R.card := by
    rw [one_div, Real.log_inv, uniformEvent, Real.log_div hR0 hN]
    ring
  rw [he]
  exact (entropy_average_le (fun i x => (conditionalDensity_isDensity hR i).1 x)).trans
    (div_le_div_of_nonneg_right (conditionalDensity_entropy_sum hR)
      (Nat.cast_nonneg (Fintype.card ι)))

end
end SetCover.Paper
