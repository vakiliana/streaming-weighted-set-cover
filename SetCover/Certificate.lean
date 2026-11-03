import SetCover.Fourier

/-!
The deterministic implication in Appendix A.3.  The two Fourier estimates are
explicit hypotheses here, not a proof of their probability under the matrix sampler.
-/

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section

def degree {v : ℕ} (t : Cube v) : ℕ := (univ.filter fun i => t i = true).card

def shortMass {v : ℕ} (μ : Cube v → ℝ) (d : ℕ) : ℝ :=
  ∑ t, if t ≠ zeroVector ∧ degree t < d then |noiseFourier μ t| else 0

def FourierBounds {v : ℕ} (μ : Cube v → ℝ) (d : ℕ) (lam η : ℝ) : Prop :=
  shortMass μ d ≤ lam ∧ ∀ t, d ≤ degree t → |noiseFourier μ t| ≤ η

theorem fourier_abs_le_one {v : ℕ} {f : Cube v → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hm : average f ≤ 1) (t : Cube v) :
    |fourier f t| ≤ 1 := by
  have h := fourier_abs_le f t
  simp_rw [abs_of_nonneg (hf _)] at h
  exact h.trans hm

theorem fourier_product_sum_le {v : ℕ} {f g : Cube v → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hf : average (fun x => f x ^ 2) ≤ L)
    (hg : average (fun x => g x ^ 2) ≤ L) :
    (∑ t, |fourier f t| * |fourier g t|) ≤ L := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ)
    (univ : Finset (Cube v)) (fun t => |fourier f t|) (fun t => |fourier g t|)
  simp only [sq_abs] at hcs
  have hpf : (∑ t, fourier f t ^ 2) = average (fun x => f x ^ 2) := by
    simpa [pow_two] using fourier_parseval f f
  have hpg : (∑ t, fourier g t ^ 2) = average (fun x => g x ^ 2) := by
    simpa [pow_two] using fourier_parseval g g
  rw [hpf, hpg] at hcs
  have hmul := mul_le_mul hf hg (average_nonneg fun x => sq_nonneg (g x)) hL
  have hsum : 0 ≤ ∑ t, |fourier f t| * |fourier g t| :=
    sum_nonneg fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

theorem bounded_pairing_lower {v d : ℕ} {μ f g : Cube v → ℝ}
    {lam η L : ℝ} (hμ : IsProbability μ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hb : FourierBounds μ d lam η)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfm : average f ≤ 1) (hgm : average g ≤ 1)
    (hf2 : average (fun x => f x ^ 2) ≤ L)
    (hg2 : average (fun x => g x ^ 2) ≤ L) :
    average f * average g - lam - η * L ≤ pairing μ f g := by
  classical
  let term := fun t => fourier f t * fourier g t *
    character t oneVector * noiseFourier μ t
  let penalty := fun t =>
    if t ≠ zeroVector ∧ degree t < d then |noiseFourier μ t| else 0
  let energy := fun t => |fourier f t| * |fourier g t|
  have he (t : Cube v) : 0 ≤ energy t := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hp (t : Cube v) : 0 ≤ penalty t := by
    dsimp [penalty]
    split_ifs <;> positivity
  have hpoint (t : Cube v) :
      (if t = zeroVector then average f * average g else 0) -
        penalty t - η * energy t ≤ term t := by
    by_cases hz : t = zeroVector
    · subst t
      simp only [term, fourier_zero, character_zero, noiseFourier_zero hμ,
        mul_one, if_pos rfl, ite_true]
      have hpen := hp (zeroVector : Cube v)
      have henergy := mul_nonneg hη (he (zeroVector : Cube v))
      linarith
    · have hterm : |term t| = energy t * |noiseFourier μ t| := by
        simp only [term, energy, abs_mul, abs_character, mul_one]
      have habs : |term t| ≤ penalty t + η * energy t := by
        by_cases hd : degree t < d
        · have hef := fourier_abs_le_one hf hfm t
          have heg := fourier_abs_le_one hg hgm t
          have he1 : energy t ≤ 1 := by
            simpa [energy] using
              mul_le_mul hef heg (abs_nonneg (fourier g t)) (by norm_num : (0 : ℝ) ≤ 1)
          have hsmall := mul_le_mul_of_nonneg_right he1 (abs_nonneg (noiseFourier μ t))
          rw [hterm]
          simp only [penalty, if_pos (show t ≠ zeroVector ∧ degree t < d from ⟨hz, hd⟩)]
          nlinarith [mul_nonneg hη (he t)]
        · have hlarge := mul_le_mul_of_nonneg_left (hb.2 t (le_of_not_gt hd)) (he t)
          rw [hterm]
          simp only [penalty, if_neg (by tauto : ¬ (t ≠ zeroVector ∧ degree t < d))]
          linarith
      rw [if_neg hz]
      have hneg := neg_abs_le (term t)
      linarith
  have hs := sum_le_sum fun t (_ : t ∈ (univ : Finset (Cube v))) => hpoint t
  simp only [sum_sub_distrib, ← mul_sum] at hs
  have hzsum : (∑ t : Cube v, if t = zeroVector then average f * average g else 0) =
      average f * average g := by simp
  rw [hzsum] at hs
  have hpenalty : (∑ t, penalty t) ≤ lam := hb.1
  have henergy : (∑ t, energy t) ≤ L := fourier_product_sum_le hL hf2 hg2
  have hηenergy := mul_le_mul_of_nonneg_left henergy hη
  rw [pairing_fourier]
  change average f * average g - lam - η * L ≤ ∑ t, term t
  linarith

theorem pairing_truncate_le {v : ℕ} {μ f g : Cube v → ℝ} {L : ℝ}
    (hμ : IsProbability μ) (hL : 0 ≤ L)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    pairing μ (truncate L f) (truncate L g) ≤ pairing μ f g := by
  apply average_mono
  intro x
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (hμ.1 z)
  exact mul_le_mul (min_le_left _ _) (min_le_left _ _)
    (le_min (hg _) hL) (hf _)

theorem certificate_of_fourier_bounds {v d : ℕ} {μ f g : Cube v → ℝ}
    {lam η L : ℝ} (hμ : IsProbability μ) (hη : 0 ≤ η) (hL : 1 < L)
    (hb : FourierBounds μ d lam η) (hf : IsDensity f) (hg : IsDensity g) :
    1 - lam - η * L - (entropy f + entropy g) / Real.log L ≤ pairing μ f g := by
  have hL0 : 0 ≤ L := by linarith
  have hfm := truncate_average_bounds hL hf
  have hgm := truncate_average_bounds hL hg
  have hfl := truncate_lost_mass hL hf
  have hgl := truncate_lost_mass hL hg
  have hprod := mul_nonneg (sub_nonneg.mpr hfm.2) (sub_nonneg.mpr hgm.2)
  have hlower : 1 - (entropy f + entropy g) / Real.log L ≤
      average (truncate L f) * average (truncate L g) := by
    rw [add_div]
    nlinarith
  have hbnd := bounded_pairing_lower hμ hη hL0 hb
    (fun x => le_min (hf.1 x) hL0) (fun x => le_min (hg.1 x) hL0)
    hfm.2 hgm.2 (truncate_second_moment hL hf) (truncate_second_moment hL hg)
  have hmono := pairing_truncate_le hμ hL0 hf.1 hg.1
  change average (truncate L f) * average (truncate L g) - lam - η * L ≤
    pairing μ (truncate L f) (truncate L g) at hbnd
  linarith

/-- Exactly the numerical density inequality in Lemma 2.2, conditional on Appendix A.2's
two Fourier bounds.  This theorem does not assert those bounds hold with
probability 9/10 for the manuscript's random matrix. -/
theorem certificate_exp_constants {v d : ℕ} {μ f g : Cube v → ℝ}
    {lam : ℝ} (hd : 0 < d) (hμ : IsProbability μ)
    (hb : FourierBounds μ d lam (Real.exp (-(d : ℝ) / 60)))
    (hf : IsDensity f) (hg : IsDensity g) :
    1 - (lam + Real.exp (-(d : ℝ) / 120)) -
      (120 / (d : ℝ)) * (entropy f + entropy g) ≤ pairing μ f g := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL : 1 < Real.exp ((d : ℝ) / 120) := by
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have h := certificate_of_fourier_bounds hμ
    (le_of_lt (Real.exp_pos _)) hL hb hf hg
  rw [Real.log_exp, ← Real.exp_add] at h
  have he : -(d : ℝ) / 60 + (d : ℝ) / 120 = -(d : ℝ) / 120 := by ring
  rw [he] at h
  have hr : (entropy f + entropy g) / ((d : ℝ) / 120) =
      (120 / (d : ℝ)) * (entropy f + entropy g) := by
    field_simp
    ring
  rw [hr] at h
  linarith

end
end SetCover
