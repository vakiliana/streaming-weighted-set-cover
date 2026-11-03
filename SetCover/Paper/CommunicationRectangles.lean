import SetCover.Paper.CommunicationMass

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def communicationError (k M v : ℕ) : ℝ :=
  lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120)

def communicationRate (k v r s : ℕ) : ℝ :=
  120 / ((effectiveDimension k v : ℝ) * (min r s : ℕ))

theorem communicationError_nonneg (k M v : ℕ) : 0 ≤ communicationError k M v := by
  unfold communicationError lambda
  positivity

theorem communicationRate_nonneg (k v r s : ℕ) : 0 ≤ communicationRate k v r s := by
  unfold communicationRate
  positivity

theorem rectangle_entropy_budget {v r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {R : Finset (Block v r)} {T : Finset (Block v s)}
    (hR : R.Nonempty) (hT : T.Nonempty) :
    entropy (meanDensity R) + entropy (meanDensity T) ≤
      Real.log (1 / (uniformEvent R * uniformEvent T)) / (min r s : ℕ) := by
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  letI : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp hs
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < (min r s : ℕ) := by exact_mod_cast lt_min hr hs
  have hur := uniformEvent_pos hR
  have hut := uniformEvent_pos hT
  have hlogR : 0 ≤ Real.log (1 / uniformEvent R) :=
    Real.log_nonneg ((one_le_div hur).2 (uniformEvent_le_one R))
  have hlogT : 0 ≤ Real.log (1 / uniformEvent T) :=
    Real.log_nonneg ((one_le_div hut).2 (uniformEvent_le_one T))
  have hminr : ((min r s : ℕ) : ℝ) ≤ r := by exact_mod_cast min_le_left r s
  have hmins : ((min r s : ℕ) : ℝ) ≤ s := by exact_mod_cast min_le_right r s
  have hR' : Real.log (1 / uniformEvent R) / r ≤
      Real.log (1 / uniformEvent R) / (min r s : ℕ) :=
    (div_le_div_iff₀ hrR hmR).2 (mul_le_mul_of_nonneg_left hminr hlogR)
  have hT' : Real.log (1 / uniformEvent T) / s ≤
      Real.log (1 / uniformEvent T) / (min r s : ℕ) :=
    (div_le_div_iff₀ hsR hmR).2 (mul_le_mul_of_nonneg_left hmins hlogT)
  have hlog : Real.log (1 / (uniformEvent R * uniformEvent T)) =
      Real.log (1 / uniformEvent R) + Real.log (1 / uniformEvent T) := by
    simp only [one_div, Real.log_inv, Real.log_mul (ne_of_gt hur) (ne_of_gt hut)]
    ring
  have hER := meanDensity_entropy_le hR
  have hET := meanDensity_entropy_le hT
  simp only [Fintype.card_fin] at hER hET
  rw [hlog, add_div]
  linarith

theorem rectangle_bound {v M k r s : ℕ} (hd : 0 < effectiveDimension k v)
    (hr : 0 < r) (hs : 0 < s) {A : CheapMatrix v M} (hA : Good k A)
    (R : Finset (Block v r)) (T : Finset (Block v s)) :
    rectangleMass (noMass v r s) R T *
      (1 - communicationError k M v -
        communicationRate k v r s * Real.log (1 / rectangleMass (noMass v r s) R T))
      ≤ rectangleMass (yesMass k r s A) R T := by
  rw [show noMass v r s = uniformMass from rfl, rectangle_uniform,
    rectangle_yesMass_identity]
  by_cases hR : R.Nonempty
  · by_cases hT : T.Nonempty
    · letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
      letI : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp hs
      have hdR : (0 : ℝ) < effectiveDimension k v := by exact_mod_cast hd
      have hcert := hA.2 (meanDensity R) (meanDensity T)
        (meanDensity_isDensity hR) (meanDensity_isDensity hT)
      have hbudget := mul_le_mul_of_nonneg_left (rectangle_entropy_budget hr hs hR hT)
        (show 0 ≤ 120 / (effectiveDimension k v : ℝ) by positivity)
      have he :
          (120 / (effectiveDimension k v : ℝ)) *
              (Real.log (1 / (uniformEvent R * uniformEvent T)) / (min r s : ℕ)) =
            communicationRate k v r s * Real.log (1 / (uniformEvent R * uniformEvent T)) := by
        unfold communicationRate
        ring
      rw [he] at hbudget
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (uniformEvent_pos hR).le (uniformEvent_pos hT).le)
      change 1 - communicationError k M v -
        communicationRate k v r s * Real.log (1 / (uniformEvent R * uniformEvent T)) ≤ _
      change 1 - communicationError k M v -
        (120 / (effectiveDimension k v : ℝ)) *
          (entropy (meanDensity R) + entropy (meanDensity T)) ≤ _ at hcert
      linarith
    · have hT0 : T = ∅ := not_nonempty_iff_eq_empty.mp hT
      simp [hT0, uniformEvent]
  · have hR0 : R = ∅ := not_nonempty_iff_eq_empty.mp hR
    simp [hR0, uniformEvent]

end
end SetCover.Paper
