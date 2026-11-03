import SetCover.Paper.MainStatement
import SetCover.Paper.StreamingLower

namespace SetCover.Paper

open Filter MeasureTheory

universe u
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem known_main_of_good_gap {k M v : ℕ} {α : ℝ}
    (hk : 4320 ≤ k) (hp : ParameterBudget k M v) (hα : 1 ≤ α)
    (hε : lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120) ≤ 1 / 12)
    (hfamily : ∃ A : CheapMatrix v M, Good k A ∧
      eventMass (noMass v (M / 2) (M - M / 2))
        (fun x => HasCoverAtMost k A x (3 * α * k)) ≤ 1 / 12) :
    KnownCheapMainConclusion.{u} (1 / 4000000) k M v α := by
  have hM : 4320 ≤ M := hk.trans hp.k_le_M
  have hr : 0 < M / 2 := by omega
  have hs : 0 < M - M / 2 := by omega
  have hv : 0 < v := lt_of_lt_of_le hp.dimension_pos hp.dimension_le_v
  have hbalance : (M : ℝ) ≤ 3 * (min (M / 2) (M - M / 2) : ℕ) := by
    exact_mod_cast (show M ≤ 3 * min (M / 2) (M - M / 2) by omega)
  have hlarge : (4320 : ℝ) ≤ (effectiveDimension k v : ℝ) * M := by
    have hd : 1 ≤ effectiveDimension k v := hp.dimension_pos
    have hmul := Nat.mul_le_mul_right M hd
    have hh : 4320 ≤ effectiveDimension k v * M := by omega
    exact_mod_cast hh
  obtain ⟨A, hA, hbad⟩ := hfamily
  refine ⟨A, hA.1, ?_⟩
  intro p S _hp Ω _ μ _ code hmeas hcorrect
  let codeB := fun ω => thresholdMachine (3 * α * k) (code ω)
  let coins := seedMass μ codeB
  have hcoins : IsProbability coins := seedMass_probability μ codeB hmeas
  have hν₀ := noMass_probability v (M / 2) (M - M / 2)
  have hν₁ := yesMass_probability hp.k_large hp.k_le_M hr hs A
  apply streaming_main_scale_bound hp.k_large hp.k_le_M hv hp.dimension_pos hr hs hA
    hν₀ hν₁
    (fun x hx => yes_support_hasCoverAtMost hp.k_large hp.k_le_M hr hs A x
      (lt_of_le_of_ne (hν₁.1 x) (Ne.symm hx)))
    hbad hε hbalance hlarge coins hcoins
  · intro x hx
    have hopt : (optimum k A x hA.1 : ℝ) ≤ 3 * k :=
      (hasCoverAtMost_iff_optimum_le hA.1 (3 * k)).mp hx
    have hyes := threshold_yes_probability μ code (by linarith : 0 ≤ α) hopt x (hcorrect x)
    change (2 / 3 : ℝ) ≤ machineAcceptance
      (seedMass μ (fun ω => thresholdMachine (3 * α * k) (code ω))) x
    rw [threshold_acceptance μ code (3 * α * k) hmeas x]
    have he : α * (3 * (k : ℝ)) = 3 * α * k := by ring
    simpa only [he] using hyes
  · intro x hx
    have hopt : 3 * α * k < (optimum k A x hA.1 : ℝ) := by
      apply lt_of_not_ge
      intro hh
      exact hx ((hasCoverAtMost_iff_optimum_le hA.1 (3 * α * k)).mpr hh)
    have hno := threshold_no_probability μ code hopt x (hcorrect x)
    exact threshold_acceptance_upper μ code (3 * α * k) hmeas x hno

/-- Theorem `thm:main` of version 17. All distributional, entropy, communication,
streaming-simulation, and asymptotic premises are proved in the imported modules. -/
theorem main_theorem : ManuscriptMainTheorem.{u} := by
  refine ⟨10000, 1 / 4000000, by norm_num, by norm_num, ?_⟩
  intro M v α hfamily hsub
  have hp := eventually_parameter_budget (C₀ := 10000) (by norm_num)
    M v α hfamily hsub
  have hg := eventually_balanced_good_gap (C₀ := 10000) (by norm_num)
    M v α hfamily hsub
  filter_upwards [hp, hg, hfamily, eventually_ge_atTop (4320 : ℕ)]
    with k hpk hgk hfk hk
  have hknown := known_main_of_good_gap.{u} hk hpk hfk.1 hgk.1 hgk.2
  have hs : 0 < M k - M k / 2 := by
    have := hpk.k_le_M
    omega
  exact full_conclusion_of_known hs hknown

end
end SetCover.Paper
