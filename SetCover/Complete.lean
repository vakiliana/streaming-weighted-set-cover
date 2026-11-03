import SetCover.LongMoment
import SetCover.ShortMoment
import SetCover.Concentration

/-! Unconditional verification of manuscript version 17, Lemma 2.2. -/

namespace SetCover

open scoped BigOperators
open Filter

noncomputable section

theorem lemma22_of_parameter_budget {k M v : ℕ}
    (hk : 64 ≤ k) (hkv : k ≤ v) (hlam : lambda k M ≤ 1)
    (hp : ParameterBudget k M v) : Lemma22Conclusion k M v := by
  let d := effectiveDimension k v
  let L := longMomentOrder k v
  have hk20 : 20 ≤ k := by omega
  have hlam0 : lambda k M ≠ 0 := by
    unfold lambda
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by have := hp.k_le_M; omega)
    positivity
  apply lemma22_of_moment_bounds (L := L) hp.k_large hp.k_le_M
    hp.dimension_pos hp.order_pos
    (shortBudget := 100 * lambda k M ^ 2)
    (momentBudget := Real.exp (-(L : ℝ) * d / 40))
  · exact short_moment_bound hk hp.k_le_M hlam hkv
  · intro D
    have hcard : D.val.card = d := D.property
    have hcorrection :
        lambda k M * L * (L - 1 : ℝ) / 2 *
          (((q k)⁻¹) ^ (2 * D.val.card) - 1) ≤ (L : ℝ) * D.val.card / 120 := by
      rw [hcard]
      have hpow : q k ^ (-(2 * (d : ℤ))) = ((q k)⁻¹) ^ (2 * d) := by
        rw [show -(2 * (d : ℤ)) = -((2 * d : ℕ) : ℤ) by push_cast; ring]
        simp only [zpow_neg, zpow_natCast, inv_pow]
      have hc := hp.long_correction
      change lambda k M * L * (L - 1 : ℝ) / 2 *
        (q k ^ (-(2 * (d : ℤ))) - 1) ≤ (L : ℝ) * d / 120 at hc
      rw [hpow] at hc
      exact hc
    have hm := sparse_moment_exponential hk20 hp.k_le_M D.val hcorrection
    simpa only [hcard] using hm
  · have hs : (100 * lambda k M ^ 2) / lambda k M = 100 * lambda k M := by
      field_simp
      ring
    have hc : Fintype.card (CoordinateSubsets v d) = Nat.choose v d := by
      simp [CoordinateSubsets, Fintype.card_finset_len]
    have hl : Real.exp (-(L : ℝ) * d / 40) /
        Real.exp (-(d : ℝ) / 60) ^ L = Real.exp (-(L : ℝ) * d / 120) := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      ring
    change (v : ℝ) * q k ^ M + (100 * lambda k M ^ 2) / lambda k M +
      Fintype.card (CoordinateSubsets v d) *
        (Real.exp (-(L : ℝ) * d / 40) / Real.exp (-(d : ℝ) / 60) ^ L) ≤ (1 / 10 : ℝ)
    rw [hs, hc, hl]
    exact hp.failure_budget

/-- Version 17, Lemma 2.2, including both the actual sampler's support and
the probability-9/10 event uniform over all real densities.
There are no moment, Fourier, or eventual-budget hypotheses in this theorem. -/
theorem manuscript_lemma22 : ManuscriptLemma22 := by
  refine ⟨10000, by norm_num, ?_⟩
  intro M v α hfamily hsub
  have hp := eventually_parameter_budget (C₀ := 10000) (by norm_num) M v α hfamily hsub
  have hb := eventually_basic_parameter_bounds (C₀ := 10000) (by norm_num)
    M v α hfamily hsub
  filter_upwards [hp, hb, eventually_ge_atTop (64 : ℕ)] with k hpk hbk hk
  exact lemma22_of_parameter_budget hk hbk.2.1 hbk.2.2 hpk

end
end SetCover
