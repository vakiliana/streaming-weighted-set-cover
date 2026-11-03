import SetCover.Paper.CoverNoBounds
import SetCover.Paper.CoverYes

namespace SetCover.Paper

open scoped BigOperators
open Finset Filter

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem no_gap_decay_le_one_over_120 {k M : ℕ} {α : ℝ}
    (hk : 40 ≤ k) (hM : 1 ≤ M) (hα : 1 ≤ α) :
    Real.exp (-3 * α * k * Real.log (2 * (M : ℝ) + 1)) ≤ 1 / 120 := by
  have hkR : (40 : ℝ) ≤ k := by exact_mod_cast hk
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 1 ≤ Real.log (2 * (M : ℝ) + 1) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    linarith [Real.exp_one_lt_d9]
  have hα0 : 0 ≤ α := by linarith
  have hαk : 3 * (k : ℝ) ≤ 3 * α * k := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ 3 * α * (k : ℝ))
  have hlarge : 120 ≤ Real.exp (3 * α * k * Real.log (2 * (M : ℝ) + 1)) := by
    linarith [Real.add_one_le_exp (3 * α * k * Real.log (2 * (M : ℝ) + 1))]
  rw [show -3 * α * k * Real.log (2 * (M : ℝ) + 1) =
    -(3 * α * k * Real.log (2 * (M : ℝ) + 1)) by ring,
    Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem good_gap_probability_of_bounds {v M r s k : ℕ} {α : ℝ}
    (hk : 8 ≤ k)
    (hgood : (9 / 10 : ℝ) ≤ eventMass (matrixMass k) (Good (v := v) (M := M) k))
    (hmean : expectation (matrixMass k) (fun A : CheapMatrix v M =>
      eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k))) ≤ 1 / 120) :
    (4 / 5 : ℝ) ≤ eventMass (matrixMass k) (fun A : CheapMatrix v M =>
      Good k A ∧
        eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k)) ≤ 1 / 12) := by
  let F : CheapMatrix v M → ℝ := fun A =>
    eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k))
  have hμ := (matrixMass_probability (v := v) (M := M) hk).1
  have hF : ∀ A, 0 ≤ F A := by
    intro A
    apply cover_eventMass_nonneg
    intro x
    unfold noMass uniformMass
    positivity
  have hmarkov : eventMass (matrixMass k) (fun A => (1 / 12 : ℝ) < F A) ≤ 1 / 10 := by
    calc
      eventMass (matrixMass k) (fun A => (1 / 12 : ℝ) < F A) ≤
          expectation (matrixMass k) F / (1 / 12) :=
        finite_markov hμ hF (by norm_num)
      _ ≤ (1 / 120 : ℝ) / (1 / 12) :=
        div_le_div_of_nonneg_right hmean (by norm_num)
      _ = 1 / 10 := by norm_num
  have hsplit : eventMass (matrixMass k) (Good (v := v) (M := M) k) ≤
      eventMass (matrixMass k) (fun A => Good k A ∧ F A ≤ 1 / 12) +
        eventMass (matrixMass k) (fun A => (1 / 12 : ℝ) < F A) := by
    calc
      eventMass (matrixMass k) (Good (v := v) (M := M) k) ≤
          eventMass (matrixMass k) (fun A =>
            (Good k A ∧ F A ≤ 1 / 12) ∨ (1 / 12 : ℝ) < F A) := by
        apply eventMass_mono hμ
        intro A hA
        by_cases h : F A ≤ 1 / 12
        · exact Or.inl ⟨hA, h⟩
        · exact Or.inr (lt_of_not_ge h)
      _ ≤ _ := eventMass_union_le hμ _ _
  change (4 / 5 : ℝ) ≤ eventMass (matrixMass k) (fun A => Good k A ∧ F A ≤ 1 / 12)
  linarith

theorem good_gap_probability_of_budget {v M r s k : ℕ} {α : ℝ}
    (hk : 64 ≤ k) (hkv : k ≤ v) (hlam : lambda k M ≤ 1)
    (hp : ParameterBudget k M v) (hα : 1 ≤ α) (hrs : r + s = M)
    (hv : 6 * α * Real.exp (27 * α) * k * Real.log (2 * (M : ℝ) + 1) ≤ v) :
    (4 / 5 : ℝ) ≤ eventMass (matrixMass k) (fun A : CheapMatrix v M =>
      Good k A ∧
        eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k)) ≤ 1 / 12) := by
  apply good_gap_probability_of_bounds hp.k_large (lemma22_of_parameter_budget hk hkv hlam hp).2
  exact (no_unconditioned_bound hp.k_large hα hrs hv).trans
    (no_gap_decay_le_one_over_120 (by omega) (by have := hp.k_le_M; omega) hα)

theorem certificate_error_le_one_twelfth {k M v : ℕ}
    (hk : 1 ≤ k) (hv : 0 < v) (hM : 24 * (k : ℝ) ^ 2 ≤ M)
    (hsmall : (v : ℝ) ≤ (k : ℝ) ^ 2 / (192000 * Real.exp 1)) :
    lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120) ≤ 1 / 12 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hM0 : (0 : ℝ) < M := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hlam : lambda k M ≤ 1 / 24 := by
    unfold lambda
    apply (div_le_iff₀ hM0).mpr
    linarith
  have hd : 3000 ≤ effectiveDimension k v := by
    unfold effectiveDimension
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num only [Nat.cast_ofNat]
    apply (le_div_iff₀ (by positivity : 0 < 64 * Real.exp 1 * (v : ℝ))).mpr
    have hs := (le_div_iff₀ (by positivity : 0 < 192000 * Real.exp 1)).mp hsmall
    nlinarith
  have hdR : (3000 : ℝ) ≤ effectiveDimension k v := by exact_mod_cast hd
  have he : Real.exp (-(effectiveDimension k v : ℝ) / 120) ≤ 1 / 24 := by
    rw [show -(effectiveDimension k v : ℝ) / 120 =
      -((effectiveDimension k v : ℝ) / 120) by ring,
      Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith [Real.add_one_le_exp ((effectiveDimension k v : ℝ) / 120)]
  linarith

theorem eventually_certificate_error_le_one_twelfth {C₀ : ℝ} (hC₀ : 10000 ≤ C₀)
    (M v : ℕ → ℕ) (α : ℕ → ℝ)
    (hfamily : ∀ᶠ k in atTop,
      1 ≤ α k ∧ C₀ * (k : ℝ) ^ 2 ≤ M k ∧
      6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k)
    (hsub : Asymptotics.IsLittleO atTop
      (fun k => (v k : ℝ)) (fun k => (k : ℝ) ^ 2)) :
    ∀ᶠ k in atTop,
      lambda k (M k) + Real.exp (-(effectiveDimension k (v k) : ℝ) / 120) ≤ 1 / 12 := by
  have hsmall : ∀ᶠ k in atTop,
      (v k : ℝ) ≤ (k : ℝ) ^ 2 / (192000 * Real.exp 1) := by
    have h := hsub.bound (by positivity : (0 : ℝ) < 1 / (192000 * Real.exp 1))
    filter_upwards [h] with k hk
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (v k) : (0 : ℝ) ≤ v k),
      abs_of_nonneg (sq_nonneg (k : ℝ))] at hk
    calc
      (v k : ℝ) ≤ (1 / (192000 * Real.exp 1)) * (k : ℝ) ^ 2 := hk
      _ = (k : ℝ) ^ 2 / (192000 * Real.exp 1) := by ring
  filter_upwards [hfamily, hsmall,
    eventually_basic_parameter_bounds hC₀ M v α hfamily hsub] with k hf hs hb
  apply certificate_error_le_one_twelfth (by omega) (by omega) _ hs
  exact (mul_le_mul_of_nonneg_right (by linarith : (24 : ℝ) ≤ C₀)
    (sq_nonneg (k : ℝ))).trans hf.2.1

theorem eventually_good_gap_probability {C₀ : ℝ} (hC₀ : 10000 ≤ C₀)
    (M v r s : ℕ → ℕ) (α : ℕ → ℝ)
    (hfamily : ∀ᶠ k in atTop,
      1 ≤ α k ∧ C₀ * (k : ℝ) ^ 2 ≤ M k ∧
      6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k)
    (hsub : Asymptotics.IsLittleO atTop
      (fun k => (v k : ℝ)) (fun k => (k : ℝ) ^ 2))
    (hblocks : ∀ᶠ k in atTop, r k + s k = M k) :
    ∀ᶠ k in atTop,
      (lambda k (M k) + Real.exp (-(effectiveDimension k (v k) : ℝ) / 120) ≤ 1 / 12) ∧
      (4 / 5 : ℝ) ≤ eventMass (matrixMass k) (fun A : CheapMatrix (v k) (M k) =>
        Good k A ∧ eventMass (noMass (v k) (r k) (s k))
          (fun x => HasCoverAtMost k A x (3 * α k * k)) ≤ 1 / 12) := by
  filter_upwards [hfamily, hblocks,
    eventually_parameter_budget hC₀ M v α hfamily hsub,
    eventually_basic_parameter_bounds hC₀ M v α hfamily hsub,
    eventually_certificate_error_le_one_twelfth hC₀ M v α hfamily hsub,
    eventually_ge_atTop (64 : ℕ)] with k hf hrs hp hb he hk
  exact ⟨he, good_gap_probability_of_budget hk hb.2.1 hb.2.2 hp hf.1 hrs hf.2.2⟩

theorem eventually_good_gap_exists {C₀ : ℝ} (hC₀ : 10000 ≤ C₀)
    (M v r s : ℕ → ℕ) (α : ℕ → ℝ)
    (hfamily : ∀ᶠ k in atTop,
      1 ≤ α k ∧ C₀ * (k : ℝ) ^ 2 ≤ M k ∧
      6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k)
    (hsub : Asymptotics.IsLittleO atTop
      (fun k => (v k : ℝ)) (fun k => (k : ℝ) ^ 2))
    (hblocks : ∀ᶠ k in atTop, r k + s k = M k) :
    ∀ᶠ k in atTop,
      (lambda k (M k) + Real.exp (-(effectiveDimension k (v k) : ℝ) / 120) ≤ 1 / 12) ∧
      ∃ A : CheapMatrix (v k) (M k), Good k A ∧
        eventMass (noMass (v k) (r k) (s k))
          (fun x => HasCoverAtMost k A x (3 * α k * k)) ≤ 1 / 12 := by
  filter_upwards [eventually_good_gap_probability hC₀ M v r s α hfamily hsub hblocks]
    with k hk
  refine ⟨hk.1, ?_⟩
  by_contra! hn
  have hz : eventMass (matrixMass k) (fun A : CheapMatrix (v k) (M k) =>
      Good k A ∧ eventMass (noMass (v k) (r k) (s k))
        (fun x => HasCoverAtMost k A x (3 * α k * k)) ≤ 1 / 12) = 0 := by
    apply Finset.sum_eq_zero
    intro A _
    rw [if_neg]
    rintro ⟨hA, hprob⟩
    exact not_lt_of_ge hprob (hn A hA)
  linarith [hk.2]

/-- A single good public matrix for the manuscript's balanced Alice/Bob split.
All probability and numerical hypotheses have been discharged. -/
theorem eventually_balanced_good_gap {C₀ : ℝ} (hC₀ : 10000 ≤ C₀)
    (M v : ℕ → ℕ) (α : ℕ → ℝ)
    (hfamily : ∀ᶠ k in atTop,
      1 ≤ α k ∧ C₀ * (k : ℝ) ^ 2 ≤ M k ∧
      6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k)
    (hsub : Asymptotics.IsLittleO atTop
      (fun k => (v k : ℝ)) (fun k => (k : ℝ) ^ 2)) :
    ∀ᶠ k in atTop,
      (lambda k (M k) + Real.exp (-(effectiveDimension k (v k) : ℝ) / 120) ≤ 1 / 12) ∧
      ∃ A : CheapMatrix (v k) (M k), Good k A ∧
        eventMass (noMass (v k) (M k / 2) (M k - M k / 2))
          (fun x => HasCoverAtMost k A x (3 * α k * k)) ≤ 1 / 12 :=
  eventually_good_gap_exists hC₀ M v (fun k => M k / 2) (fun k => M k - M k / 2) α
    hfamily hsub (Eventually.of_forall fun k => Nat.add_sub_of_le (Nat.div_le_self (M k) 2))

end
end SetCover.Paper
