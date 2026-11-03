import SetCover.Probability

/-!
Markov/union-bound assembly for Appendix A.2. `Complete.lean` discharges its
premises using `ShortMoment.lean`, `LongMoment.lean`, and `AsymptoticBudget.lean`.
-/

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev CoordinateSubsets (v d : ℕ) := {D : Finset (Fin v) // D.card = d}

theorem shortMass_nonneg {v : ℕ} (μ : Cube v → ℝ) (d : ℕ) : 0 ≤ shortMass μ d := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs <;> positivity

theorem fourierGood_of_sparse_bounds {v M k : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M)
    (A : CheapMatrix v M) (hc : Covers A)
    (hs : shortMass (noiseMass k A) (effectiveDimension k v) ≤ lambda k M)
    (hl : ∀ D : CoordinateSubsets v (effectiveDimension k v),
      sparseProbability k A D.val ≤ Real.exp (-(effectiveDimension k v : ℝ) / 60)) :
    FourierGood k A := by
  refine ⟨hc, hs, ?_⟩
  intro t ht
  obtain ⟨D, hD, hcard⟩ := Finset.exists_subset_card_eq ht
  have hD' : ∀ e ∈ D, t e = true := by
    intro e he
    exact (Finset.mem_filter.mp (hD he)).2
  exact (noiseFourier_dominated hk hkM A t D hD').trans (hl ⟨D, hcard⟩)

theorem power_markov {Ω : Type*} [Fintype Ω] {μ F : Ω → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x)
    {L : ℕ} (hL : 0 < L) {η B : ℝ} (hη : 0 < η)
    (hm : expectation μ (fun x => F x ^ L) ≤ B) :
    eventMass μ (fun x => η < F x) ≤ B / η ^ L := by
  have hsub : eventMass μ (fun x => η < F x) ≤
      eventMass μ (fun x => η ^ L < F x ^ L) := by
    apply eventMass_mono hμ
    intro x hx
    exact pow_lt_pow_left₀ hx (le_of_lt hη) (Nat.ne_of_gt hL)
  have hmk := finite_markov hμ (fun x => pow_nonneg (hF x) L) (pow_pos hη L)
  exact hsub.trans (hmk.trans (div_le_div_of_nonneg_right hm (le_of_lt (pow_pos hη L))))

/-- Quantitative finite assembly. The full proof supplies `hshort`, `hlong`, and
`hbudget` from the actual sampler and the manuscript's parameter assumptions. -/
theorem lemma22_of_moment_bounds {v M k L : ℕ}
    (hk : 8 ≤ k) (hkM : k ≤ M) (hd : 0 < effectiveDimension k v)
    (hL : 0 < L) {shortBudget momentBudget : ℝ}
    (hshort :
      expectation (matrixMass k)
        (fun A : CheapMatrix v M => shortMass (noiseMass k A) (effectiveDimension k v))
      ≤ shortBudget)
    (hlong : ∀ D : CoordinateSubsets v (effectiveDimension k v),
      expectation (matrixMass k)
        (fun A : CheapMatrix v M => sparseProbability k A D.val ^ L) ≤ momentBudget)
    (hbudget :
      (v : ℝ) * q k ^ M + shortBudget / lambda k M +
        Fintype.card (CoordinateSubsets v (effectiveDimension k v)) *
          (momentBudget / Real.exp (-(effectiveDimension k v : ℝ) / 60) ^ L)
        ≤ (1 / 10 : ℝ)) :
    Lemma22Conclusion k M v := by
  let ν : CheapMatrix v M → ℝ := matrixMass k
  let d := effectiveDimension k v
  let lam := lambda k M
  let η := Real.exp (-(d : ℝ) / 60)
  have hν : IsProbability ν := matrixMass_probability hk
  have hlam : 0 < lam := by
    dsimp [lam, lambda]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    positivity
  have hη : 0 < η := Real.exp_pos _
  let badCover := fun A : CheapMatrix v M => ¬ Covers A
  let badShort := fun A : CheapMatrix v M => lam < shortMass (noiseMass k A) d
  let badLong := fun A : CheapMatrix v M =>
    ∃ D : CoordinateSubsets v d, η < sparseProbability k A D.val
  have hs : eventMass ν badShort ≤ shortBudget / lam :=
    (finite_markov hν.1 (fun A => shortMass_nonneg _ _) hlam).trans
      (div_le_div_of_nonneg_right hshort (le_of_lt hlam))
  have hl : eventMass ν badLong ≤
      Fintype.card (CoordinateSubsets v d) * (momentBudget / η ^ L) := by
    calc
      eventMass ν badLong ≤ ∑ D : CoordinateSubsets v d,
          eventMass ν (fun A => η < sparseProbability k A D.val) :=
          eventMass_exists_le hν.1 _
      _ ≤ ∑ _D : CoordinateSubsets v d, momentBudget / η ^ L := by
        apply Finset.sum_le_sum
        intro D _
        exact power_markov hν.1 (fun A => sparseProbability_nonneg hkM A D.val)
          hL hη (hlong D)
      _ = _ := by simp
  have hfail : eventMass ν (fun A => ¬ FourierGood k A) ≤
      eventMass ν badCover + eventMass ν badShort + eventMass ν badLong := by
    calc
      eventMass ν (fun A => ¬ FourierGood k A)
          ≤ eventMass ν (fun A => badCover A ∨ badShort A ∨ badLong A) := by
            apply eventMass_mono hν.1
            intro A hn
            by_contra h
            have hc : Covers A := by
              by_contra hn
              exact h (Or.inl hn)
            have hs' : shortMass (noiseMass k A) d ≤ lam := by
              by_contra hn
              exact h (Or.inr (Or.inl (lt_of_not_ge hn)))
            have hl' : ∀ D : CoordinateSubsets v d, sparseProbability k A D.val ≤ η := by
              intro D
              by_contra hn
              exact h (Or.inr (Or.inr ⟨D, lt_of_not_ge hn⟩))
            exact hn (fourierGood_of_sparse_bounds hk hkM A hc hs' hl')
      _ ≤ eventMass ν badCover +
          eventMass ν (fun A => badShort A ∨ badLong A) := eventMass_union_le hν.1 _ _
      _ ≤ eventMass ν badCover + eventMass ν badShort + eventMass ν badLong := by
        have h := eventMass_union_le hν.1 badShort badLong
        linarith
  have hc : eventMass ν badCover ≤ (v : ℝ) * q k ^ M := coverage_failure_le hk
  have htotal : eventMass ν (fun A => ¬ FourierGood k A) ≤ (1 / 10 : ℝ) := by
    change (v : ℝ) * q k ^ M + shortBudget / lam +
      Fintype.card (CoordinateSubsets v d) * (momentBudget / η ^ L) ≤ (1 / 10 : ℝ) at hbudget
    linarith
  rw [eventMass_compl hν] at htotal
  apply lemma22_of_joint_fourier_event hk hkM hd
  change (9 / 10 : ℝ) ≤ eventMass ν (FourierGood k)
  linarith

end
end SetCover
