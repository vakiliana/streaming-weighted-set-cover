import SetCover.ShortParity
import SetCover.BernoulliCounts

/-!
The short-parity expectation estimate for the actual Bernoulli matrix sampler.
The proof uses the marked-four-column expansion of `bias`, rather than a
spectral hypothesis. The elementary estimates below require `64 ≤ k`.
-/

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

theorem short_degree_pos {v : ℕ} (t : Cube v) (ht : t ≠ zeroVector) :
    0 < degree t := by
  by_contra hn
  have hz : degree t = 0 := by omega
  have he : (univ.filter (fun i => t i = true)) = ∅ :=
    Finset.card_eq_zero.mp hz
  apply ht
  funext i
  have hi := Finset.filter_eq_empty_iff.mp he (Finset.mem_univ i)
  simpa [zeroVector, Bool.not_eq_true] using hi

theorem short_sum_degree {v : ℕ} (f : ℕ → ℝ) :
    (∑ t : Cube v, f (degree t)) =
      ∑ j ∈ range (v + 1), (Nat.choose v j : ℝ) * f j := by
  calc
    _ = ∑ S : Finset (Fin v), f S.card := by
      rw [← (bitSetEquiv (Fin v)).symm.sum_comp]
      apply Finset.sum_congr rfl
      intro S _
      have h := (bitSetEquiv (Fin v)).apply_symm_apply S
      change bitSupport ((bitSetEquiv (Fin v)).symm S) = S at h
      change f (bitSupport ((bitSetEquiv (Fin v)).symm S)).card = f S.card
      rw [h]
    _ = _ := by simpa using sum_finset_card (ι := Fin v) f

theorem short_choose_exp_bound (v : ℕ) {t : ℕ} (ht : 0 < t) :
    (Nat.choose v t : ℝ) ≤ (Real.exp 1 * v / t) ^ t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have he : Real.exp (t : ℝ) = Real.exp 1 ^ t := by simp [← Real.exp_nat_mul]
  have hmul : (Nat.choose v t : ℝ) * (t : ℝ) ^ t ≤ (Real.exp 1 * v) ^ t := by
    calc
      _ ≤ ((v : ℝ) ^ t / t.factorial) * (t : ℝ) ^ t :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div t v) (pow_nonneg htR.le _)
      _ = (v : ℝ) ^ t * ((t : ℝ) ^ t / t.factorial) := by ring
      _ ≤ (v : ℝ) ^ t * Real.exp (t : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.pow_div_factorial_le_exp (t : ℝ) htR.le t) (by positivity)
      _ = _ := by rw [he, mul_pow]; ring
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos htR _)).mpr hmul

theorem short_degree_term_le {v k d t : ℕ} (hk : 0 < k)
    (hcut : 16 * Real.exp 1 * v * d / (k : ℝ) ^ 2 ≤ 1 / 4)
    (ht : 0 < t) (htd : t < d) :
    (Nat.choose v t : ℝ) * (4 * (t : ℝ) / k) ^ (2 * t) ≤ (1 / 4 : ℝ) ^ t := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htdR : (t : ℝ) ≤ d := by exact_mod_cast htd.le
  have hratio : 16 * Real.exp 1 * v * t / (k : ℝ) ^ 2 ≤ 1 / 4 :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htdR (by positivity : 0 ≤ 16 * Real.exp 1 * (v : ℝ)))
      (sq_nonneg _)).trans hcut
  calc
    _ ≤ (Real.exp 1 * v / t) ^ t * (4 * (t : ℝ) / k) ^ (2 * t) :=
      mul_le_mul_of_nonneg_right (short_choose_exp_bound v ht) (by positivity)
    _ = (16 * Real.exp 1 * v * t / (k : ℝ) ^ 2) ^ t := by
      rw [pow_mul, ← mul_pow]
      congr 1
      field_simp
      ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hratio t

theorem short_geometric_tail_le (v d : ℕ) :
    (∑ j ∈ range (v + 1), if 0 < j ∧ j < d then (1 / 4 : ℝ) ^ j else 0) ≤
      (1 / 3 : ℝ) := by
  have hgeo : (1 / 4 : ℝ) * (∑ j ∈ range v, (1 / 4 : ℝ) ^ j) ≤ 1 / 3 := by
    have h := geom_sum_mul_neg (1 / 4 : ℝ) v
    have hp : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ v := by positivity
    nlinarith
  calc
    _ ≤ ∑ j ∈ range (v + 1), if j = 0 then (0 : ℝ) else (1 / 4 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = 0
      · simp [hj]
      · rw [if_neg hj]
        split_ifs
        · exact le_rfl
        · positivity
    _ = (1 / 4 : ℝ) * (∑ j ∈ range v, (1 / 4 : ℝ) ^ j) := by
      rw [Finset.sum_range_succ']
      simp [pow_succ, Finset.mul_sum, mul_comm]
    _ ≤ _ := hgeo

/-- A cutoff form, useful independently of the manuscript's floor definition. -/
theorem short_moment_bound_cutoff {v M k d : ℕ}
    (hk : 64 ≤ k) (hkM : k ≤ M) (hlam : lambda k M ≤ 1)
    (hcut : 16 * Real.exp 1 * v * d / (k : ℝ) ^ 2 ≤ 1 / 4) :
    expectation (matrixMass k)
      (fun A : CheapMatrix v M => shortMass (noiseMass k A) d) ≤
        100 * lambda k M ^ 2 := by
  let F : ℕ → ℝ := fun j =>
    if 0 < j ∧ j < d then (4 * (j : ℝ) / k) ^ (2 * j) else 0
  have hmass :
      expectation (matrixMass k) (fun A : CheapMatrix v M => shortMass (noiseMass k A) d) ≤
        8 * lambda k M ^ 2 * ∑ t : Cube v, F (degree t) := by
    unfold shortMass
    rw [short_expectation_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : t ≠ zeroVector ∧ degree t < d
    · have hpos := short_degree_pos t ht.1
      simp only [if_pos ht, F, if_pos (show 0 < degree t ∧ degree t < d from ⟨hpos, ht.2⟩)]
      exact short_parity_expectation_le hk hkM hlam t hpos
    · simp only [if_neg ht, expectation, mul_zero, Finset.sum_const_zero]
      have hF : 0 ≤ F (degree t) := by dsimp [F]; split_ifs <;> positivity
      exact mul_nonneg (by positivity) hF
  calc
    _ ≤ 8 * lambda k M ^ 2 * ∑ t : Cube v, F (degree t) := hmass
    _ = 8 * lambda k M ^ 2 *
        ∑ j ∈ range (v + 1), (Nat.choose v j : ℝ) * F j := by rw [short_sum_degree F]
    _ ≤ 8 * lambda k M ^ 2 *
        ∑ j ∈ range (v + 1), if 0 < j ∧ j < d then (1 / 4 : ℝ) ^ j else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : 0 < j ∧ j < d
      · simp only [F, if_pos hj]
        exact short_degree_term_le (by omega) hcut hj.1 hj.2
      · simp [F, hj]
    _ ≤ 8 * lambda k M ^ 2 * (1 / 3) :=
      mul_le_mul_of_nonneg_left (short_geometric_tail_le v d) (by positivity)
    _ ≤ 100 * lambda k M ^ 2 := by nlinarith [sq_nonneg (lambda k M)]

theorem short_effective_dimension_cutoff {k v : ℕ} (hk : 0 < k) (hv : 0 < v) :
    16 * Real.exp 1 * v * effectiveDimension k v / (k : ℝ) ^ 2 ≤ 1 / 4 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hden : 0 < 64 * Real.exp 1 * (v : ℝ) := by positivity
  have hd : (effectiveDimension k v : ℝ) ≤ (k : ℝ) ^ 2 / (64 * Real.exp 1 * v) :=
    Nat.floor_le (by positivity)
  have hmul := (le_div_iff₀ hden).mp hd
  apply (div_le_iff₀ (sq_pos_of_pos hkR)).mpr
  nlinarith

/-- The short-moment estimate required by the concentration assembly, with no
spectral or probabilistic premise beyond the explicit finite parameters. -/
theorem short_moment_bound {v M k : ℕ}
    (hk : 64 ≤ k) (hkM : k ≤ M) (hlam : lambda k M ≤ 1) (hkv : k ≤ v) :
    expectation (matrixMass k)
      (fun A : CheapMatrix v M => shortMass (noiseMass k A) (effectiveDimension k v)) ≤
        100 * lambda k M ^ 2 :=
  short_moment_bound_cutoff hk hkM hlam
    (short_effective_dimension_cutoff (by omega) (by omega))

end
end SetCover
