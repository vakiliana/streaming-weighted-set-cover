import SetCover.Paper.CoverProduct
import SetCover.Paper.CoverFamilies

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem cover_log_q_lower {k : ℕ} (hk : 8 ≤ k) :
    -(8 / (k : ℝ)) ≤ Real.log (q k) := by
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hq : 0 < q k := q_pos hk
  have hqhalf : (1 / 2 : ℝ) ≤ q k := by
    have hb : 4 / (k : ℝ) ≤ 1 / 2 := (div_le_iff₀ hk0).mpr (by linarith)
    unfold q beta
    linarith
  have hi : (q k)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hq]
    linarith
  have he : (1 - 4 / (k : ℝ)) * (q k)⁻¹ = 1 := by
    change q k * (q k)⁻¹ = 1
    exact mul_inv_cancel₀ hq.ne'
  have hm := mul_le_mul_of_nonneg_left hi
    (by positivity : (0 : ℝ) ≤ 4 / (k : ℝ))
  have hlower : -(8 / (k : ℝ)) ≤ 1 - (q k)⁻¹ := by
    ring_nf at he hm ⊢
    linarith only [he, hm]
  exact hlower.trans (Real.one_sub_inv_le_log_of_pos hq)

theorem coverBitMass_false_lower {M r s k : ℕ} (hk : 8 ≤ k)
    (i : SetId M r s) :
    Real.exp (-(9 / (k : ℝ)) * (weight k i : ℝ)) ≤ coverBitMass k i false := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  cases i with
  | inl j =>
    simp only [weight, Sum.elim_inl, Nat.cast_one, mul_one, coverBitMass, matrixBitMass]
    rw [← Real.exp_log (q_pos hk)]
    apply Real.exp_le_exp.mpr
    exact (neg_le_neg (div_le_div_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 9)
      hk0.le)).trans (cover_log_q_lower hk)
  | inr j =>
    simp only [weight, Sum.elim_inr, coverBitMass]
    have he : -(9 / (k : ℝ)) * (k : ℝ) = -9 := by field_simp
    rw [he, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 9)]
    linarith [Real.add_one_le_exp (9 : ℝ)]

theorem omissionProbability_lower {M r s k : ℕ} (hk : 8 ≤ k)
    (F : Finset (SetId M r s)) :
    Real.exp (-(9 / (k : ℝ)) * (cost k F : ℝ)) ≤ omissionProbability k F := by
  calc
    Real.exp (-(9 / (k : ℝ)) * (cost k F : ℝ)) =
        ∏ i ∈ F, Real.exp (-(9 / (k : ℝ)) * (weight k i : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      simp [cost, Finset.mul_sum]
    _ ≤ omissionProbability k F := by
      apply Finset.prod_le_prod
      · intro i _
        exact (Real.exp_pos _).le
      · intro i _
        exact coverBitMass_false_lower hk i

/-- The paper's one-coordinate obstruction bound, for the actual row law. -/
theorem no_one_coordinate_bound {M r s k : ℕ} {α : ℝ} (hk : 8 ≤ k)
    (F : Finset (SetId M r s)) (hcost : (cost k F : ℝ) ≤ 3 * α * k) :
    Real.exp (-27 * α) ≤ eventMass (coverRowMass k) (rowOmission F) := by
  rw [rowOmission_probability]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm := mul_le_mul_of_nonpos_left hcost
    (neg_nonpos.mpr (by positivity) : -(9 / (k : ℝ)) ≤ 0)
  have he : -(9 / (k : ℝ)) * (3 * α * k) = -27 * α := by
    field_simp
    ring
  rw [he] at hm
  exact (Real.exp_le_exp.mpr hm).trans (omissionProbability_lower hk F)

theorem no_fixed_family_power_bound {v M r s k : ℕ} (hk : 8 ≤ k)
    (F : Finset (SetId M r s)) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      eventMass (noMass v r s) (fun x => IsCover A x F)) ≤
        (1 - omissionProbability k F) ^ v := by
  have hno : ∀ x : Input v r s, 0 ≤ noMass v r s x := by
    intro x
    unfold noMass uniformMass
    positivity
  calc
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
        eventMass (noMass v r s) (fun x => IsCover A x F)) ≤
      expectation (matrixMass k) (fun A : CheapMatrix v M =>
        eventMass (noMass v r s) (fun x =>
          ∀ e, ¬ rowOmission F (coverRowsEquiv v M r s (A, x) e))) := by
      apply cover_expectation_mono (matrixMass_probability hk).1
      intro A
      exact eventMass_mono hno fun _ => isCover_no_rowOmission
    _ = eventMass (fun y : Fin v → SetId M r s → Bool =>
        ∏ e, coverRowMass k (y e)) (fun y => ∀ e, ¬ rowOmission F (y e)) :=
      by
        exact cover_joint_eventMass (v := v) (M := M) (r := r) (s := s) k
          (fun y => ∀ e, ¬ rowOmission F (y e))
    _ = ∏ _e : Fin v, eventMass (coverRowMass k) (fun row => ¬ rowOmission F row) :=
      by
        exact cover_product_eventMass
          (fun _e : Fin v => coverRowMass (M := M) (r := r) (s := s) k)
          (fun _e row => ¬ rowOmission F row)
    _ = (1 - omissionProbability k F) ^ v := by
      rw [eventMass_compl (coverRowMass_probability (M := M) (r := r) (s := s) hk),
        rowOmission_probability]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Independence across actual matrix rows and transversal bits. -/
theorem no_fixed_family_bound {v M r s k : ℕ} {α : ℝ} (hk : 8 ≤ k)
    (F : Finset (SetId M r s)) (hcost : (cost k F : ℝ) ≤ 3 * α * k) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      eventMass (noMass v r s) (fun x => IsCover A x F)) ≤
        Real.exp (-Real.exp (-27 * α) * v) := by
  have hrow := coverRowMass_probability (M := M) (r := r) (s := s) hk
  have hnonneg : 0 ≤ 1 - omissionProbability k F := by
    rw [← rowOmission_probability k F, ← eventMass_compl hrow]
    exact cover_eventMass_nonneg hrow.1 _
  have hlower : Real.exp (-27 * α) ≤ omissionProbability k F := by
    simpa only [rowOmission_probability] using no_one_coordinate_bound hk F hcost
  have hbase : 1 - omissionProbability k F ≤ Real.exp (-omissionProbability k F) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-omissionProbability k F)
  calc
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
        eventMass (noMass v r s) (fun x => IsCover A x F)) ≤
        (1 - omissionProbability k F) ^ v := no_fixed_family_power_bound hk F
    _ ≤ Real.exp (-omissionProbability k F) ^ v := pow_le_pow_left₀ hnonneg hbase _
    _ = Real.exp (-omissionProbability k F * v) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-Real.exp (-27 * α) * v) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hlower) (Nat.cast_nonneg v)

theorem no_union_bound {v M r s k : ℕ} {α : ℝ} (hk : 8 ≤ k) (hα : 1 ≤ α) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k))) ≤
      Real.exp (3 * α * k * Real.log (Fintype.card (SetId M r s) + 1) -
        Real.exp (-27 * α) * v) := by
  let B : ℝ := 3 * α * k
  let C : ℝ := Real.exp (-Real.exp (-27 * α) * v)
  have hα0 : 0 ≤ α := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hno : ∀ x : Input v r s, 0 ≤ noMass v r s x := by
    intro x
    unfold noMass uniformMass
    positivity
  calc
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
        eventMass (noMass v r s) (fun x => HasCoverAtMost k A x B)) ≤
      expectation (matrixMass k) (fun A : CheapMatrix v M =>
        ∑ F : AffordableFamily k M r s B,
          eventMass (noMass v r s) (fun x => IsCover A x F.val)) := by
      apply cover_expectation_mono (matrixMass_probability hk).1
      intro A
      simp only [hasCoverAtMost_iff_affordable]
      exact eventMass_exists_le hno _
    _ = ∑ F : AffordableFamily k M r s B,
        expectation (matrixMass k) (fun A : CheapMatrix v M =>
          eventMass (noMass v r s) (fun x => IsCover A x F.val)) := by
      simp only [expectation, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ _F : AffordableFamily k M r s B, C := by
      apply Finset.sum_le_sum
      intro F _
      exact no_fixed_family_bound hk F.val F.property
    _ = (Fintype.card (AffordableFamily k M r s B) : ℝ) * C := by simp
    _ ≤ Real.exp (B * Real.log (Fintype.card (SetId M r s) + 1)) * C :=
      mul_le_mul_of_nonneg_right
        (affordableFamilies_card_le_exp (by omega : 1 ≤ k) hB) (Real.exp_pos _).le
    _ = Real.exp (3 * α * k * Real.log (Fintype.card (SetId M r s) + 1) -
        Real.exp (-27 * α) * v) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [B]
      ring

/-- The unconditioned NO gap, without assigning an optimum to uncoverable inputs. -/
theorem no_unconditioned_bound {v M r s k : ℕ} {α : ℝ}
    (hk : 8 ≤ k) (hα : 1 ≤ α) (hrs : r + s = M)
    (hv : 6 * α * Real.exp (27 * α) * k * Real.log (2 * (M : ℝ) + 1) ≤ v) :
    expectation (matrixMass k) (fun A : CheapMatrix v M =>
      eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k))) ≤
      Real.exp (-3 * α * k * Real.log (2 * (M : ℝ) + 1)) := by
  have hcard : (Fintype.card (SetId M r s) : ℝ) = 2 * M := by
    simp only [SetId, Fintype.card_sum, Fintype.card_fin, hrs, Nat.cast_add]
    ring
  have hprod : Real.exp (-27 * α) * Real.exp (27 * α) = 1 := by
    rw [← Real.exp_add]
    simp
  have hm := mul_le_mul_of_nonneg_left hv (Real.exp_pos (-27 * α)).le
  have hv' : 6 * α * k * Real.log (2 * (M : ℝ) + 1) ≤
      Real.exp (-27 * α) * v := by
    calc
      6 * α * k * Real.log (2 * (M : ℝ) + 1) =
        (Real.exp (-27 * α) * Real.exp (27 * α)) *
          (6 * α * k * Real.log (2 * (M : ℝ) + 1)) := by rw [hprod, one_mul]
      _ = Real.exp (-27 * α) *
        (6 * α * Real.exp (27 * α) * k * Real.log (2 * (M : ℝ) + 1)) := by ring
      _ ≤ Real.exp (-27 * α) * v := hm
  have hu := no_union_bound (v := v) (M := M) (r := r) (s := s) hk hα
  rw [hcard] at hu
  exact hu.trans (Real.exp_le_exp.mpr (by linarith))

end
end SetCover.Paper
