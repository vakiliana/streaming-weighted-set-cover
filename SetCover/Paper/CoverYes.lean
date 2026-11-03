import SetCover.Paper.CoverOptimum

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def repairFamily {M r s : ℕ} (K : Finset (Fin M)) (i : Fin r) (j : Fin s) :
    Finset (SetId M r s) :=
  insert (Sum.inr (Sum.inl i)) (insert (Sum.inr (Sum.inr j)) (K.image Sum.inl))

theorem repairFamily_cost {M r s : ℕ} (k : ℕ) (K : Finset (Fin M))
    (i : Fin r) (j : Fin s) :
    cost k (repairFamily K i j) = 2 * k + K.card := by
  unfold cost repairFamily
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_image]
  · simp [weight]
    omega
  · intro a _ b _ h
    exact Sum.inl.inj h

theorem repairFamily_isCover {v M r s : ℕ} {A : CheapMatrix v M}
    {x : Input v r s} {K : Finset (Fin M)} (i : Fin r) (j : Fin s)
    (hK : ∀ e, planted (x.1 i) (x.2 j) e = true → ∃ a ∈ K, A e a = true) :
    IsCover A x (repairFamily K i j) := by
  rintro ⟨e, b⟩
  by_cases hi : x.1 i e = b
  · exact ⟨Sum.inr (Sum.inl i), by simp [repairFamily], hi⟩
  by_cases hj : x.2 j e = b
  · exact ⟨Sum.inr (Sum.inr j), by simp [repairFamily], hj⟩
  have hp : planted (x.1 i) (x.2 j) e = true := by
    simp only [planted, xor, oneVector]
    cases hx : x.1 i e <;> cases hy : x.2 j e <;> cases b <;> simp_all
  obtain ⟨a, ha, hAe⟩ := hK e hp
  exact ⟨Sum.inl a, by simp [repairFamily, ha], hAe⟩

theorem repairable_pair_hasCoverAtMost {v M r s : ℕ} {k : ℕ}
    {A : CheapMatrix v M} {x : Input v r s} (i : Fin r) (j : Fin s)
    (h : Repairable k A (planted (x.1 i) (x.2 j))) :
    HasCoverAtMost k A x (3 * k) := by
  obtain ⟨K, hcard, hK⟩ := h
  refine ⟨repairFamily K i j, repairFamily_isCover i j hK, ?_⟩
  rw [repairFamily_cost]
  exact_mod_cast (show 2 * k + K.card ≤ 3 * k by omega)

theorem yes_support_hasCoverAtMost {v M r s : ℕ} {k : ℕ}
    (_hk : 8 ≤ k) (hkM : k ≤ M) (hr : 0 < r) (hs : 0 < s)
    (A : CheapMatrix v M) (x : Input v r s) (hx : 0 < yesMass k r s A x) :
    HasCoverAtMost k A x (3 * k) := by
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have hno : 0 < noMass v r s x := by
    unfold noMass uniformMass
    exact one_div_pos.mpr card_pos
  have hmean : 0 < average (fun i : Fin r => average (fun j : Fin s =>
      (Fintype.card (Cube v) : ℝ) * noiseMass k A (planted (x.1 i) (x.2 j)))) :=
    (mul_pos_iff_of_pos_left hno).mp hx
  obtain ⟨i, j, hij⟩ : ∃ i : Fin r, ∃ j : Fin s,
      0 < noiseMass k A (planted (x.1 i) (x.2 j)) := by
    by_contra! h
    have hle : average (fun i : Fin r => average (fun j : Fin s =>
        (Fintype.card (Cube v) : ℝ) * noiseMass k A (planted (x.1 i) (x.2 j)))) ≤ 0 := by
      have hh := average_mono (fun i => average_mono (fun j =>
        mul_nonpos_of_nonneg_of_nonpos
          (Nat.cast_nonneg (Fintype.card (Cube v)) : (0 : ℝ) ≤ _) (h i j)))
      simpa only [average_const] using hh
    linarith
  exact repairable_pair_hasCoverAtMost i j (noiseMass_repairable hkM A _ hij)

end
end SetCover.Paper
