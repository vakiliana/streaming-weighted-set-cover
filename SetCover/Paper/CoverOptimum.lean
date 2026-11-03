import SetCover.Paper.Basic

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def cheapFamily (M r s : ℕ) : Finset (SetId M r s) :=
  univ.image Sum.inl

theorem cheapFamily_isCover {v M r s : ℕ} {A : CheapMatrix v M}
    (hA : Covers A) (x : Input v r s) :
    IsCover A x (cheapFamily M r s) := by
  intro e
  obtain ⟨j, hj⟩ := hA e.1
  exact ⟨Sum.inl j, by simp [cheapFamily], hj⟩

@[simp] theorem cost_cheapFamily (k M r s : ℕ) :
    cost k (cheapFamily M r s) = M := by
  unfold cost cheapFamily
  rw [Finset.sum_image]
  · simp [weight]
  · intro a _ b _ h
    exact Sum.inl.inj h

theorem cover_cost_exists {v M r s : ℕ} (k : ℕ) (A : CheapMatrix v M)
    (x : Input v r s) (hA : Covers A) :
    ∃ n : ℕ, ∃ F : Finset (SetId M r s), IsCover A x F ∧ cost k F = n :=
  ⟨M, cheapFamily M r s, cheapFamily_isCover hA x, cost_cheapFamily k M r s⟩

/-- The integer optimum is defined only for a covering cheap matrix. -/
def optimum {v M r s : ℕ} (k : ℕ) (A : CheapMatrix v M)
    (x : Input v r s) (hA : Covers A) : ℕ :=
  Nat.find (cover_cost_exists k A x hA)

theorem optimum_spec {v M r s : ℕ} (k : ℕ) (A : CheapMatrix v M)
    (x : Input v r s) (hA : Covers A) :
    ∃ F : Finset (SetId M r s), IsCover A x F ∧ cost k F = optimum k A x hA :=
  Nat.find_spec (cover_cost_exists k A x hA)

theorem optimum_le_cost {v M r s : ℕ} {k : ℕ} {A : CheapMatrix v M}
    {x : Input v r s} (hA : Covers A) {F : Finset (SetId M r s)}
    (hF : IsCover A x F) : optimum k A x hA ≤ cost k F :=
  Nat.find_min' (cover_cost_exists k A x hA) ⟨F, hF, rfl⟩

theorem hasCoverAtMost_iff_optimum_le {v M r s : ℕ} {k : ℕ}
    {A : CheapMatrix v M} {x : Input v r s} (hA : Covers A) (B : ℝ) :
    HasCoverAtMost k A x B ↔ (optimum k A x hA : ℝ) ≤ B := by
  constructor
  · rintro ⟨F, hF, hcost⟩
    exact (Nat.cast_le.mpr (optimum_le_cost hA hF)).trans hcost
  · intro h
    obtain ⟨F, hF, hcost⟩ := optimum_spec k A x hA
    exact ⟨F, hF, by simpa [hcost] using h⟩

theorem optimum_le_M {v M r s : ℕ} (k : ℕ) (A : CheapMatrix v M)
    (x : Input v r s) (hA : Covers A) : optimum k A x hA ≤ M := by
  simpa using optimum_le_cost (k := k) hA (cheapFamily_isCover hA x)

end
end SetCover.Paper
