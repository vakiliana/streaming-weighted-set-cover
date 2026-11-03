import SetCover.ReplicaOverlap

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

def multiplicity {M k L : ℕ} (ks : Fin L → RepairChoices M k) (j : Fin M) : ℕ :=
  (univ.filter fun a => j ∈ (ks a).val).card

def sharedCount {M k L : ℕ} (ks : Fin L → RepairChoices M k) (a : Fin L) : ℕ :=
  ((ks a).val.filter fun j => 2 ≤ multiplicity ks j).card

def uniqueColumns {M k L : ℕ} (ks : Fin L → RepairChoices M k) (a : Fin L) :
    Finset (Fin M) := (ks a).val.filter fun j => ¬ 2 ≤ multiplicity ks j

theorem unique_shared_card {M k L : ℕ} (ks : Fin L → RepairChoices M k) (a : Fin L) :
    (uniqueColumns ks a).card + sharedCount ks a = k := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := (ks a).val)
    (fun j => 2 ≤ multiplicity ks j)
  rw [(ks a).property] at h
  dsimp [uniqueColumns, sharedCount]
  omega

theorem uniqueColumns_pairwise {M k L : ℕ} (ks : Fin L → RepairChoices M k) :
    Pairwise fun a b => Disjoint (uniqueColumns ks a) (uniqueColumns ks b) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro j hja hjb
  have ha := Finset.mem_filter.mp hja
  have hb := Finset.mem_filter.mp hjb
  have hsub : ({a, b} : Finset (Fin L)) ⊆ univ.filter (fun i => j ∈ (ks i).val) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [ha.1, hb.1]
  have hcard := Finset.card_le_card hsub
  have hm : 2 ≤ multiplicity ks j := by
    simpa [multiplicity, hab] using hcard
  exact ha.2 hm

theorem card_filter_as_univ_sum {M : ℕ} (S : Finset (Fin M)) (p : Fin M → Prop)
    [DecidablePred p] :
    (S.filter p).card = ∑ j : Fin M, if j ∈ S ∧ p j then 1 else 0 := by
  rw [Finset.sum_boole]
  congr 1
  ext j
  simp

theorem shared_counts_sum {M k L : ℕ} (ks : Fin L → RepairChoices M k) :
    (∑ a, sharedCount ks a) =
      ∑ j : Fin M, if 2 ≤ multiplicity ks j then multiplicity ks j else 0 := by
  simp only [sharedCount, card_filter_as_univ_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 2 ≤ multiplicity ks j
  · simp only [hj, and_true, ite_true]
    simp [multiplicity, Finset.sum_boole]
  · simp [hj]

theorem multiplicity_sum {M k L : ℕ} (ks : Fin L → RepairChoices M k) :
    (∑ j, multiplicity ks j) = L * k := by
  have hm (j : Fin M) : multiplicity ks j =
      ∑ a : Fin L, if j ∈ (ks a).val then 1 else 0 := by
    simp [multiplicity, Finset.sum_boole]
  simp_rw [hm]
  rw [Finset.sum_comm]
  have hcard (a : Fin L) :
      (∑ j : Fin M, if j ∈ (ks a).val then 1 else 0) = k := by
    rw [Finset.sum_boole]
    simpa using (ks a).property
  simp_rw [hcard]
  simp

theorem replicaUnion_card_sum {M k L : ℕ} (ks : Fin L → RepairChoices M k) :
    (replicaUnion ks).card =
      ∑ j : Fin M, if 0 < multiplicity ks j then 1 else 0 := by
  rw [Finset.sum_boole]
  congr 1
  ext j
  simp [replicaUnion, multiplicity, Finset.card_pos, Finset.Nonempty]

theorem shared_counts_le_twice_excess {M k L : ℕ} (ks : Fin L → RepairChoices M k) :
    (∑ a, sharedCount ks a) ≤ 2 * replicaExcess ks := by
  have hpoint (j : Fin M) :
      (if 2 ≤ multiplicity ks j then multiplicity ks j else 0) +
        2 * (if 0 < multiplicity ks j then 1 else 0) ≤ 2 * multiplicity ks j := by
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin M))) => hpoint j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← shared_counts_sum,
    ← replicaUnion_card_sum, multiplicity_sum] at hsum
  have hcard := replicaUnion_card_le ks
  unfold replicaExcess
  omega

end
end SetCover
