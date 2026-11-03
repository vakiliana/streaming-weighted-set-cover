import SetCover.UniformSubsets

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section

theorem average_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (e : Ω ≃ Γ) (f : Γ → ℝ) :
    average (fun x => f (e x)) = average f := by
  unfold average
  rw [e.sum_comp, Fintype.card_congr e]

theorem average_pair {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (f : Ω × Γ → ℝ) :
    average f = average (fun x => average (fun y => f (x, y))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

theorem average_comm {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (f : Ω → Γ → ℝ) :
    average (fun x => average (f x)) = average (fun y => average (fun x => f x y)) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem average_fin_cons {Ω : Type*} [Fintype Ω] {L : ℕ}
    (f : (Fin (L + 1) → Ω) → ℝ) :
    average f = average (fun K : Ω => average (fun ks : Fin L → Ω => f (Fin.cons K ks))) := by
  rw [← average_equiv (Fin.consEquiv (fun _ : Fin (L + 1) => Ω)) f, average_pair]
  rfl

def replicaUnion {M k L : ℕ} (ks : Fin L → RepairChoices M k) : Finset (Fin M) :=
  univ.biUnion (fun i => (ks i).val)

def replicaExcess {M k L : ℕ} (ks : Fin L → RepairChoices M k) : ℕ :=
  L * k - (replicaUnion ks).card

theorem replicaUnion_card_le {M k L : ℕ} (ks : Fin L → RepairChoices M k) :
    (replicaUnion ks).card ≤ L * k := by
  calc
    (replicaUnion ks).card ≤ ∑ i : Fin L, (ks i).val.card := Finset.card_biUnion_le
    _ = L * k := by
      have hcard (i : Fin L) : (ks i).val.card = k := (ks i).property
      simp [hcard]

theorem replicaUnion_cons {M k L : ℕ} (K : RepairChoices M k)
    (ks : Fin L → RepairChoices M k) :
    replicaUnion (Fin.cons K ks) = K.val ∪ replicaUnion ks := by
  ext j
  simp [replicaUnion, Fin.exists_fin_succ]

theorem replicaExcess_cons {M k L : ℕ} (K : RepairChoices M k)
    (ks : Fin L → RepairChoices M k) :
    replicaExcess (Fin.cons K ks) =
      replicaExcess ks + (K.val ∩ replicaUnion ks).card := by
  have hu := replicaUnion_card_le ks
  have hi := Finset.card_union_add_card_inter K.val (replicaUnion ks)
  rw [K.property] at hi
  simp only [replicaExcess, replicaUnion_cons, Nat.succ_mul]
  omega

theorem replica_overlap_mgf {M k : ℕ} (hM : 0 < M) (hkM : k ≤ M)
    {z : ℝ} (hz : 1 ≤ z) (L : ℕ) :
    average (fun ks : Fin L → RepairChoices M k => z ^ replicaExcess ks) ≤
      Real.exp (lambda k M * L * (L - 1 : ℝ) / 2 * (z - 1)) := by
  letI := repairChoices_nonempty hkM
  have hz0 : 0 ≤ z := by linarith
  have hzm : 0 ≤ z - 1 := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  induction L with
  | zero =>
      simp [replicaExcess, average_const]
  | succ L ih =>
      have hstep (ks : Fin L → RepairChoices M k) :
          average (fun K : RepairChoices M k => z ^ (K.val ∩ replicaUnion ks).card) ≤
            Real.exp (lambda k M * L * (z - 1)) := by
        have hcard : ((replicaUnion ks).card : ℝ) ≤ L * k := by
          exact_mod_cast replicaUnion_card_le ks
        apply (overlap_mgf_le hM hkM (replicaUnion ks) hz).trans
        apply Real.exp_le_exp.mpr
        unfold lambda
        have hm := mul_le_mul_of_nonneg_left hcard
          (show 0 ≤ (k : ℝ) / M * (z - 1) by positivity)
        convert hm using 1 <;> ring
      calc
        average (fun ks : Fin (L + 1) → RepairChoices M k => z ^ replicaExcess ks)
            = average (fun ks : Fin L → RepairChoices M k =>
                z ^ replicaExcess ks *
                  average (fun K : RepairChoices M k => z ^ (K.val ∩ replicaUnion ks).card)) := by
              rw [average_fin_cons, average_comm]
              simp_rw [replicaExcess_cons, pow_add, average_mul]
        _ ≤ average (fun ks : Fin L → RepairChoices M k =>
              z ^ replicaExcess ks * Real.exp (lambda k M * L * (z - 1))) := by
              apply average_mono
              intro ks
              exact mul_le_mul_of_nonneg_left (hstep ks) (pow_nonneg hz0 _)
        _ = average (fun ks : Fin L → RepairChoices M k => z ^ replicaExcess ks) *
              Real.exp (lambda k M * L * (z - 1)) := average_mul_right _ _
        _ ≤ Real.exp (lambda k M * L * (L - 1 : ℝ) / 2 * (z - 1)) *
              Real.exp (lambda k M * L * (z - 1)) := by
              exact mul_le_mul_of_nonneg_right ih (le_of_lt (Real.exp_pos _))
        _ = Real.exp (lambda k M * (L + 1) * (L + 1 - 1 : ℝ) / 2 * (z - 1)) := by
              rw [← Real.exp_add]
              congr 1
              ring
        _ = _ := by push_cast; ring_nf

end
end SetCover
