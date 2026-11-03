import SetCover.Paper.CommunicationRectangles
import SetCover.Paper.CommunicationProtocols

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

variable {X Y : Type*} [Fintype X] [Fintype Y]

def Protocol.leafMass (p : Protocol X Y) (μ : X × Y → ℝ) : p.Leaf → ℝ :=
  pushMass μ (fun z => p.leafFor z.1 z.2)

theorem Protocol.leafMass_probability (p : Protocol X Y) {μ : X × Y → ℝ}
    (hμ : IsProbability μ) : IsProbability (p.leafMass μ) :=
  pushMass_probability hμ _

theorem Protocol.leafMass_rectangle (p : Protocol X Y) (μ : X × Y → ℝ) (t : p.Leaf) :
    p.leafMass μ t = rectangleMass μ (p.leftFinset t) (p.rightFinset t) := by
  unfold leafMass pushMass rectangleMass eventMass
  apply sum_congr rfl
  intro z _
  simp only [leftFinset, rightFinset, mem_filter, mem_univ, true_and, leafFor_eq_iff]

theorem Protocol.leafMass_entropy_le (p : Protocol X Y) {μ : X × Y → ℝ}
    (hμ : IsProbability μ) {b : ℕ} (hb : p.depth ≤ b) :
    shannon (p.leafMass μ) ≤ (b : ℝ) * Real.log 2 := by
  have hcard : (Fintype.card p.Leaf : ℝ) ≤ (2 : ℝ) ^ b := by
    exact_mod_cast p.card_leaf_le_of_depth hb
  calc
    shannon (p.leafMass μ) ≤ Real.log (Fintype.card p.Leaf) :=
      shannon_le_log_card (p.leafMass_probability hμ)
    _ ≤ Real.log ((2 : ℝ) ^ b) := Real.log_le_log (card_pos (Ω := p.Leaf)) hcard
    _ = (b : ℝ) * Real.log 2 := Real.log_pow _ _

theorem acceptance_eq_leafMass {v r s : ℕ} (μ : Input v r s → ℝ)
    (p : Protocol (Block v r) (Block v s)) :
    acceptance μ p = eventMass (p.leafMass μ) (fun t => p.leafAnswer t = true) := by
  rw [eventMass_eq_expectation]
  unfold Protocol.leafMass
  rw [pushMass_expectation]
  simp only [Protocol.leafAnswer_leafFor, acceptance]

theorem probability_le_one {μ : X → ℝ} (hμ : IsProbability μ) (x : X) :
    μ x ≤ 1 := by
  calc
    μ x ≤ ∑ y, μ y := single_le_sum (fun y _ => hμ.1 y) (mem_univ x)
    _ = 1 := hμ.2

theorem probability_surprisal_nonneg {μ : X → ℝ} (hμ : IsProbability μ) (x : X) :
    0 ≤ μ x * Real.log (1 / μ x) := by
  by_cases hx : μ x = 0
  · simp [hx]
  · have hxpos : 0 < μ x := lt_of_le_of_ne (hμ.1 x) (Ne.symm hx)
    exact mul_nonneg (hμ.1 x)
      (Real.log_nonneg ((one_le_div hxpos).2 (probability_le_one hμ x)))

theorem eventMass_gap_of_rectangle_bounds {p q : X → ℝ}
    (hp : IsProbability p) (hq : IsProbability q) {ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hlower : ∀ x, q x * (1 - ε - C * Real.log (1 / q x)) ≤ p x)
    (P : X → Prop) :
    |eventMass p P - eventMass q P| ≤ ε + C * shannon q := by
  have hpenalty :
      (∑ x, (q x * ε + C * (q x * Real.log (1 / q x)))) = ε + C * shannon q := by
    simp only [one_div, Real.log_inv, mul_neg, sum_add_distrib, ← sum_mul,
      ← mul_sum, sum_neg_distrib, hq.2, one_mul, shannon]
  have hone (Q : X → Prop) :
      eventMass q Q - eventMass p Q ≤ ε + C * shannon q := by
    rw [← hpenalty, eventMass, eventMass, ← sum_sub_distrib]
    apply sum_le_sum
    intro x _
    by_cases hx : Q x
    · simp only [if_pos hx]
      have h := hlower x
      nlinarith
    · simp only [if_neg hx, sub_self]
      exact add_nonneg (mul_nonneg (hq.1 x) hε)
        (mul_nonneg hC (probability_surprisal_nonneg hq x))
  apply abs_le.mpr
  constructor
  · have h := hone P
    linarith
  · have h := hone (fun x => ¬ P x)
    rw [eventMass_compl hq, eventMass_compl hp] at h
    linarith

theorem deterministic_protocol_acceptance_gap {v M k r s b : ℕ}
    (hk : 8 ≤ k) (hkM : k ≤ M) (hd : 0 < effectiveDimension k v)
    (hr : 0 < r) (hs : 0 < s) {A : CheapMatrix v M} (hA : Good k A)
    (p : Protocol (Block v r) (Block v s)) (hb : p.depth ≤ b) :
    |acceptance (yesMass k r s A) p - acceptance (noMass v r s) p| ≤
      communicationError k M v + communicationRate k v r s * ((b : ℝ) * Real.log 2) := by
  have hp := p.leafMass_probability (yesMass_probability hk hkM hr hs A)
  have hq := p.leafMass_probability (noMass_probability v r s)
  have hlower (t : p.Leaf) :
      p.leafMass (noMass v r s) t *
        (1 - communicationError k M v - communicationRate k v r s *
          Real.log (1 / p.leafMass (noMass v r s) t)) ≤ p.leafMass (yesMass k r s A) t := by
    simp only [p.leafMass_rectangle]
    exact rectangle_bound hd hr hs hA _ _
  rw [acceptance_eq_leafMass, acceptance_eq_leafMass]
  exact (eventMass_gap_of_rectangle_bounds hp hq
    (communicationError_nonneg k M v) (communicationRate_nonneg k v r s) hlower _).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left
        (p.leafMass_entropy_le (noMass_probability v r s) hb)
        (communicationRate_nonneg k v r s)) _)

end
end SetCover.Paper
