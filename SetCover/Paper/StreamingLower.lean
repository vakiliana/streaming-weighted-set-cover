import SetCover.Paper.Acceptance
import SetCover.Paper.Communication

namespace SetCover.Paper

open scoped BigOperators
open Finset MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- A finite-parameter assembly lemma. The cover-gap hypotheses below are
proved from the hard instance before applying this lemma in the main theorem. -/
theorem streaming_gap_lower_bound {p S v M k r s : ℕ} {α : ℝ}
    (hk : 8 ≤ k) (hkM : k ≤ M) (hd : 0 < effectiveDimension k v)
    (hr : 0 < r) (hs : 0 < s) {A : CheapMatrix v M} (hA : Good k A)
    (hν₀ : IsProbability (noMass v r s)) (hν₁ : IsProbability (yesMass k r s A))
    (hyesSupport : ∀ x, yesMass k r s A x ≠ 0 → HasCoverAtMost k A x (3 * k))
    (hbad : eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k)) ≤ 1 / 12)
    (hε : lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120) ≤ 1 / 12)
    (hbalance : (M : ℝ) ≤ 3 * (min r s : ℕ))
    (hlarge : (4320 : ℝ) ≤ (effectiveDimension k v : ℝ) * M)
    (coins : StreamingMachine p S v r s Bool → ℝ) (hcoins : IsProbability coins)
    (hyes : ∀ x, HasCoverAtMost k A x (3 * k) →
      (2 / 3 : ℝ) ≤ machineAcceptance coins x)
    (hno : ∀ x, ¬ HasCoverAtMost k A x (3 * α * k) →
      machineAcceptance coins x ≤ (1 / 3 : ℝ)) :
    (effectiveDimension k v : ℝ) * M / 8640 ≤ (p : ℝ) * S := by
  have hg := acceptance_gap_from_correctness hν₀ hν₁ hyesSupport hyes hno
    (fun x => (machineAcceptance_bounds hcoins x).2) hbad
  have hc := randomized_protocol_acceptance_gap hk hkM hd hr hs hA
    coins hcoins (fun m => m.protocol id) (fun m => m.protocol_depth id)
  rw [machine_protocol_acceptance, machine_protocol_acceptance] at hc
  have hgap := hg.trans ((le_abs_self _).trans hc)
  apply work_lower_of_communication_gap (d := effectiveDimension k v) (M := M)
    (t := (min r s : ℕ)) (b := (2 * p * S + 1 : ℕ))
    (ε := lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120))
  · exact_mod_cast hd
  · exact_mod_cast lt_min hr hs
  · positivity
  · exact hε
  · exact hbalance
  · exact hlarge
  · push_cast
    ring_nf
    exact le_rfl
  · exact hgap

theorem streaming_main_scale_bound {p S v M k r s : ℕ} {α : ℝ}
    (hk : 8 ≤ k) (hkM : k ≤ M) (hv : 0 < v) (hd : 0 < effectiveDimension k v)
    (hr : 0 < r) (hs : 0 < s) {A : CheapMatrix v M} (hA : Good k A)
    (hν₀ : IsProbability (noMass v r s)) (hν₁ : IsProbability (yesMass k r s A))
    (hyesSupport : ∀ x, yesMass k r s A x ≠ 0 → HasCoverAtMost k A x (3 * k))
    (hbad : eventMass (noMass v r s) (fun x => HasCoverAtMost k A x (3 * α * k)) ≤ 1 / 12)
    (hε : lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120) ≤ 1 / 12)
    (hbalance : (M : ℝ) ≤ 3 * (min r s : ℕ))
    (hlarge : (4320 : ℝ) ≤ (effectiveDimension k v : ℝ) * M)
    (coins : StreamingMachine p S v r s Bool → ℝ) (hcoins : IsProbability coins)
    (hyes : ∀ x, HasCoverAtMost k A x (3 * k) →
      (2 / 3 : ℝ) ≤ machineAcceptance coins x)
    (hno : ∀ x, ¬ HasCoverAtMost k A x (3 * α * k) →
      machineAcceptance coins x ≤ (1 / 3 : ℝ)) :
    (1 / 4000000 : ℝ) * ((2 * M : ℕ) : ℝ) * (k : ℝ)^2 /
      ((2 * v : ℕ) : ℝ) ≤ (p : ℝ) * S := by
  apply work_lower_main_scale hv hd (by positivity)
  exact streaming_gap_lower_bound hk hkM hd hr hs hA hν₀ hν₁
    hyesSupport hbad hε hbalance hlarge coins hcoins hyes hno

end
end SetCover.Paper
