import SetCover.Paper.Streaming

namespace SetCover.Paper

open scoped BigOperators
open Finset MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Measurability of the finite behavior induced by a random seed.
No finiteness, discreteness, or uniformity assumption is made on the seed space. -/
def SeedMeasurable {Ω B : Type*} [MeasurableSpace Ω] (code : Ω → B) : Prop :=
  ∀ b, MeasurableSet {ω | code ω = b}

def seedMass {Ω B : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → B) (b : B) : ℝ :=
  μ.real {ω | code ω = b}

theorem seedMass_probability {Ω B : Type*} [MeasurableSpace Ω] [Fintype B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (code : Ω → B)
    (hcode : SeedMeasurable code) : IsProbability (seedMass μ code) := by
  constructor
  · intro b
    exact measureReal_nonneg
  · have h := sum_measureReal_preimage_singleton (μ := μ) (univ : Finset B)
      (f := code) (fun b _ => hcode b)
    simpa [seedMass] using h

theorem seedMass_event {Ω B : Type*} [MeasurableSpace Ω] [Fintype B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (code : Ω → B)
    (hcode : SeedMeasurable code) (P : B → Prop) :
    eventMass (seedMass μ code) P = μ.real {ω | P (code ω)} := by
  unfold eventMass seedMass
  rw [← Finset.sum_filter]
  have h := sum_measureReal_preimage_singleton (μ := μ) (univ.filter P)
    (f := code) (fun b _ => hcode b)
  simpa using h

def thresholdMachine {p S v r s : ℕ} (T : ℝ)
    (m : StreamingMachine p S v r s ℝ) : StreamingMachine p S v r s Bool :=
  m.mapOutput (fun z => decide (z ≤ T))

@[simp] theorem thresholdMachine_run {p S v r s : ℕ} (T : ℝ)
    (m : StreamingMachine p S v r s ℝ) (x : Input v r s) :
    (thresholdMachine T m).run x = decide (m.run x ≤ T) := rfl

def machineAcceptance {p S v r s : ℕ}
    (coins : StreamingMachine p S v r s Bool → ℝ) (x : Input v r s) : ℝ :=
  eventMass coins (fun m => m.run x = true)

theorem threshold_acceptance {Ω : Type*} [MeasurableSpace Ω]
    {p S v r s : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (code : Ω → StreamingMachine p S v r s ℝ) (T : ℝ)
    (hcode : SeedMeasurable (fun ω => thresholdMachine T (code ω))) (x : Input v r s) :
    machineAcceptance (seedMass μ (fun ω => thresholdMachine T (code ω))) x =
      μ.real {ω | (code ω).run x ≤ T} := by
  unfold machineAcceptance
  rw [seedMass_event μ _ hcode]
  simp

theorem machineAcceptance_bounds {p S v r s : ℕ}
    {coins : StreamingMachine p S v r s Bool → ℝ} (hcoins : IsProbability coins)
    (x : Input v r s) : 0 ≤ machineAcceptance coins x ∧ machineAcceptance coins x ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro m _
    split_ifs
    · exact hcoins.1 m
    · exact le_rfl
  · have hm := eventMass_mono hcoins.1
      (P := fun m => m.run x = true) (Q := fun _ => True) (fun _ _ => trivial)
    have ht : eventMass coins (fun _ => True) = 1 := by simp [eventMass, hcoins.2]
    exact hm.trans_eq ht

theorem machine_protocol_acceptance {p S v r s : ℕ}
    (coins : StreamingMachine p S v r s Bool → ℝ) (law : Input v r s → ℝ) :
    randomAcceptance coins (fun m => m.protocol id) law =
      expectation law (machineAcceptance coins) := by
  unfold randomAcceptance acceptance machineAcceptance expectation eventMass
  simp_rw [StreamingMachine.protocol_run]
  simp only [id_eq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : m.run x = true <;> simp [h, mul_comm]

end
end SetCover.Paper
