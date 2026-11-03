import SetCover.Paper.CoverGap
import SetCover.Paper.Randomness
import SetCover.Paper.KnownPrefix

namespace SetCover.Paper

open Filter MeasureTheory

universe u
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Pointwise estimator correctness on every input over the fixed covering cheap family. -/
def EstimatesKnown {Ω : Type u} [MeasurableSpace Ω]
    {p S v M r s : ℕ} (μ : Measure Ω)
    (code : Ω → StreamingMachine p S v r s ℝ)
    (k : ℕ) (A : CheapMatrix v M) (hA : Covers A) (α : ℝ) : Prop :=
  ∀ x : Input v r s, (2 / 3 : ℝ) ≤ μ.real
    {ω | (optimum k A x hA : ℝ) ≤ (code ω).run x ∧
      (code ω).run x ≤ α * (optimum k A x hA : ℝ)}

def EstimatesFull {Ω : Type u} [MeasurableSpace Ω]
    {p S v M r s : ℕ} (μ : Measure Ω)
    (code : Ω → FullMachine p S v M r s ℝ)
    (k : ℕ) (A : CheapMatrix v M) (hA : Covers A) (hs : 0 < s) (α : ℝ) : Prop :=
  ∀ x : Input v r s, (2 / 3 : ℝ) ≤ μ.real
    {ω | (optimum k A x hA : ℝ) ≤ (code ω).run k A hs x ∧
      (code ω).run k A hs x ≤ α * (optimum k A x hA : ℝ)}

def KnownCheapMainConclusion (c : ℝ) (k M v : ℕ) (α : ℝ) : Prop :=
  let r := M / 2
  let s := M - r
  ∃ A : CheapMatrix v M, ∃ hA : Covers A,
    ∀ (p S : ℕ), 0 < p →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (code : Ω → StreamingMachine p S v r s ℝ),
        SeedMeasurable (fun ω => thresholdMachine (3 * α * k) (code ω)) →
        EstimatesKnown μ code k A hA α →
        c * ((2 * M : ℕ) : ℝ) * (k : ℝ)^2 / ((2 * v : ℕ) : ℝ) ≤ (p : ℝ) * S

/-- The literal full-stream conclusion. Only the usual parameter, measurability,
probability normalization, and estimator-correctness conditions are hypotheses. -/
def MainConclusion (c : ℝ) (k M v : ℕ) (α : ℝ) : Prop :=
  let r := M / 2
  let s := M - r
  ∃ hs : 0 < s, ∃ A : CheapMatrix v M, ∃ hA : Covers A,
    ∀ (p S : ℕ), 0 < p →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (code : Ω → FullMachine p S v M r s ℝ),
        SeedMeasurable (fun ω =>
          thresholdMachine (3 * α * k) ((code ω).withKnownCheap k A hs)) →
        EstimatesFull μ code k A hA hs α →
        c * ((2 * M : ℕ) : ℝ) * (k : ℝ)^2 / ((2 * v : ℕ) : ℝ) ≤ (p : ℝ) * S

/-- Version 17, Theorem `thm:main`, for arbitrary random-seed probability spaces. -/
def ManuscriptMainTheorem : Prop :=
  ∃ C₀ c : ℝ, 0 < C₀ ∧ 0 < c ∧
    ∀ (M v : ℕ → ℕ) (α : ℕ → ℝ),
      (∀ᶠ k in atTop,
        1 ≤ α k ∧ C₀ * (k : ℝ)^2 ≤ M k ∧
        6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k) →
      Asymptotics.IsLittleO atTop (fun k => (v k : ℝ)) (fun k => (k : ℝ)^2) →
      ∀ᶠ k in atTop, MainConclusion.{u} c k (M k) (v k) (α k)

theorem full_conclusion_of_known {c α : ℝ} {k M v : ℕ}
    (hs : 0 < M - M / 2) (h : KnownCheapMainConclusion.{u} c k M v α) :
    MainConclusion.{u} c k M v α := by
  obtain ⟨A, hA, hbound⟩ := h
  refine ⟨hs, A, hA, ?_⟩
  intro p S hp Ω _ μ _ code hmeas hcorrect
  apply hbound p S hp Ω μ (fun ω => (code ω).withKnownCheap k A hs) hmeas
  intro x
  simpa only [FullMachine.knownCheap_run] using hcorrect x

end
end SetCover.Paper
