import SetCover.NoiseFourier

/-!
The full finite and asymptotic statements of manuscript Lemma 2.2.
`ManuscriptLemma22` is the target proposition proved by
`SetCover.manuscript_lemma22` in `SetCover/Complete.lean`.
The conditional bridge below is one intermediate step of that proof.
-/

namespace SetCover

open scoped BigOperators
open Finset Filter

noncomputable section

def matrixBitMass (k : ℕ) (b : Bool) : ℝ := if b then beta k else q k

def matrixMass {v M : ℕ} (k : ℕ) (A : CheapMatrix v M) : ℝ :=
  ∏ e, ∏ j, matrixBitMass k (A e j)

theorem matrixBitMass_nonneg {k : ℕ} (hk : 8 ≤ k) (b : Bool) :
    0 ≤ matrixBitMass k b := by
  cases b
  · exact le_of_lt (q_pos hk)
  · exact le_of_lt (beta_pos hk)

@[simp] theorem matrixBitMass_sum (k : ℕ) :
    ∑ b : Bool, matrixBitMass k b = 1 := by
  simp [Fintype.sum_bool, matrixBitMass, q]

theorem matrixMass_probability {v M k : ℕ} (hk : 8 ≤ k) :
    IsProbability (matrixMass (v := v) (M := M) k) := by
  constructor
  · intro A
    exact Finset.prod_nonneg fun e _ =>
      Finset.prod_nonneg fun j _ => matrixBitMass_nonneg hk (A e j)
  · unfold matrixMass
    rw [← Fintype.prod_sum (fun (_ : Fin v) (row : Fin M → Bool) =>
      ∏ j, matrixBitMass k (row j))]
    simp only [← Fintype.prod_sum (fun (_ : Fin M) (b : Bool) => matrixBitMass k b),
      matrixBitMass_sum, Finset.prod_const_one]

def eventMass {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ x, if P x then μ x else 0

theorem eventMass_mono {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) {P Q : Ω → Prop} (hPQ : ∀ x, P x → Q x) :
    eventMass μ P ≤ eventMass μ Q := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x
  · simp [hp, hPQ x hp]
  · by_cases hq : Q x <;> simp [hp, hq, hμ x]

def effectiveDimension (k v : ℕ) : ℕ :=
  ⌊(k : ℝ)^2 / (64 * Real.exp 1 * v)⌋₊

def lambda (k M : ℕ) : ℝ := (k : ℝ)^2 / M

def Covers {v M : ℕ} (A : CheapMatrix v M) : Prop :=
  ∀ e, ∃ j, A e j = true

def DensityCertificate {v M : ℕ} (k : ℕ) (A : CheapMatrix v M) : Prop :=
  ∀ f g : Cube v → ℝ, IsDensity f → IsDensity g →
    1 - (lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120)) -
      (120 / (effectiveDimension k v : ℝ)) * (entropy f + entropy g)
        ≤ pairing (noiseMass k A) f g

def Good {v M : ℕ} (k : ℕ) (A : CheapMatrix v M) : Prop :=
  Covers A ∧ DensityCertificate k A

/-- The complete finite conclusion: the actual sampler is a probability law,
all its supported masks are repairable, and one event works for ALL densities. -/
def Lemma22Conclusion (k M v : ℕ) : Prop :=
  (∀ A : CheapMatrix v M,
    IsProbability (noiseMass k A) ∧
      ∀ z, noiseMass k A z ≠ 0 → Repairable k A z) ∧
  (9 / 10 : ℝ) ≤ eventMass (matrixMass k) (Good (v := v) (M := M) k)

/-- The exact asymptotic target proved in `SetCover/Complete.lean`. -/
def ManuscriptLemma22 : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (M v : ℕ → ℕ) (α : ℕ → ℝ),
      (∀ᶠ k in atTop,
        1 ≤ α k ∧ C₀ * (k : ℝ)^2 ≤ M k ∧
        6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k) →
      Asymptotics.IsLittleO atTop (fun k => (v k : ℝ)) (fun k => (k : ℝ)^2) →
      ∀ᶠ k in atTop, Lemma22Conclusion k (M k) (v k)

theorem sampler_part_of_lemma22 {k M v : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M) :
    ∀ A : CheapMatrix v M,
      IsProbability (noiseMass k A) ∧
        ∀ z, noiseMass k A z ≠ 0 → Repairable k A z := by
  intro A
  have hp := noiseMass_probability hk hkM A
  refine ⟨hp, ?_⟩
  intro z hz
  exact noiseMass_repairable hkM A z (lt_of_le_of_ne (hp.1 z) (Ne.symm hz))

def FourierGood {v M : ℕ} (k : ℕ) (A : CheapMatrix v M) : Prop :=
  Covers A ∧ FourierBounds (noiseMass k A) (effectiveDimension k v)
    (lambda k M) (Real.exp (-(effectiveDimension k v : ℝ) / 60))

theorem good_of_fourierGood {v M k : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M)
    (hd : 0 < effectiveDimension k v) (A : CheapMatrix v M)
    (hA : FourierGood k A) : Good k A := by
  refine ⟨hA.1, ?_⟩
  intro f g hf hg
  exact certificate_exp_constants hd (noiseMass_probability hk hkM A) hA.2 hf hg

/-- Conditional reduction. The full proof establishes `hconcentration` from the
short- and long-moment estimates rather than assuming it. -/
theorem lemma22_of_joint_fourier_event {v M k : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M)
    (hd : 0 < effectiveDimension k v)
    (hconcentration :
      (9 / 10 : ℝ) ≤ eventMass (matrixMass k) (FourierGood (v := v) (M := M) k)) :
    Lemma22Conclusion k M v := by
  refine ⟨sampler_part_of_lemma22 hk hkM, ?_⟩
  exact hconcentration.trans
    (eventMass_mono (matrixMass_probability hk).1 (good_of_fourierGood hk hkM hd))

end
end SetCover
