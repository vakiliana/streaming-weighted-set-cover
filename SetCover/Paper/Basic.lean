import SetCover.Complete

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

abbrev Block (v r : ℕ) := Fin r → Cube v
abbrev Input (v r s : ℕ) := Block v r × Block v s
abbrev SetId (M r s : ℕ) := Fin M ⊕ (Fin r ⊕ Fin s)
abbrev Element (v : ℕ) := Fin v × Bool

def vectorAt {v r s : ℕ} (x : Input v r s) : (Fin r ⊕ Fin s) → Cube v :=
  Sum.elim x.1 x.2

def contains {v M r s : ℕ} (A : CheapMatrix v M) (x : Input v r s)
    (i : SetId M r s) (e : Element v) : Prop :=
  match i with
  | Sum.inl j => A e.1 j = true
  | Sum.inr j => vectorAt x j e.1 = e.2

def weight {M r s : ℕ} (k : ℕ) : SetId M r s → ℕ :=
  Sum.elim (fun _ => 1) (fun _ => k)

def cost {M r s : ℕ} (k : ℕ) (F : Finset (SetId M r s)) : ℕ :=
  ∑ i ∈ F, weight k i

def IsCover {v M r s : ℕ} (A : CheapMatrix v M) (x : Input v r s)
    (F : Finset (SetId M r s)) : Prop :=
  ∀ e : Element v, ∃ i ∈ F, contains A x i e

def HasCoverAtMost {v M r s : ℕ} (k : ℕ) (A : CheapMatrix v M)
    (x : Input v r s) (B : ℝ) : Prop :=
  ∃ F : Finset (SetId M r s), IsCover A x F ∧ (cost k F : ℝ) ≤ B

def uniformMass {Ω : Type*} [Fintype Ω] (_ : Ω) : ℝ :=
  1 / Fintype.card Ω

def noMass (v r s : ℕ) : Input v r s → ℝ := uniformMass

/-- The actual planted-pair law, written as its likelihood ratio against NO.
Normalization and the rectangle identity are proved in the communication development. -/
def yesMass {v M : ℕ} (k r s : ℕ) (A : CheapMatrix v M) (x : Input v r s) : ℝ :=
  noMass v r s x *
    average (fun i : Fin r => average (fun j : Fin s =>
      (Fintype.card (Cube v) : ℝ) * noiseMass k A (planted (x.1 i) (x.2 j))))

inductive Protocol (X Y : Type*) where
  | leaf (answer : Bool)
  | alice (message : X → Bool) (zero one : Protocol X Y)
  | bob (message : Y → Bool) (zero one : Protocol X Y)

def Protocol.depth {X Y : Type*} : Protocol X Y → ℕ
  | .leaf _ => 0
  | .alice _ t₀ t₁ => 1 + max t₀.depth t₁.depth
  | .bob _ t₀ t₁ => 1 + max t₀.depth t₁.depth

def Protocol.run {X Y : Type*} : Protocol X Y → X → Y → Bool
  | .leaf b, _, _ => b
  | .alice m t₀ t₁, x, y => if m x then t₁.run x y else t₀.run x y
  | .bob m t₀ t₁, x, y => if m y then t₁.run x y else t₀.run x y

def Protocol.trace {X Y : Type*} : Protocol X Y → X → Y → List Bool
  | .leaf _, _, _ => []
  | .alice m t₀ t₁, x, y =>
      if m x then true :: t₁.trace x y else false :: t₀.trace x y
  | .bob m t₀ t₁, x, y =>
      if m y then true :: t₁.trace x y else false :: t₀.trace x y

def acceptance {v r s : ℕ} (μ : Input v r s → ℝ)
    (p : Protocol (Block v r) (Block v s)) : ℝ :=
  expectation μ (fun x => if p.run x.1 x.2 then 1 else 0)

def randomAcceptance {Ω : Type*} [Fintype Ω] {v r s : ℕ}
    (coins : Ω → ℝ) (p : Ω → Protocol (Block v r) (Block v s))
    (μ : Input v r s → ℝ) : ℝ :=
  expectation coins (fun ω => acceptance μ (p ω))

end
end SetCover.Paper
