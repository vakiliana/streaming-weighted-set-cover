import SetCover.BernoulliCounts

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

def supportCount {ι : Type*} (S : Finset ι) (x : ι → Bool) : ℕ :=
  (S.filter fun i => x i = true).card

def binomialExpectation (k n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ c ∈ range (n + 1), (Nat.choose n c : ℝ) *
    beta k ^ c * q k ^ (n - c) * f c

def blockOwner {ι κ : Type*} (S : κ → Finset ι) (i : ι) : Option κ :=
  if h : ∃ a, i ∈ S a then some (Classical.choose h) else none

theorem blockOwner_eq_some {ι κ : Type*} {S : κ → Finset ι}
    (hS : Pairwise fun a b => Disjoint (S a) (S b)) (a : κ) (i : ι) :
    blockOwner S i = some a ↔ i ∈ S a := by
  by_cases h : ∃ b, i ∈ S b
  · have hc := Classical.choose_spec h
    have huniq : i ∈ S a → Classical.choose h = a := by
      intro ha
      by_contra hn
      exact Finset.disjoint_left.mp (hS hn) hc ha
    simp only [blockOwner, dif_pos h, Option.some.injEq]
    exact ⟨fun he => he ▸ hc, huniq⟩
  · simp only [blockOwner, dif_neg h, reduceCtorEq, false_iff]
    exact fun hi => h ⟨a, hi⟩

theorem count_fiber {ι κ : Type*} [Fintype ι] [DecidableEq κ] (owner : ι → κ) (a : κ)
    (S : Finset ι) (hS : ∀ i, i ∈ S ↔ owner i = a) (x : ι → Bool) :
    (bitSupport (fun j : {i : ι // owner i = a} => x j.val)).card =
      supportCount S x := by
  have hs := Finset.sum_subtype (F := inferInstance) S hS
    (fun i => if x i = true then (1 : ℕ) else 0)
  have hb := Finset.sum_boole (α := ℕ) (fun j : {i : ι // owner i = a} => x j.val = true)
    (univ : Finset {i : ι // owner i = a})
  simp only [Nat.cast_id] at hb
  unfold bitSupport supportCount
  rw [← hb, ← hs, Finset.sum_boole]
  simp only [Nat.cast_id]

theorem card_fiber {ι κ : Type*} [Fintype ι] [DecidableEq κ] (owner : ι → κ) (a : κ)
    (S : Finset ι) (hS : ∀ i, i ∈ S ↔ owner i = a) :
    Fintype.card {i : ι // owner i = a} = S.card := by
  rw [Fintype.subtype_card]
  congr 1
  ext i
  simp [← hS i]

theorem iidExpectation_disjoint_counts {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (S : κ → Finset ι) (hS : Pairwise fun a b => Disjoint (S a) (S b))
    (f : κ → ℕ → ℝ) :
    iidExpectation k (fun x : ι → Bool => ∏ a, f a (supportCount (S a) x)) =
      ∏ a, binomialExpectation k (S a).card (f a) := by
  let owner := blockOwner S
  let F : (o : Option κ) → ({i : ι // owner i = o} → Bool) → ℝ :=
    fun o x => match o with
      | none => 1
      | some a => f a (bitSupport x).card
  have hp := iidExpectation_partition k owner F
  have hlhs :
      (fun x : ι → Bool => ∏ a, f a (supportCount (S a) x)) =
      (fun x : ι → Bool => ∏ o : Option κ, F o (fun i => x i.val)) := by
    funext x
    simp only [Fintype.prod_option, F, one_mul]
    apply Finset.prod_congr rfl
    intro a _
    congr 1
    exact (count_fiber owner (some a) (S a)
      (fun i => (blockOwner_eq_some hS a i).symm) x).symm
  rw [hlhs, hp]
  simp only [Fintype.prod_option, F, iidExpectation_one, one_mul]
  apply Finset.prod_congr rfl
  intro a _
  have hcount := iidExpectation_count (ι := {i : ι // owner i = some a}) k (f a)
  rw [card_fiber owner (some a) (S a) (fun i => (blockOwner_eq_some hS a i).symm)] at hcount
  convert hcount using 1
  congr 1
  exact Subsingleton.elim _ _

end
end SetCover
