import SetCover.ShortCombinatorics

/-!
The cancellation in the sampler can also be expressed without constructing a
biased Fourier basis: mark four columns, put a centered bit on those columns,
and require every unmarked column to be zero.
-/

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

def shortCenteredBit (k : ℕ) (b : Bool) : ℝ :=
  if b then -q k / beta k else 1

def shortZeroBit (b : Bool) : ℝ := if b then 0 else 1

def shortMarkedBit {M : ℕ} (k : ℕ) (K S : Finset (Fin M))
    (i : Fin M) (b : Bool) : ℝ :=
  if i ∈ K then
    if i ∈ S then shortCenteredBit k b else shortZeroBit b
  else 1

def shortMarked {M : ℕ} (k : ℕ) (K S : Finset (Fin M))
    (row : Fin M → Bool) : ℝ :=
  ∏ i, shortMarkedBit k K S i (row i)

theorem shortMarked_eq {M : ℕ} (k : ℕ) (K S : Finset (Fin M))
    (row : Fin M → Bool) :
    shortMarked k K S row =
      if K.filter (fun i => row i = true) ⊆ S then
        (-q k / beta k) ^ (K.filter (fun i => row i = true)).card
      else 0 := by
  rw [shortMarked]
  simp only [shortMarkedBit, Fintype.prod_ite_mem]
  by_cases h : K.filter (fun i => row i = true) ⊆ S
  · rw [if_pos h]
    calc
      (∏ i ∈ K, if i ∈ S then shortCenteredBit k (row i) else shortZeroBit (row i)) =
          ∏ i ∈ K, if row i = true then (-q k / beta k) else 1 := by
            apply Finset.prod_congr rfl
            intro i hi
            cases hb : row i
            · simp [shortCenteredBit, shortZeroBit]
            · have hiS := h (Finset.mem_filter.mpr ⟨hi, hb⟩)
              simp [hiS, shortCenteredBit]
      _ = _ := by rw [← Finset.prod_filter, Finset.prod_const]
  · rw [if_neg h]
    obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp h
    have hi' := Finset.mem_filter.mp hi
    apply Finset.prod_eq_zero hi'.1
    simp [hiS, hi'.2, shortZeroBit]

theorem short_bias_choose {k c : ℕ} (hk : 8 ≤ k) (hc : c ≤ 4) :
    (Nat.choose k 4 : ℝ) * bias k c =
      (-q k / beta k) ^ c * Nat.choose (k - c) (4 - c) := by
  have hck : c ≤ k := by omega
  have hb : beta k ≠ 0 := ne_of_gt (beta_pos hk)
  have hq : q k ≠ 0 := ne_of_gt (q_pos hk)
  have hcK : (Nat.choose k c : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.choose_pos hck)
  have hchoose := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.choose_mul (show 4 ≤ k by omega) hc)
  push_cast at hchoose
  simp only [bias, if_pos hc, div_pow]
  field_simp
  rw [neg_pow (q k)]
  linear_combination ((-1 : ℝ) ^ c * q k ^ c * beta k ^ c) * hchoose

theorem short_bias_marked {M k : ℕ} (hk : 8 ≤ k)
    (K : Finset (Fin M)) (hK : K.card = k) (row : Fin M → Bool) :
    bias k (K.filter (fun i => row i = true)).card =
      (∑ S ∈ K.powersetCard 4, shortMarked k K S row) / Nat.choose k 4 := by
  let C := K.filter (fun i => row i = true)
  have hCK : C ⊆ K := Finset.filter_subset _ _
  have hcK : (Nat.choose k 4 : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.choose_pos (show 4 ≤ k by omega))
  apply (eq_div_iff hcK).mpr
  by_cases hc : C.card ≤ 4
  · have hsum : (∑ S ∈ K.powersetCard 4, shortMarked k K S row) =
        (-q k / beta k) ^ C.card *
          (((K.powersetCard 4).filter (C ⊆ ·)).card : ℝ) := by
      simp_rw [shortMarked_eq]
      change (∑ S ∈ K.powersetCard 4,
        if C ⊆ S then (-q k / beta k) ^ C.card else 0) = _
      rw [← Finset.sum_filter]
      simp [mul_comm]
    rw [hsum, short_supersets_card K C hCK hc, hK]
    simpa [mul_comm, C] using short_bias_choose hk hc
  · have hnone (S : Finset (Fin M)) (hS : S ∈ K.powersetCard 4) : ¬ C ⊆ S := by
      intro hCS
      have h := Finset.card_le_card hCS
      rw [(Finset.mem_powersetCard.mp hS).2] at h
      exact hc h
    have hz : (∑ S ∈ K.powersetCard 4, shortMarked k K S row) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      simp only [shortMarked_eq, C, if_neg (hnone S hS)]
    rw [hz]
    simp [bias, show ¬ (K.filter (fun i => row i = true)).card ≤ 4 from hc]

theorem short_row_product {M : ℕ} (k : ℕ) (f : Fin M → Bool → ℝ) :
    expectation (rowMass k) (fun row => ∏ i, f i (row i)) =
      ∏ i, ∑ b : Bool, matrixBitMass k b * f i b := by
  simp only [expectation, rowMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin M) (b : Bool) => matrixBitMass k b * f i b)).symm

theorem short_centered_mean {k : ℕ} (hk : 8 ≤ k) :
    (∑ b : Bool, matrixBitMass k b * shortCenteredBit k b) = 0 := by
  have hb : beta k ≠ 0 := ne_of_gt (beta_pos hk)
  simp only [Fintype.sum_bool, matrixBitMass, shortCenteredBit, Bool.false_eq_true,
    if_false, Bool.true_eq, if_true, mul_one]
  field_simp
  ring

theorem short_marked_cross_zero {M k : ℕ} (hk : 8 ≤ k)
    (K L S T : Finset (Fin M)) (hSK : S ⊆ K) (hSL : ¬ S ⊆ L) :
    expectation (rowMass k) (fun row => shortMarked k K S row * shortMarked k L T row) = 0 := by
  simp only [shortMarked, ← Finset.prod_mul_distrib]
  rw [short_row_product k
    (fun i b => shortMarkedBit k K S i b * shortMarkedBit k L T i b)]
  obtain ⟨i, hiS, hiL⟩ := Finset.not_subset.mp hSL
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [shortMarkedBit, hSK hiS, hiS, hiL] using short_centered_mean hk

theorem short_marked_cross {M k : ℕ} (hk : 8 ≤ k)
    (K L S T : Finset (Fin M)) (hSK : S ⊆ K) (hTL : T ⊆ L)
    (hSL : S ⊆ L) (hTK : T ⊆ K) :
    expectation (rowMass k) (fun row => shortMarked k K S row * shortMarked k L T row) =
      q k ^ (K ∪ L).card * ∏ i ∈ T, (if i ∈ S then (beta k)⁻¹ else 1) := by
  have hb : beta k ≠ 0 := ne_of_gt (beta_pos hk)
  have hbq : beta k + q k = 1 := by simp [q]
  simp only [shortMarked, ← Finset.prod_mul_distrib]
  rw [short_row_product k
    (fun i b => shortMarkedBit k K S i b * shortMarkedBit k L T i b)]
  have hbit (i : Fin M) :
      (∑ b : Bool, matrixBitMass k b *
        (shortMarkedBit k K S i b * shortMarkedBit k L T i b)) =
      (if i ∈ K ∪ L then q k else 1) *
        (if i ∈ T then (if i ∈ S then (beta k)⁻¹ else 1) else 1) := by
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
    · have hiK := hSK hiS
      have hiL := hTL hiT
      simp only [Fintype.sum_bool, matrixBitMass, shortMarkedBit, if_pos hiK,
        if_pos hiL, if_pos hiS, if_pos hiT, shortCenteredBit, Bool.false_eq_true,
        if_false, Bool.true_eq, if_true, mul_one]
      simp only [Finset.mem_union, hiK, hiL, or_self, if_true]
      field_simp
      linear_combination (q k * beta k ^ 2) * hbq
    · have hiK := hSK hiS
      have hiL := hSL hiS
      simp [Fintype.sum_bool, matrixBitMass, shortMarkedBit, shortCenteredBit,
        shortZeroBit, hiK, hiL, hiS, hiT]
    · have hiK := hTK hiT
      have hiL := hTL hiT
      simp [Fintype.sum_bool, matrixBitMass, shortMarkedBit, shortCenteredBit,
        shortZeroBit, hiK, hiL, hiS, hiT]
    · by_cases hiK : i ∈ K <;> by_cases hiL : i ∈ L <;>
        simp [Fintype.sum_bool, matrixBitMass, shortMarkedBit, shortZeroBit,
          hiK, hiL, hiS, hiT, hbq]
  simp_rw [hbit]
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Fintype.prod_ite_mem]
  simp

end
end SetCover
