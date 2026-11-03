import SetCover.Finite

namespace SetCover

open scoped BigOperators
open Finset

noncomputable section

abbrev Cube (v : ℕ) := Fin v → Bool

def zeroVector {v : ℕ} : Cube v := fun _ => false
def oneVector {v : ℕ} : Cube v := fun _ => true
def xor {v : ℕ} (x y : Cube v) : Cube v := fun i => Bool.xor (x i) (y i)
def planted {v : ℕ} (x z : Cube v) : Cube v := xor oneVector (xor x z)

def bitCharacter (t x : Bool) : ℝ := if t && x then -1 else 1

def character {v : ℕ} (t x : Cube v) : ℝ := ∏ i, bitCharacter (t i) (x i)

def fourier {v : ℕ} (f : Cube v → ℝ) (t : Cube v) : ℝ :=
  average (fun x => f x * character t x)

def noiseFourier {v : ℕ} (μ : Cube v → ℝ) (t : Cube v) : ℝ :=
  ∑ z, μ z * character t z

def pairing {v : ℕ} (μ f g : Cube v → ℝ) : ℝ :=
  average (fun x => ∑ z, μ z * (f x * g (planted x z)))

def IsProbability {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

@[simp] theorem character_zero {v : ℕ} (x : Cube v) :
    character zeroVector x = 1 := by
  simp [character, zeroVector, bitCharacter]

theorem character_comm {v : ℕ} (t x : Cube v) : character t x = character x t := by
  simp [character, bitCharacter, Bool.and_comm]

theorem abs_character {v : ℕ} (t x : Cube v) : |character t x| = 1 := by
  rw [character, Finset.abs_prod]
  have h : ∀ i, |bitCharacter (t i) (x i)| = 1 := by
    intro i
    cases t i <;> cases x i <;> norm_num [bitCharacter]
  simp [h]

theorem character_xor {v : ℕ} (t x y : Cube v) :
    character t (xor x y) = character t x * character t y := by
  rw [character, character, character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change bitCharacter (t i) (Bool.xor (x i) (y i)) =
    bitCharacter (t i) (x i) * bitCharacter (t i) (y i)
  cases t i <;> cases x i <;> cases y i <;> norm_num [bitCharacter]

theorem character_planted {v : ℕ} (t x z : Cube v) :
    character t (planted x z) =
      character t oneVector * character t x * character t z := by
  simp only [planted, character_xor]
  ring

theorem character_orthogonality {v : ℕ} (x y : Cube v) :
    ∑ t : Cube v, character t x * character t y =
      if x = y then (Fintype.card (Cube v) : ℝ) else 0 := by
  classical
  have hbit (a b : Bool) :
      (∑ t : Bool, bitCharacter t a * bitCharacter t b) = if a = b then 2 else 0 := by
    cases a <;> cases b <;> norm_num [bitCharacter, Fintype.sum_bool]
  calc
    ∑ t : Cube v, character t x * character t y
        = ∏ i, ∑ b : Bool, bitCharacter b (x i) * bitCharacter b (y i) := by
          simp only [character, ← Finset.prod_mul_distrib, Fintype.prod_sum]
    _ = ∏ i, if x i = y i then (2 : ℝ) else 0 := by simp_rw [hbit]
    _ = if x = y then (Fintype.card (Cube v) : ℝ) else 0 := by
      by_cases h : x = y
      · subst y
        simp [Cube, Fintype.card_pi, Fintype.card_bool]
      · rw [if_neg h]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
          by_contra hn
          push_neg at hn
          exact h (funext hn)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem fourier_inversion {v : ℕ} (f : Cube v → ℝ) (x : Cube v) :
    ∑ t, fourier f t * character t x = f x := by
  classical
  have hcard : (Fintype.card (Cube v) : ℝ) ≠ 0 :=
    ne_of_gt (card_pos (Ω := Cube v))
  simp only [fourier, average, div_mul_eq_mul_div, ← Finset.sum_div,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, character_orthogonality]
  simp [hcard]

theorem fourier_parseval {v : ℕ} (f g : Cube v → ℝ) :
    ∑ t, fourier f t * fourier g t = average (fun x => f x * g x) := by
  calc
    ∑ t, fourier f t * fourier g t
        = ∑ t, average (fun x => f x * (fourier g t * character t x)) := by
          apply Finset.sum_congr rfl
          intro t _
          change average (fun x => f x * character t x) * fourier g t = _
          rw [← average_mul_right]
          congr 1
          funext x
          ring
    _ = average (fun x => ∑ t, f x * (fourier g t * character t x)) :=
      (average_sum _).symm
    _ = average (fun x => f x * g x) := by
      simp_rw [← Finset.mul_sum, fourier_inversion]

theorem fourier_abs_le {v : ℕ} (f : Cube v → ℝ) (t : Cube v) :
    |fourier f t| ≤ average (fun x => |f x|) := by
  unfold fourier
  simpa only [abs_mul, abs_character, mul_one] using
    abs_average_le (fun x => f x * character t x)

@[simp] theorem fourier_zero {v : ℕ} (f : Cube v → ℝ) :
    fourier f zeroVector = average f := by
  simp [fourier]

@[simp] theorem noiseFourier_zero {v : ℕ} {μ : Cube v → ℝ}
    (hμ : IsProbability μ) : noiseFourier μ zeroVector = 1 := by
  simpa [noiseFourier] using hμ.2

theorem pairing_fourier {v : ℕ} (μ f g : Cube v → ℝ) :
    pairing μ f g = ∑ t, fourier f t * fourier g t *
      character t oneVector * noiseFourier μ t := by
  unfold pairing
  conv_lhs =>
    arg 1
    ext x
    arg 2
    ext z
    rw [← fourier_inversion g (planted x z)]
  simp_rw [Finset.mul_sum, character_planted]
  conv_lhs =>
    arg 1
    ext x
    rw [Finset.sum_comm]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro t _
  calc
    average (fun x => ∑ z, μ z *
        (f x * (fourier g t * (character t oneVector * character t x * character t z))))
        = average (fun x => (f x * character t x) *
            (fourier g t * character t oneVector * noiseFourier μ t)) := by
          congr 1
          funext x
          unfold noiseFourier
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          ring
    _ = fourier f t * fourier g t * character t oneVector * noiseFourier μ t := by
      rw [average_mul_right]
      unfold fourier
      ring

end
end SetCover
