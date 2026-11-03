import SetCover.Paper.EntropyConditioning

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

variable {X Y ι : Type*} [Fintype X] [Fintype Y] [Fintype ι]

theorem expectation_average (μ : X → ℝ) (f : ι → X → ℝ) :
    expectation μ (fun x => average (fun i => f i x)) =
      average (fun i => expectation μ (f i)) := by
  simp only [expectation, average, ← mul_div_assoc, mul_sum, ← sum_div]
  rw [sum_comm]

theorem expectation_mul (μ : X → ℝ) (c : ℝ) (f : X → ℝ) :
    expectation μ (fun x => c * f x) = c * expectation μ f := by
  simp only [expectation, mul_left_comm (μ _) c, ← mul_sum]

theorem expectation_congr (μ : X → ℝ) {f g : X → ℝ} (h : ∀ x, f x = g x) :
    expectation μ f = expectation μ g := by
  congr 1
  exact funext h

theorem average_coordinate [Nonempty X] {r : ℕ} (i : Fin r) (f : X → ℝ) :
    average (fun x : Fin r → X => f (x i)) = average f := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      rw [average_fin_cons]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, average_const]
      · simp only [Fin.cons_succ, ih, average_const]

theorem uniformMass_prod (x : X) (y : Y) :
    uniformMass (x, y) = uniformMass x * uniformMass y := by
  simp [uniformMass, Fintype.card_prod, Nat.cast_mul, one_div, mul_inv]
  ring

def rectangleMass (μ : X × Y → ℝ) (R : Finset X) (T : Finset Y) : ℝ :=
  eventMass μ (fun z => z.1 ∈ R ∧ z.2 ∈ T)

theorem rectangle_tilt [Nonempty X] [Nonempty Y]
    (R : Finset X) (T : Finset Y) (L : X × Y → ℝ) :
    rectangleMass (fun z => uniformMass z * L z) R T =
      uniformEvent R * uniformEvent T *
        expectation (uniformOnMass R) (fun x =>
          expectation (uniformOnMass T) (fun y => L (x, y))) := by
  calc
    rectangleMass (fun z => uniformMass z * L z) R T =
        ∑ x, ∑ y, (if x ∈ R then uniformMass x else 0) *
          (if y ∈ T then uniformMass y else 0) * L (x, y) := by
      unfold rectangleMass eventMass
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      by_cases hx : x ∈ R <;> by_cases hy : y ∈ T <;>
        simp [hx, hy, uniformMass_prod]
    _ = ∑ x, ∑ y, (uniformEvent R * uniformEvent T) *
          (uniformOnMass R x * (uniformOnMass T y * L (x, y))) := by
      simp_rw [← uniformEvent_mul_uniformOnMass]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      ring
    _ = _ := by
      simp only [expectation, mul_sum]

theorem rectangle_uniform [Nonempty X] [Nonempty Y] (R : Finset X) (T : Finset Y) :
    rectangleMass uniformMass R T = uniformEvent R * uniformEvent T := by
  have he : (fun z : X × Y => z.1 ∈ R ∧ z.2 ∈ T) =
      (fun z => z ∈ R ×ˢ T) := by
    funext z
    exact propext mem_product.symm
  rw [rectangleMass, he, eventMass_uniform]
  simp only [uniformEvent, card_product, Fintype.card_prod, Nat.cast_mul]
  rw [div_mul_div_comm]

theorem planted_involutive {v : ℕ} (x : Cube v) :
    Function.Involutive (planted x) := by
  intro y
  funext e
  cases hx : x e <;> cases hy : y e <;> simp [planted, xor, oneVector, hx, hy]

def plantedEquiv {v : ℕ} (x : Cube v) : Cube v ≃ Cube v :=
  (planted_involutive x).toPerm

theorem average_planted {v : ℕ} (x : Cube v) (f : Cube v → ℝ) :
    average (fun y => f (planted x y)) = average f :=
  average_equiv (plantedEquiv x) f

def pairKernel {v : ℕ} (μ : Cube v → ℝ) (x y : Cube v) : ℝ :=
  Fintype.card (Cube v) * μ (planted x y)

theorem average_pairKernel {v : ℕ} {μ : Cube v → ℝ} (hμ : IsProbability μ)
    (x : Cube v) : average (pairKernel μ x) = 1 := by
  unfold pairKernel
  rw [average_mul, average_planted]
  simp [average, hμ.2, ne_of_gt (card_pos (Ω := Cube v))]

theorem pairing_kernel {v : ℕ} (μ f g : Cube v → ℝ) :
    average (fun x => average (fun y => f x * g y * pairKernel μ x y)) =
      pairing μ f g := by
  unfold pairing
  congr 1
  funext x
  rw [← average_equiv (plantedEquiv x)]
  have he (z : Cube v) :
      f x * g (plantedEquiv x z) * pairKernel μ x (plantedEquiv x z) =
        (Fintype.card (Cube v) : ℝ) * (μ z * (f x * g (planted x z))) := by
    change f x * g (planted x z) *
      ((Fintype.card (Cube v) : ℝ) * μ (planted x (planted x z))) = _
    rw [planted_involutive x z]
    ring
  simp_rw [he]
  rw [average_mul]
  unfold average
  field_simp

theorem density_expectation [Nonempty X] (μ f : X → ℝ) :
    expectation μ f = average (fun x => massDensity μ x * f x) := by
  simp only [expectation, average, massDensity, mul_assoc, ← mul_sum]
  field_simp

theorem pairing_massDensity {v : ℕ} (μ a b : Cube v → ℝ) :
    expectation a (fun x => expectation b (fun y => pairKernel μ x y)) =
      pairing μ (massDensity a) (massDensity b) := by
  rw [density_expectation]
  simp_rw [density_expectation b, ← average_mul]
  have he :
      (fun x => average (fun y => massDensity a x *
        (massDensity b y * pairKernel μ x y))) =
      (fun x => average (fun y => massDensity a x *
        massDensity b y * pairKernel μ x y)) := by
    funext x
    congr 1
    funext y
    ring
  rw [he, pairing_kernel]

theorem pairing_average_left {v : ℕ} (μ : Cube v → ℝ)
    (f : ι → Cube v → ℝ) (g : Cube v → ℝ) :
    pairing μ (fun x => average (fun i => f i x)) g =
      average (fun i => pairing μ (f i) g) := by
  unfold pairing
  simp_rw [← average_mul_right, ← average_mul, ← average_sum]
  exact average_average_comm _

theorem pairing_average_right {v : ℕ} (μ f : Cube v → ℝ)
    (g : ι → Cube v → ℝ) :
    pairing μ f (fun x => average (fun i => g i x)) =
      average (fun i => pairing μ f (g i)) := by
  unfold pairing
  simp_rw [← average_mul, ← average_sum]
  exact average_average_comm _

theorem noMass_probability (v r s : ℕ) : IsProbability (noMass v r s) :=
  uniformMass_probability

theorem yesMass_probability {v M k r s : ℕ} (hk : 8 ≤ k) (hkM : k ≤ M)
    (hr : 0 < r) (hs : 0 < s) (A : CheapMatrix v M) :
    IsProbability (yesMass k r s A) := by
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  letI : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp hs
  have hμ := noiseMass_probability hk hkM A
  constructor
  · intro x
    unfold yesMass
    exact mul_nonneg ((noMass_probability v r s).1 x)
      (average_nonneg fun i => average_nonneg fun j =>
        mul_nonneg (Nat.cast_nonneg _) (hμ.1 _))
  · change expectation uniformMass
      (fun x : Input v r s => average (fun i : Fin r => average (fun j : Fin s =>
        pairKernel (noiseMass k A) (x.1 i) (x.2 j)))) = 1
    rw [expectation_uniform, average_pair]
    have hy (x : Block v r) :
        average (fun y : Block v s => average (fun i : Fin r =>
          average (fun j : Fin s => pairKernel (noiseMass k A) (x i) (y j)))) = 1 := by
      rw [average_average_comm]
      have hi (i : Fin r) :
          average (fun y : Block v s =>
            average (fun j : Fin s => pairKernel (noiseMass k A) (x i) (y j))) = 1 := by
        rw [average_average_comm]
        simp only [average_coordinate, average_pairKernel hμ, average_const]
      simp only [hi, average_const]
    simp only [hy, average_const]

theorem rectangle_yesMass_identity {v M k r s : ℕ}
    (A : CheapMatrix v M) (R : Finset (Block v r)) (T : Finset (Block v s)) :
    rectangleMass (yesMass k r s A) R T =
      uniformEvent R * uniformEvent T *
        pairing (noiseMass k A) (meanDensity R) (meanDensity T) := by
  rw [show yesMass k r s A =
    (fun z : Input v r s => uniformMass z *
      average (fun i : Fin r => average (fun j : Fin s =>
        pairKernel (noiseMass k A) (z.1 i) (z.2 j)))) from rfl, rectangle_tilt]
  congr 1
  have he (i : Fin r) (j : Fin s) :
      expectation (uniformOnMass R) (fun x =>
        expectation (uniformOnMass T) (fun y =>
          pairKernel (noiseMass k A) (x i) (y j))) =
        pairing (noiseMass k A) (conditionalDensity R i) (conditionalDensity T j) := by
    have hT (x : Block v r) :
        expectation (uniformOnMass T) (fun y =>
          pairKernel (noiseMass k A) (x i) (y j)) =
        expectation (marginalMass (uniformOnMass T) j)
          (pairKernel (noiseMass k A) (x i)) :=
      (marginalMass_expectation (uniformOnMass T) j
        (pairKernel (noiseMass k A) (x i))).symm
    simp_rw [hT]
    rw [← marginalMass_expectation (uniformOnMass R) i
      (fun a => expectation (marginalMass (uniformOnMass T) j)
        (pairKernel (noiseMass k A) a)), pairing_massDensity]
    rfl
  simp_rw [expectation_average]
  unfold meanDensity
  rw [pairing_average_left]
  simp_rw [pairing_average_right]
  congr 1
  funext i
  congr 1
  funext j
  exact he i j

end
end SetCover.Paper
