import Mathlib

/-! Finite real-valued expectations, with no measure-theoretic coercions. -/

namespace SetCover

open scoped BigOperators

noncomputable section

def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem card_pos : (0 : ℝ) < Fintype.card Ω := by
  exact_mod_cast Fintype.card_pos

@[simp] theorem average_const (c : ℝ) :
    average (fun _ : Ω => c) = c := by
  simp [average, ne_of_gt (card_pos (Ω := Ω))]

theorem average_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x)
    (le_of_lt (card_pos (Ω := Ω)))

theorem average_nonneg {f : Ω → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  simpa using average_mono h

omit [Nonempty Ω] in
theorem average_add (f g : Ω → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

omit [Nonempty Ω] in
theorem average_sub (f g : Ω → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, sub_div]

omit [Nonempty Ω] in
theorem average_mul (c : ℝ) (f : Ω → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp [average, ← Finset.mul_sum, mul_div_assoc]

omit [Nonempty Ω] in
theorem average_mul_right (f : Ω → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := by
  simpa [mul_comm] using average_mul c f

omit [Nonempty Ω] in
theorem average_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    average (fun x => ∑ i, f i x) = ∑ i, average (f i) := by
  simp only [average, Finset.sum_div]
  rw [Finset.sum_comm]

theorem abs_average_le (f : Ω → ℝ) :
    |average f| ≤ average (fun x => |f x|) := by
  simp only [average, abs_div, abs_of_pos (card_pos (Ω := Ω))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
    (le_of_lt (card_pos (Ω := Ω)))

def IsDensity (f : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ average f = 1

def entropy (f : Ω → ℝ) : ℝ :=
  average (fun x => f x * Real.log (f x))

def phi (u : ℝ) : ℝ := u * Real.log u - u + 1

theorem phi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ phi u := by
  rcases eq_or_lt_of_le hu with h | h
  · subst u
    norm_num [phi]
  · have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos h) hu
    have he : u * (1 - u⁻¹) = u - 1 := by
      field_simp
    rw [he] at hh
    unfold phi
    linarith

theorem average_phi {f : Ω → ℝ} (hf : IsDensity f) :
    average (fun x => phi (f x)) = entropy f := by
  simp only [phi, average_add, average_sub, average_const, hf.2, entropy]
  ring

theorem entropy_nonneg {f : Ω → ℝ} (hf : IsDensity f) : 0 ≤ entropy f := by
  rw [← average_phi hf]
  exact average_nonneg fun x => phi_nonneg (hf.1 x)

def truncate (L : ℝ) (f : Ω → ℝ) : Ω → ℝ := fun x => min (f x) L

theorem log_mul_truncation_loss_le {L u : ℝ} (hL : 1 < L) (hu : 0 ≤ u) :
    Real.log L * (u - min u L) ≤ phi u := by
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  by_cases huL : u ≤ L
  · rw [min_eq_left huL, sub_self, mul_zero]
    exact phi_nonneg hu
  · have hLu : L < u := lt_of_not_ge huL
    have hu0 : 0 < u := lt_trans hL0 hLu
    rw [min_eq_right (le_of_lt hLu)]
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hL0)
    rw [Real.log_div (ne_of_gt hu0) (ne_of_gt hL0)] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog hu
    have he : u * (1 - (u / L)⁻¹) = u - L := by
      field_simp
    rw [he] at hm
    have hp := phi_nonneg (le_of_lt hL0)
    unfold phi at *
    nlinarith

theorem truncate_average_bounds {L : ℝ} {f : Ω → ℝ}
    (hL : 1 < L) (hf : IsDensity f) :
    0 ≤ average (truncate L f) ∧ average (truncate L f) ≤ 1 := by
  constructor
  · exact average_nonneg fun x => le_min (hf.1 x) (by linarith)
  · calc
      average (truncate L f) ≤ average f := average_mono fun x => min_le_left _ _
      _ = 1 := hf.2

theorem truncate_second_moment {L : ℝ} {f : Ω → ℝ}
    (hL : 1 < L) (hf : IsDensity f) :
    average (fun x => truncate L f x ^ 2) ≤ L := by
  have hL0 : 0 ≤ L := by linarith
  calc
    average (fun x => truncate L f x ^ 2)
        ≤ average (fun x => L * truncate L f x) := by
          apply average_mono
          intro x
          have h0 : 0 ≤ truncate L f x := le_min (hf.1 x) hL0
          have h1 : truncate L f x ≤ L := min_le_right _ _
          nlinarith
    _ = L * average (truncate L f) := average_mul _ _
    _ ≤ L * 1 := mul_le_mul_of_nonneg_left (truncate_average_bounds hL hf).2 hL0
    _ = L := mul_one _

theorem truncate_lost_mass {L : ℝ} {f : Ω → ℝ}
    (hL : 1 < L) (hf : IsDensity f) :
    1 - average (truncate L f) ≤ entropy f / Real.log L := by
  have h := average_mono fun x => log_mul_truncation_loss_le hL (hf.1 x)
  rw [average_mul, average_sub, hf.2, average_phi hf] at h
  exact (le_div_iff₀ (Real.log_pos hL)).2 (by simpa [mul_comm, truncate] using h)

end
end SetCover
