import SetCover.Statement

/-!
Numeric parameter discharge for Lemma 2.2.  No random-matrix moment
estimate is assumed or proved in this file.
-/

namespace SetCover

open Filter

noncomputable section

def longMomentOrder (k v : ℕ) : ℕ :=
  ⌈240 * Real.log (Real.exp 1 * v / effectiveDimension k v)⌉₊

theorem choose_exp_log_bound {v d : ℕ} (hv : 0 < v) (hd : 0 < d) :
    (Nat.choose v d : ℝ) ≤
      Real.exp ((d : ℝ) * Real.log (Real.exp 1 * v / d)) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfR : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  calc
    (Nat.choose v d : ℝ) ≤ (v : ℝ) ^ d / d.factorial :=
      Nat.choose_le_pow_div d v
    _ = ((v : ℝ) / d) ^ d * ((d : ℝ) ^ d / d.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((v : ℝ) / d) ^ d * Real.exp d :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (d : ℝ) hdR.le d)
        (by positivity)
    _ = Real.exp ((d : ℝ) * Real.log (Real.exp 1 * v / d)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity),
        show Real.exp 1 * (v : ℝ) / d = Real.exp 1 * ((v : ℝ) / d) by ring,
        mul_pow, ← Real.exp_nat_mul]
      simp [mul_comm]

theorem entropy_log_ge_one {v d : ℕ} (hd : 0 < d) (hdv : d ≤ v) :
    1 ≤ Real.log (Real.exp 1 * v / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdvR : (d : ℝ) ≤ v := by exact_mod_cast hdv
  have hratio : Real.exp 1 ≤ Real.exp 1 * v / d := by
    apply (le_div_iff₀ hdR).mpr
    exact mul_le_mul_of_nonneg_left hdvR (Real.exp_pos _).le
  simpa using Real.log_le_log (Real.exp_pos 1) hratio

theorem binomial_tail_bound {v d L : ℕ} (hd : 0 < d) (hdv : d ≤ v)
    (hL : 240 * Real.log (Real.exp 1 * v / d) ≤ (L : ℝ)) :
    (Nat.choose v d : ℝ) * Real.exp (-(L : ℝ) * d / 120) ≤
      Real.exp (-(d : ℝ)) := by
  have hv : 0 < v := lt_of_lt_of_le hd hdv
  have hlog := entropy_log_ge_one hd hdv
  have hm := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hlogm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  calc
    (Nat.choose v d : ℝ) * Real.exp (-(L : ℝ) * d / 120) ≤
        Real.exp ((d : ℝ) * Real.log (Real.exp 1 * v / d)) *
          Real.exp (-(L : ℝ) * d / 120) :=
      mul_le_mul_of_nonneg_right (choose_exp_log_bound hv hd) (Real.exp_pos _).le
    _ = Real.exp ((d : ℝ) * Real.log (Real.exp 1 * v / d) -
        (L : ℝ) * d / 120) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(d : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)

theorem effectiveDimension_le_k_div_64 {k v : ℕ} (hk : 0 < k) (hkv : k ≤ v) :
    (effectiveDimension k v : ℝ) ≤ (k : ℝ) / 64 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hvR : (0 : ℝ) < v := by exact_mod_cast lt_of_lt_of_le hk hkv
  have hkvR : (k : ℝ) ≤ v := by exact_mod_cast hkv
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hke : (k : ℝ) ≤ Real.exp 1 * v := by
    calc
      (k : ℝ) ≤ v := hkvR
      _ ≤ Real.exp 1 * v := by nlinarith
  calc
    (effectiveDimension k v : ℝ) ≤ (k : ℝ) ^ 2 / (64 * Real.exp 1 * v) :=
      Nat.floor_le (by positivity)
    _ ≤ (k : ℝ) / 64 := by
      apply (div_le_iff₀ (by positivity : 0 < 64 * Real.exp 1 * (v : ℝ))).mpr
      nlinarith [mul_le_mul_of_nonneg_left hke hkR.le]

theorem effectiveDimension_ge_hundred {k v : ℕ} (hv : 0 < v)
    (hsmall : (v : ℝ) ≤ (k : ℝ) ^ 2 / (6400 * Real.exp 1)) :
    100 ≤ effectiveDimension k v := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  unfold effectiveDimension
  apply (Nat.le_floor_iff (by positivity)).mpr
  norm_num only [Nat.cast_ofNat]
  apply (le_div_iff₀ (by positivity : 0 < 64 * Real.exp 1 * (v : ℝ))).mpr
  have h := (le_div_iff₀ (by positivity : 0 < 6400 * Real.exp 1)).mp hsmall
  nlinarith

theorem q_inv_power_sub_one_bound {k d : ℕ} (hk : 8 ≤ k)
    (hdk : (d : ℝ) ≤ (k : ℝ) / 32) :
    (q k ^ (2 * d))⁻¹ - 1 ≤ 32 * (d : ℝ) / k := by
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hq : 0 < q k := q_pos hk
  have hp : 0 < q k ^ (2 * d) := pow_pos hq _
  have hbern := one_add_mul_le_pow (a := -(4 / (k : ℝ)))
    (by have := (div_le_iff₀ hk0).mpr (by linarith : (4 : ℝ) ≤ 2 * k)
        linarith) (2 * d)
  have hlower : 1 - 8 * (d : ℝ) / k ≤ q k ^ (2 * d) := by
    convert hbern using 1
    simp only [Nat.cast_mul, Nat.cast_ofNat, q, beta, sub_eq_add_neg]
    ring
  have hr : 8 * (d : ℝ) / k ≤ 1 / 4 := by
    apply (div_le_iff₀ hk0).mpr
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ q k ^ (2 * d) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hhalf
    (by positivity : (0 : ℝ) ≤ 32 * (d : ℝ) / k)
  have hr0 : (0 : ℝ) ≤ (d : ℝ) / k := by positivity
  have hr32 : 8 * (d : ℝ) / k ≤ (32 * (d : ℝ) / k) * (1 / 2) := by
    calc
      8 * (d : ℝ) / k = 8 * ((d : ℝ) / k) := by ring
      _ ≤ 16 * ((d : ℝ) / k) :=
        mul_le_mul_of_nonneg_right (by norm_num) hr0
      _ = (32 * (d : ℝ) / k) * (1 / 2) := by ring
  rw [inv_eq_one_div, sub_le_iff_le_add, div_le_iff₀ hp]
  calc
    1 ≤ q k ^ (2 * d) + 8 * (d : ℝ) / k := (sub_le_iff_le_add).mp hlower
    _ ≤ q k ^ (2 * d) + (32 * (d : ℝ) / k) * (1 / 2) :=
      add_le_add_left hr32 _
    _ ≤ q k ^ (2 * d) + (32 * (d : ℝ) / k) * q k ^ (2 * d) :=
      add_le_add_left hmul _
    _ = _ := by ring

theorem q_zpow_sub_one_bound {k d : ℕ} (hk : 8 ≤ k)
    (hdk : (d : ℝ) ≤ (k : ℝ) / 32) :
    q k ^ (-(2 * (d : ℤ))) - 1 ≤ 32 * (d : ℝ) / k := by
  have hcast : 2 * (d : ℤ) = ((2 * d : ℕ) : ℤ) := by norm_cast
  rw [hcast, zpow_neg, zpow_natCast]
  exact q_inv_power_sub_one_bound hk hdk

theorem coverage_numeric_budget {k M v : ℕ} (hk : 100 ≤ k)
    (hM : (k : ℝ) ^ 2 ≤ M) (hv : (v : ℝ) ≤ (k : ℝ) ^ 2) :
    (v : ℝ) * q k ^ M ≤ (1 / 100 : ℝ) := by
  have hk8 : 8 ≤ k := by omega
  have hkR : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hqexp : q k ≤ Real.exp (-(4 / (k : ℝ))) := by
    have h := Real.add_one_le_exp (-(4 / (k : ℝ)))
    simpa [q, beta, sub_eq_add_neg, add_comm] using h
  have hpow : q k ^ M ≤ Real.exp ((M : ℝ) * (-(4 / (k : ℝ)))) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (q_pos hk8).le hqexp _
  have hexponent : (M : ℝ) * (-(4 / (k : ℝ))) ≤ -4 * k := by
    have h : (-4 * (M : ℝ)) / k ≤ -4 * k := by
      apply (div_le_iff₀ hk0).mpr
      nlinarith
    convert h using 1; ring
  have hexp : q k ^ M ≤ Real.exp (-4 * (k : ℝ)) :=
    hpow.trans (Real.exp_le_exp.mpr hexponent)
  have hseries := Real.pow_div_factorial_le_exp (4 * (k : ℝ)) (by positivity) 3
  norm_num [Nat.factorial] at hseries
  have hbig := mul_le_mul_of_nonneg_right hkR (sq_nonneg (k : ℝ))
  have hpoly : 100 * (k : ℝ) ^ 2 ≤ Real.exp (4 * (k : ℝ)) := by nlinarith
  have hdecay : (k : ℝ) ^ 2 * Real.exp (-4 * (k : ℝ)) ≤ (1 / 100 : ℝ) := by
    rw [show -4 * (k : ℝ) = -(4 * (k : ℝ)) by ring, Real.exp_neg,
      ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  calc
    (v : ℝ) * q k ^ M ≤ (k : ℝ) ^ 2 * Real.exp (-4 * (k : ℝ)) :=
      mul_le_mul hv hexp (pow_nonneg (q_pos hk8).le _) (sq_nonneg _)
    _ ≤ (1 / 100 : ℝ) := hdecay

theorem longMomentOrder_bounds {k v : ℕ} (hk : 0 < k)
    (hd : 0 < effectiveDimension k v) (hdv : effectiveDimension k v ≤ v)
    (hv : (v : ℝ) ≤ (k : ℝ) ^ 2) :
    0 < longMomentOrder k v ∧
      (longMomentOrder k v : ℝ) ≤ 241 + 480 * Real.log (k : ℝ) := by
  let d := effectiveDimension k v
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hvR : (0 : ℝ) < v := by exact_mod_cast lt_of_lt_of_le hd hdv
  have hratio : 0 < Real.exp 1 * v / (d : ℝ) := by positivity
  have hlog := entropy_log_ge_one hd hdv
  change 1 ≤ Real.log (Real.exp 1 * v / (d : ℝ)) at hlog
  have hratio_upper : Real.exp 1 * v / (d : ℝ) ≤ Real.exp 1 * (k : ℝ) ^ 2 := by
    calc
      Real.exp 1 * v / (d : ℝ) ≤ Real.exp 1 * v :=
        div_le_self (by positivity) hdR
      _ ≤ Real.exp 1 * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
  have hlog_upper := Real.log_le_log hratio hratio_upper
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hkR.ne'),
    Real.log_exp, Real.log_pow] at hlog_upper
  have hceil := Nat.ceil_lt_add_one
    (by linarith : 0 ≤ 240 * Real.log (Real.exp 1 * v / (d : ℝ)))
  constructor
  · apply Nat.ceil_pos.mpr
    change 0 < 240 * Real.log (Real.exp 1 * v / (d : ℝ))
    linarith
  · change (⌈240 * Real.log (Real.exp 1 * v / (d : ℝ))⌉₊ : ℝ) ≤ _
    norm_num only [Nat.cast_ofNat] at hlog_upper
    linarith

theorem eventually_log_small :
    ∀ᶠ k : ℕ in atTop, Real.log (k : ℝ) ≤ (k : ℝ) / 2000000 := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto hnat).bound
    (by norm_num : (0 : ℝ) < 1 / 2000000)
  filter_upwards [h] with k hk
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)] at hk
  have := (le_abs_self (Real.log (k : ℝ))).trans hk
  linarith

theorem long_correction_sufficient_bound {k M L d : ℕ} (hk : 0 < k)
    (hlam : lambda k M ≤ 1) (hLk : 1920 * (L : ℝ) ≤ k) :
    16 * lambda k M * (L : ℝ) ^ 2 * d / k ≤ (L : ℝ) * d / 120 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hLk
    (by positivity : (0 : ℝ) ≤ (L : ℝ) * d)
  calc
    16 * lambda k M * (L : ℝ) ^ 2 * d / k ≤
        16 * 1 * (L : ℝ) ^ 2 * d / k := by gcongr
    _ ≤ (L : ℝ) * d / 120 := by
      apply (div_le_iff₀ hkR).mpr
      nlinarith only [hm]

theorem long_correction_bound {k M L d : ℕ} (hk : 0 < k) (hL : 0 < L)
    (hlam : lambda k M ≤ 1) (hLk : 1920 * (L : ℝ) ≤ k)
    (hq : q k ^ (-(2 * (d : ℤ))) - 1 ≤ 32 * (d : ℝ) / k) :
    lambda k M * (L : ℝ) * ((L : ℝ) - 1) / 2 *
        (q k ^ (-(2 * (d : ℤ))) - 1) ≤ (L : ℝ) * d / 120 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLsub : 0 ≤ (L : ℝ) - 1 := sub_nonneg.mpr hL1
  have hlam0 : 0 ≤ lambda k M := by unfold lambda; positivity
  calc
    lambda k M * (L : ℝ) * ((L : ℝ) - 1) / 2 *
        (q k ^ (-(2 * (d : ℤ))) - 1) ≤
        lambda k M * (L : ℝ) * ((L : ℝ) - 1) / 2 *
          (32 * (d : ℝ) / k) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ lambda k M * (L : ℝ) * L / 2 * (32 * (d : ℝ) / k) := by
      gcongr
      linarith
    _ = 16 * lambda k M * (L : ℝ) ^ 2 * d / k := by ring
    _ ≤ (L : ℝ) * d / 120 := long_correction_sufficient_bound hk hlam hLk

structure ParameterBudget (k M v : ℕ) : Prop where
  k_large : 8 ≤ k
  k_le_M : k ≤ M
  dimension_pos : 0 < effectiveDimension k v
  order_pos : 0 < longMomentOrder k v
  dimension_le_v : effectiveDimension k v ≤ v
  failure_budget :
    (v : ℝ) * q k ^ M + 100 * lambda k M +
      (Nat.choose v (effectiveDimension k v) : ℝ) *
        Real.exp (-(longMomentOrder k v : ℝ) * effectiveDimension k v / 120) ≤
          (1 / 10 : ℝ)
  inverse_power_bound :
    q k ^ (-(2 * (effectiveDimension k v : ℤ))) - 1 ≤
      32 * (effectiveDimension k v : ℝ) / k
  long_correction_sufficient :
    16 * lambda k M * (longMomentOrder k v : ℝ) ^ 2 * effectiveDimension k v / k ≤
      (longMomentOrder k v : ℝ) * effectiveDimension k v / 120
  long_correction :
    lambda k M * (longMomentOrder k v : ℝ) * ((longMomentOrder k v : ℝ) - 1) / 2 *
        (q k ^ (-(2 * (effectiveDimension k v : ℤ))) - 1) ≤
      (longMomentOrder k v : ℝ) * effectiveDimension k v / 120

theorem parameterBudget_of_numeric_conditions {k M v : ℕ}
    (hk : 2000000 ≤ k) (hM : 10000 * (k : ℝ) ^ 2 ≤ M) (hkv : k ≤ v)
    (hvsmall : (v : ℝ) ≤ (k : ℝ) ^ 2 / (6400 * Real.exp 1))
    (hlog : Real.log (k : ℝ) ≤ (k : ℝ) / 2000000) :
    ParameterBudget k M v := by
  have hk0 : 0 < k := by omega
  have hk8 : 8 ≤ k := by omega
  have hkR : (2000000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR0 : (0 : ℝ) < k := by exact_mod_cast hk0
  have hv0 : 0 < v := lt_of_lt_of_le hk0 hkv
  have hM2 : (k : ℝ) ^ 2 ≤ M := by nlinarith [sq_nonneg (k : ℝ)]
  have hkM : k ≤ M := by
    have : (k : ℝ) ≤ M := by nlinarith
    exact_mod_cast this
  have hMR0 : (0 : ℝ) < M := by
    exact_mod_cast lt_of_lt_of_le hk0 hkM
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hv : (v : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hden : 1 ≤ 6400 * Real.exp 1 := by linarith
    exact hvsmall.trans (div_le_self (sq_nonneg _) hden)
  have hd100 : 100 ≤ effectiveDimension k v :=
    effectiveDimension_ge_hundred hv0 hvsmall
  have hd : 0 < effectiveDimension k v := by omega
  have hdk := effectiveDimension_le_k_div_64 hk0 hkv
  have hdv : effectiveDimension k v ≤ v := by
    have hkvR : (k : ℝ) ≤ v := by exact_mod_cast hkv
    have : (effectiveDimension k v : ℝ) ≤ v := by linarith
    exact_mod_cast this
  have hL := longMomentOrder_bounds hk0 hd hdv hv
  have hLk : 1920 * (longMomentOrder k v : ℝ) ≤ k := by
    linarith [hL.2]
  have hlam : lambda k M ≤ (1 / 10000 : ℝ) := by
    unfold lambda
    apply (div_le_iff₀ hMR0).mpr
    linarith
  have hlam1 : lambda k M ≤ 1 := hlam.trans (by norm_num)
  have htail := binomial_tail_bound hd hdv
    (Nat.le_ceil (240 * Real.log (Real.exp 1 * v / effectiveDimension k v)))
  have hdecay : Real.exp (-(effectiveDimension k v : ℝ)) ≤ (1 / 100 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    have hdR : (100 : ℝ) ≤ effectiveDimension k v := by exact_mod_cast hd100
    have hexp := Real.add_one_le_exp (effectiveDimension k v : ℝ)
    linarith
  have hcover := coverage_numeric_budget (by omega : 100 ≤ k) hM2 hv
  have hq := q_zpow_sub_one_bound hk8
    (show (effectiveDimension k v : ℝ) ≤ (k : ℝ) / 32 by linarith)
  refine {
    k_large := hk8
    k_le_M := hkM
    dimension_pos := hd
    order_pos := hL.1
    dimension_le_v := hdv
    failure_budget := ?_
    inverse_power_bound := hq
    long_correction_sufficient := long_correction_sufficient_bound hk0 hlam1 hLk
    long_correction := long_correction_bound hk0 hL.1 hlam1 hLk hq }
  change (Nat.choose v (effectiveDimension k v) : ℝ) *
    Real.exp (-(longMomentOrder k v : ℝ) * effectiveDimension k v / 120) ≤ _ at htail
  linarith [htail.trans hdecay]

/-- Every fixed `C₀ ≥ 10000` suffices for the numeric budget.  The hypotheses
are exactly the manuscript family hypotheses, without any moment assumptions. -/
theorem eventually_parameter_budget {C₀ : ℝ} (hC₀ : 10000 ≤ C₀)
    (M v : ℕ → ℕ) (α : ℕ → ℝ)
    (hfamily : ∀ᶠ k in atTop,
      1 ≤ α k ∧ C₀ * (k : ℝ) ^ 2 ≤ M k ∧
      6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k)
    (hsub : Asymptotics.IsLittleO atTop
      (fun k => (v k : ℝ)) (fun k => (k : ℝ) ^ 2)) :
    ∀ᶠ k in atTop, ParameterBudget k (M k) (v k) := by
  have hsmall : ∀ᶠ k in atTop,
      (v k : ℝ) ≤ (k : ℝ) ^ 2 / (6400 * Real.exp 1) := by
    have h := hsub.bound (by positivity : (0 : ℝ) < 1 / (6400 * Real.exp 1))
    filter_upwards [h] with k hk
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (v k) : (0 : ℝ) ≤ v k),
      abs_of_nonneg (sq_nonneg (k : ℝ))] at hk
    calc
      (v k : ℝ) ≤ (1 / (6400 * Real.exp 1)) * (k : ℝ) ^ 2 := hk
      _ = (k : ℝ) ^ 2 / (6400 * Real.exp 1) := by ring
  filter_upwards [hfamily, hsmall, eventually_log_small,
    eventually_ge_atTop 2000000] with k hfamily hsmall hlog hk
  have hkR : (2000000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hM : 10000 * (k : ℝ) ^ 2 ≤ M k :=
    (mul_le_mul_of_nonneg_right hC₀ (sq_nonneg _)).trans hfamily.2.1
  have hM1 : (1 : ℝ) ≤ M k := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hlogM : 1 ≤ Real.log (2 * (M k : ℝ) + 1) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    have he := Real.exp_one_lt_d9
    linarith
  have hα0 : 0 ≤ α k := by linarith [hfamily.1]
  have hexp : 1 ≤ Real.exp (27 * α k) := Real.one_le_exp (by positivity)
  have hcoef : 1 ≤ 6 * α k * Real.exp (27 * α k) := by
    have hm := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 6 * α k)
    nlinarith [hfamily.1]
  have hkv : k ≤ v k := by
    have hkvR : (k : ℝ) ≤ v k := by
      calc
        (k : ℝ) ≤ 6 * α k * Real.exp (27 * α k) * k := by
          simpa using mul_le_mul_of_nonneg_right hcoef hk0.le
        _ ≤ 6 * α k * Real.exp (27 * α k) * k *
            Real.log (2 * (M k : ℝ) + 1) := by
          simpa using mul_le_mul_of_nonneg_left hlogM
            (by positivity : 0 ≤ 6 * α k * Real.exp (27 * α k) * k)
        _ ≤ v k := hfamily.2.2
    exact_mod_cast hkvR
  exact parameterBudget_of_numeric_conditions hk hM hkv hsmall hlog

theorem eventually_basic_parameter_bounds {C₀ : ℝ} (hC₀ : 10000 ≤ C₀)
    (M v : ℕ → ℕ) (α : ℕ → ℝ)
    (hfamily : ∀ᶠ k in atTop,
      1 ≤ α k ∧ C₀ * (k : ℝ) ^ 2 ≤ M k ∧
      6 * α k * Real.exp (27 * α k) * k * Real.log (2 * M k + 1) ≤ v k)
    (hsub : Asymptotics.IsLittleO atTop
      (fun k => (v k : ℝ)) (fun k => (k : ℝ) ^ 2)) :
    ∀ᶠ k in atTop, 20 ≤ k ∧ k ≤ v k ∧ lambda k (M k) ≤ 1 := by
  filter_upwards [eventually_parameter_budget hC₀ M v α hfamily hsub,
    hfamily, eventually_ge_atTop 20] with k hb hf hk
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkM : (k : ℝ) ≤ M k := by exact_mod_cast hb.k_le_M
  have hM0 : (0 : ℝ) < M k := hk0.trans_le hkM
  have hC1 : 1 ≤ C₀ := by linarith
  have hM2 : (k : ℝ) ^ 2 ≤ M k := by
    have hm := mul_le_mul_of_nonneg_right hC1 (sq_nonneg (k : ℝ))
    linarith [hf.2.1]
  have hlam : lambda k (M k) ≤ 1 := by
    unfold lambda
    exact (div_le_one hM0).mpr hM2
  have hlogM : 1 ≤ Real.log (2 * (M k : ℝ) + 1) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    linarith [Real.exp_one_lt_d9]
  have hα0 : 0 ≤ α k := by linarith [hf.1]
  have hexp : 1 ≤ Real.exp (27 * α k) := Real.one_le_exp (by positivity)
  have hcoef : 1 ≤ 6 * α k * Real.exp (27 * α k) := by
    have hm := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 6 * α k)
    nlinarith [hf.1]
  have hkv : k ≤ v k := by
    have hkvR : (k : ℝ) ≤ v k := by
      calc
        (k : ℝ) ≤ 6 * α k * Real.exp (27 * α k) * k := by
          simpa using mul_le_mul_of_nonneg_right hcoef hk0.le
        _ ≤ 6 * α k * Real.exp (27 * α k) * k *
            Real.log (2 * (M k : ℝ) + 1) := by
          simpa using mul_le_mul_of_nonneg_left hlogM
            (by positivity : 0 ≤ 6 * α k * Real.exp (27 * α k) * k)
        _ ≤ v k := hf.2.2
    exact_mod_cast hkvR
  exact ⟨hk, hkv, hlam⟩

theorem q_pow_self_lower_bound {k : ℕ} (hk : 20 ≤ k) :
    (1 / 256 : ℝ) ≤ q k ^ k := by
  have hk8 : 8 ≤ k := by omega
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk4 : (0 : ℝ) < (k : ℝ) - 4 := by linarith
  have hq : 0 < q k := q_pos hk8
  have hlog := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos hq) hk0.le
  have hqne : 1 - 4 / (k : ℝ) ≠ 0 := hq.ne'
  have hid : (k : ℝ) * (1 - (q k)⁻¹) =
      -4 * (k : ℝ) / ((k : ℝ) - 4) := by
    unfold q beta
    field_simp [hk0.ne', hk4.ne', hqne]
    ring
  rw [hid] at hlog
  have hquot : (-5 : ℝ) ≤ -4 * (k : ℝ) / ((k : ℝ) - 4) := by
    apply (le_div_iff₀ hk4).mpr
    linarith
  have he1 : Real.exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he5 : Real.exp 5 ≤ (256 : ℝ) := by
    calc
      Real.exp 5 = Real.exp 1 ^ 5 := by simp [← Real.exp_nat_mul]
      _ ≤ (3 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos _).le he1 _
      _ ≤ 256 := by norm_num
  have hinv : (1 / 256 : ℝ) ≤ Real.exp (-5) := by
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
    linarith
  calc
    (1 / 256 : ℝ) ≤ Real.exp (-5) := hinv
    _ ≤ Real.exp ((k : ℝ) * Real.log (q k)) :=
      Real.exp_le_exp.mpr (hquot.trans hlog)
    _ = q k ^ k := by rw [Real.exp_nat_mul, Real.exp_log hq]

theorem binomial_mass_five_lower_bound {k : ℕ} (hk : 20 ≤ k) :
    (1 / 30 : ℝ) ≤ binomialMass k 5 := by
  have hk4 : 4 ≤ k := by omega
  have hk5 : 5 ≤ k := by omega
  have hk8 : 8 ≤ k := by omega
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk4R : 0 < (k : ℝ) - 4 := by linarith
  have hq : 0 < q k := q_pos hk8
  have hb : 0 < beta k := beta_pos hk8
  have hdesc := Nat.pow_sub_le_descFactorial k 5
  rw [show k + 1 - 5 = k - 4 by omega,
    Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  norm_num [Nat.factorial] at hdesc
  have hdescR : ((k : ℝ) - 4) ^ 5 ≤ 120 * (Nat.choose k 5 : ℝ) := by
    exact_mod_cast hdesc
  have hm := mul_le_mul_of_nonneg_right hdescR
    (by positivity : (0 : ℝ) ≤ (4 / ((k : ℝ) - 4)) ^ 5)
  have hcancel : ((k : ℝ) - 4) ^ 5 * (4 / ((k : ℝ) - 4)) ^ 5 = (4 : ℝ) ^ 5 := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hcancel] at hm
  have hweighted : (4 : ℝ) ^ 5 / 120 ≤
      (Nat.choose k 5 : ℝ) * (beta k / q k) ^ 5 := by
    rw [beta_div_q hk8]
    nlinarith only [hm]
  have hpow : q k ^ (k - 5) * q k ^ 5 = q k ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk5]
  have hmass : binomialMass k 5 =
      (Nat.choose k 5 : ℝ) * (beta k / q k) ^ 5 * q k ^ k := by
    rw [binomialMass, div_pow, ← hpow]
    field_simp
    ring
  rw [hmass]
  calc
    (1 / 30 : ℝ) = ((4 : ℝ) ^ 5 / 120) * (1 / 256) := by norm_num
    _ ≤ (Nat.choose k 5 : ℝ) * (beta k / q k) ^ 5 * q k ^ k :=
      mul_le_mul hweighted (q_pow_self_lower_bound hk) (by norm_num) (by positivity)

end
end SetCover
