import SetCover.Paper.CommunicationPartition

/-! The communication inequality of manuscript Lemma 3.4, for the actual planted
and uniform input laws and arbitrary normalized finite public or private coins. -/

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

theorem randomized_protocol_acceptance_gap {v M k r s b : ℕ}
    (hk : 8 ≤ k) (hkM : k ≤ M) (hd : 0 < effectiveDimension k v)
    (hr : 0 < r) (hs : 0 < s) {A : CheapMatrix v M} (hA : Good k A)
    {Ω : Type*} [Fintype Ω] (coins : Ω → ℝ) (hcoins : IsProbability coins)
    (p : Ω → Protocol (Block v r) (Block v s)) (hb : ∀ ω, (p ω).depth ≤ b) :
    |randomAcceptance coins p (yesMass k r s A) -
        randomAcceptance coins p (noMass v r s)| ≤
      lambda k M + Real.exp (-(effectiveDimension k v : ℝ) / 120) +
        120 * (b : ℝ) * Real.log 2 /
          ((effectiveDimension k v : ℝ) * (min r s : ℕ)) := by
  let B := communicationError k M v +
    communicationRate k v r s * ((b : ℝ) * Real.log 2)
  have hB (ω : Ω) :
      |acceptance (yesMass k r s A) (p ω) - acceptance (noMass v r s) (p ω)| ≤ B :=
    deterministic_protocol_acceptance_gap hk hkM hd hr hs hA (p ω) (hb ω)
  have hmain :
      |randomAcceptance coins p (yesMass k r s A) -
          randomAcceptance coins p (noMass v r s)| ≤ B := by
    unfold randomAcceptance expectation
    rw [← sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      |∑ ω, coins ω *
          (acceptance (yesMass k r s A) (p ω) - acceptance (noMass v r s) (p ω))| ≤
          ∑ ω, |coins ω *
            (acceptance (yesMass k r s A) (p ω) - acceptance (noMass v r s) (p ω))| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ ω, coins ω *
          |acceptance (yesMass k r s A) (p ω) - acceptance (noMass v r s) (p ω)| := by
        simp only [abs_mul, abs_of_nonneg (hcoins.1 _)]
      _ ≤ ∑ ω, coins ω * B :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hB ω) (hcoins.1 ω)
      _ = B := by rw [← sum_mul, hcoins.2, one_mul]
  convert hmain using 1
  unfold B communicationError communicationRate
  ring

end
end SetCover.Paper
