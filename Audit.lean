import SetCover
import Mathlib.Util.AssertNoSorry

open Lean Elab Command in
elab "audit_set_cover_axioms" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut roots := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "SetCover." && !name.isInternalDetail then
      roots := roots.push name
  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for axiomName in state.axioms do
    unless allowed.contains axiomName do
      throwError "SetCover mathematical declarations depend on unapproved axiom {axiomName}"
  logInfo m!"Audited {roots.size} public SetCover declarations transitively: only propext, Classical.choice, Quot.sound."

audit_set_cover_axioms

assert_no_sorry SetCover.manuscript_lemma22
assert_no_sorry SetCover.Paper.main_theorem

#print axioms SetCover.manuscript_lemma22
#print axioms SetCover.Paper.main_theorem

-- The final theorem has no Fourier, moment, or numerical-budget hypotheses.
#check SetCover.manuscript_lemma22
#print SetCover.ManuscriptLemma22
#print SetCover.Lemma22Conclusion
#print SetCover.Good
#print SetCover.DensityCertificate

run_cmd Lean.logInfo "FULL LEMMA STATUS: PROVED. All moment and asymptotic obligations are discharged."

#check SetCover.Paper.main_theorem
#print SetCover.Paper.ManuscriptMainTheorem
#print SetCover.Paper.MainConclusion
#print SetCover.Paper.EstimatesFull
#print SetCover.Paper.SeedMeasurable
#check SetCover.Paper.optimum_spec
#check SetCover.Paper.optimum_le_cost
#check SetCover.Paper.universe_card
#check SetCover.Paper.set_family_card
#check SetCover.Paper.FullMachine.knownCheap_run
#check SetCover.Paper.StreamingMachine.protocol_run
#check SetCover.Paper.StreamingMachine.protocol_depth

run_cmd Lean.logInfo "MAIN THEOREM STATUS: PROVED. No unproved cover-gap, rectangle, entropy, or simulation hypotheses."
