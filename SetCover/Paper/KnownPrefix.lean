import SetCover.Paper.Streaming

namespace SetCover.Paper

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

abbrev Incidence (v : ℕ) := Element v → Bool

def cheapBits {v M : ℕ} (A : CheapMatrix v M) (j : Fin M) : Incidence v :=
  fun e => A e.1 j

def transversalBits {v : ℕ} (x : Cube v) : Incidence v :=
  fun e => decide (x e.1 = e.2)

def itemBits {v M r s : ℕ} (A : CheapMatrix v M) (x : Input v r s) :
    SetId M r s → Incidence v :=
  Sum.elim (cheapBits A) (fun j => transversalBits (vectorAt x j))

theorem itemBits_correct {v M r s : ℕ} (A : CheapMatrix v M) (x : Input v r s)
    (i : SetId M r s) (e : Element v) :
    itemBits A x i e = true ↔ contains A x i e := by
  cases i <;> simp [itemBits, cheapBits, transversalBits, contains]

theorem universe_card (v : ℕ) : Fintype.card (Element v) = 2 * v := by
  simp [Element, Nat.mul_comm]

theorem set_family_card {M r s : ℕ} (h : r + s = M) :
    Fintype.card (SetId M r s) = 2 * M := by
  simp only [SetId, Fintype.card_sum, Fintype.card_fin]
  omega

theorem hard_weights {M r s : ℕ} (k : ℕ) (i : SetId M r s) :
    weight k i = 1 ∨ weight k i = k := by
  cases i <;> simp [weight]

def fullIndices (M r s : ℕ) : List (SetId M r s) :=
  (List.finRange M).map Sum.inl ++ (streamIndices r s).map Sum.inr

/-- Ordinary itemwise processing of all M+r+s labeled weighted input sets. -/
structure FullMachine (p S v M r s : ℕ) (Out : Type*) where
  initial : Memory S
  step : Fin p → SetId M r s → Memory S → Incidence v → ℕ → Memory S
  finish : Memory S → SetId M r s → Incidence v → ℕ → Out

def lastRightId {M r s : ℕ} (hs : 0 < s) : SetId M r s :=
  Sum.inr (Sum.inr ⟨s - 1, by omega⟩)

def FullMachine.runPass {p S v M r s : ℕ} {Out : Type*}
    (m : FullMachine p S v M r s Out) (k : ℕ) (A : CheapMatrix v M)
    (x : Input v r s) (q : Fin p) (st : Memory S) : Memory S :=
  (fullIndices M r s).foldl
    (fun state i => m.step q i state (itemBits A x i) (weight k i)) st

def FullMachine.run {p S v M r s : ℕ} {Out : Type*}
    (m : FullMachine p S v M r s Out) (k : ℕ) (A : CheapMatrix v M)
    (hs : 0 < s) (x : Input v r s) : Out :=
  let final := (List.finRange p).foldl (fun st q => m.runPass k A x q st) m.initial
  m.finish final (lastRightId hs) (itemBits A x (lastRightId hs)) k

/-- Compile the fixed cheap prefix into a local state transformation in each pass. -/
def FullMachine.withKnownCheap {p S v M r s : ℕ} {Out : Type*}
    (m : FullMachine p S v M r s Out) (k : ℕ) (A : CheapMatrix v M)
    (hs : 0 < s) : StreamingMachine p S v r s Out where
  initial := m.initial
  prepare q st := (List.finRange M).foldl
    (fun state j => m.step q (Sum.inl j) state (cheapBits A j) 1) st
  step q j st z := m.step q (Sum.inr j) st (transversalBits z) k
  finish st z := m.finish st (lastRightId hs) (transversalBits z) k

theorem FullMachine.knownCheap_pass {p S v M r s : ℕ} {Out : Type*}
    (m : FullMachine p S v M r s Out) (k : ℕ) (A : CheapMatrix v M)
    (hs : 0 < s) (x : Input v r s) (q : Fin p) (st : Memory S) :
    (m.withKnownCheap k A hs).runPass q st x = m.runPass k A x q st := by
  simp [StreamingMachine.runPass, FullMachine.runPass, withKnownCheap, fullIndices,
    List.foldl_append, List.foldl_map, itemBits, weight, Function.comp_def]

theorem FullMachine.knownCheap_run {p S v M r s : ℕ} {Out : Type*}
    (m : FullMachine p S v M r s Out) (k : ℕ) (A : CheapMatrix v M)
    (hs : 0 < s) (x : Input v r s) :
    (m.withKnownCheap k A hs).run x = m.run k A hs x := by
  unfold StreamingMachine.run StreamingMachine.runRounds FullMachine.run
  simp only [knownCheap_pass]
  simp [withKnownCheap, lastRight, hs, lastRightId, itemBits, vectorAt]

end
end SetCover.Paper
