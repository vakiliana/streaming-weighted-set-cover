import SetCover.Paper.Entropy

namespace SetCover.Paper

open scoped BigOperators
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

variable {X Y : Type*}

def Protocol.Leaf : Protocol X Y → Type
  | .leaf _ => Unit
  | .alice _ zero one => zero.Leaf ⊕ one.Leaf
  | .bob _ zero one => zero.Leaf ⊕ one.Leaf

instance Protocol.leafFintype (p : Protocol X Y) : Fintype p.Leaf :=
  match p with
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | .alice _ zero one =>
      letI := zero.leafFintype
      letI := one.leafFintype
      inferInstanceAs (Fintype (zero.Leaf ⊕ one.Leaf))
  | .bob _ zero one =>
      letI := zero.leafFintype
      letI := one.leafFintype
      inferInstanceAs (Fintype (zero.Leaf ⊕ one.Leaf))

def Protocol.firstLeaf : (p : Protocol X Y) → p.Leaf
  | .leaf _ => ()
  | .alice _ zero _ => Sum.inl zero.firstLeaf
  | .bob _ zero _ => Sum.inl zero.firstLeaf

instance Protocol.leafNonempty (p : Protocol X Y) : Nonempty p.Leaf :=
  ⟨p.firstLeaf⟩

def Protocol.leafFor : (p : Protocol X Y) → X → Y → p.Leaf
  | .leaf _, _, _ => ()
  | .alice m zero one, x, y =>
      if m x then Sum.inr (one.leafFor x y) else Sum.inl (zero.leafFor x y)
  | .bob m zero one, x, y =>
      if m y then Sum.inr (one.leafFor x y) else Sum.inl (zero.leafFor x y)

def Protocol.leafAnswer : (p : Protocol X Y) → p.Leaf → Bool
  | .leaf b, _ => b
  | .alice _ zero _, .inl t => zero.leafAnswer t
  | .alice _ _ one, .inr t => one.leafAnswer t
  | .bob _ zero _, .inl t => zero.leafAnswer t
  | .bob _ _ one, .inr t => one.leafAnswer t

def Protocol.leafTrace : (p : Protocol X Y) → p.Leaf → List Bool
  | .leaf _, _ => []
  | .alice _ zero _, .inl t => false :: zero.leafTrace t
  | .alice _ _ one, .inr t => true :: one.leafTrace t
  | .bob _ zero _, .inl t => false :: zero.leafTrace t
  | .bob _ _ one, .inr t => true :: one.leafTrace t

def Protocol.leftFiber : (p : Protocol X Y) → p.Leaf → X → Prop
  | .leaf _, _, _ => True
  | .alice m zero _, .inl t, x => m x = false ∧ zero.leftFiber t x
  | .alice m _ one, .inr t, x => m x = true ∧ one.leftFiber t x
  | .bob _ zero _, .inl t, x => zero.leftFiber t x
  | .bob _ _ one, .inr t, x => one.leftFiber t x

def Protocol.rightFiber : (p : Protocol X Y) → p.Leaf → Y → Prop
  | .leaf _, _, _ => True
  | .alice _ zero _, .inl t, y => zero.rightFiber t y
  | .alice _ _ one, .inr t, y => one.rightFiber t y
  | .bob m zero _, .inl t, y => m y = false ∧ zero.rightFiber t y
  | .bob m _ one, .inr t, y => m y = true ∧ one.rightFiber t y

theorem Protocol.leafFor_eq_iff (p : Protocol X Y) (t : p.Leaf) (x : X) (y : Y) :
    p.leafFor x y = t ↔ p.leftFiber t x ∧ p.rightFiber t y := by
  induction p with
  | leaf b =>
      change Unit at t
      cases t
      simp [leafFor, leftFiber, rightFiber]
  | alice m zero one ih0 ih1 =>
      cases t with
      | inl t =>
          cases hm : m x <;>
            simp [leafFor, leftFiber, rightFiber, hm, Sum.inl.injEq, ih0, and_assoc]
          exact ⟨fun h => (ih0 t).mp (Sum.inl.inj h),
            fun h => congrArg Sum.inl ((ih0 t).mpr h)⟩
      | inr t =>
          cases hm : m x <;>
            simp [leafFor, leftFiber, rightFiber, hm, Sum.inr.injEq, ih1, and_assoc]
          exact ⟨fun h => (ih1 t).mp (Sum.inr.inj h),
            fun h => congrArg Sum.inr ((ih1 t).mpr h)⟩
  | bob m zero one ih0 ih1 =>
      cases t with
      | inl t =>
          cases hm : m y <;>
            simp [leafFor, leftFiber, rightFiber, hm, Sum.inl.injEq, ih0, and_assoc]
          exact ⟨fun h => (ih0 t).mp (Sum.inl.inj h),
            fun h => congrArg Sum.inl ((ih0 t).mpr h)⟩
      | inr t =>
          cases hm : m y <;>
            simp [leafFor, leftFiber, rightFiber, hm, Sum.inr.injEq, ih1, and_assoc]
          exact ⟨fun h => (ih1 t).mp (Sum.inr.inj h),
            fun h => congrArg Sum.inr ((ih1 t).mpr h)⟩

theorem Protocol.leafAnswer_leafFor (p : Protocol X Y) (x : X) (y : Y) :
    p.leafAnswer (p.leafFor x y) = p.run x y := by
  induction p with
  | leaf b => rfl
  | alice m zero one ih0 ih1 =>
      cases hm : m x <;> simp [leafFor, leafAnswer, run, hm, ih0, ih1]
  | bob m zero one ih0 ih1 =>
      cases hm : m y <;> simp [leafFor, leafAnswer, run, hm, ih0, ih1]

theorem Protocol.leafTrace_leafFor (p : Protocol X Y) (x : X) (y : Y) :
    p.leafTrace (p.leafFor x y) = p.trace x y := by
  induction p with
  | leaf b => rfl
  | alice m zero one ih0 ih1 =>
      cases hm : m x <;> simp [leafFor, leafTrace, trace, hm, ih0, ih1]
  | bob m zero one ih0 ih1 =>
      cases hm : m y <;> simp [leafFor, leafTrace, trace, hm, ih0, ih1]

theorem Protocol.leafTrace_injective (p : Protocol X Y) : Function.Injective p.leafTrace := by
  induction p with
  | leaf b =>
      change Function.Injective (fun _ : Unit => ([] : List Bool))
      exact fun _ _ _ => Subsingleton.elim _ _
  | alice m zero one ih0 ih1 =>
      intro a b h
      cases a <;> cases b <;> simp only [leafTrace, List.cons.injEq] at h
      · exact congrArg Sum.inl (ih0 h.2)
      · cases h.1
      · cases h.1
      · exact congrArg Sum.inr (ih1 h.2)
  | bob m zero one ih0 ih1 =>
      intro a b h
      cases a <;> cases b <;> simp only [leafTrace, List.cons.injEq] at h
      · exact congrArg Sum.inl (ih0 h.2)
      · cases h.1
      · cases h.1
      · exact congrArg Sum.inr (ih1 h.2)

theorem Protocol.transcript_fiber_rectangle (p : Protocol X Y) (t : p.Leaf) :
    ∀ x y, p.trace x y = p.leafTrace t ↔ p.leftFiber t x ∧ p.rightFiber t y := by
  intro x y
  rw [← p.leafTrace_leafFor, p.leafTrace_injective.eq_iff, p.leafFor_eq_iff]

theorem Protocol.card_leaf_le (p : Protocol X Y) : Fintype.card p.Leaf ≤ 2 ^ p.depth := by
  induction p with
  | leaf b => simp [Leaf, depth, leafFintype]
  | alice m zero one ih0 ih1 =>
      have h0 := ih0.trans (Nat.pow_le_pow_right (by omega : 0 < 2)
        (le_max_left zero.depth one.depth))
      have h1 := ih1.trans (Nat.pow_le_pow_right (by omega : 0 < 2)
        (le_max_right zero.depth one.depth))
      simp only [Leaf, leafFintype, Fintype.card_sum, depth, pow_add, pow_one]
      omega
  | bob m zero one ih0 ih1 =>
      have h0 := ih0.trans (Nat.pow_le_pow_right (by omega : 0 < 2)
        (le_max_left zero.depth one.depth))
      have h1 := ih1.trans (Nat.pow_le_pow_right (by omega : 0 < 2)
        (le_max_right zero.depth one.depth))
      simp only [Leaf, leafFintype, Fintype.card_sum, depth, pow_add, pow_one]
      omega

theorem Protocol.card_leaf_le_of_depth (p : Protocol X Y) {b : ℕ} (hb : p.depth ≤ b) :
    Fintype.card p.Leaf ≤ 2 ^ b :=
  p.card_leaf_le.trans (Nat.pow_le_pow_right (by omega : 0 < 2) hb)

def Protocol.nodeLeft : Protocol X Y → List Bool → X → Prop
  | _, [], _ => True
  | .leaf _, _ :: _, _ => False
  | .alice m zero _, false :: t, x => m x = false ∧ zero.nodeLeft t x
  | .alice m _ one, true :: t, x => m x = true ∧ one.nodeLeft t x
  | .bob _ zero _, false :: t, x => zero.nodeLeft t x
  | .bob _ _ one, true :: t, x => one.nodeLeft t x

def Protocol.nodeRight : Protocol X Y → List Bool → Y → Prop
  | _, [], _ => True
  | .leaf _, _ :: _, _ => False
  | .alice _ zero _, false :: t, y => zero.nodeRight t y
  | .alice _ _ one, true :: t, y => one.nodeRight t y
  | .bob m zero _, false :: t, y => m y = false ∧ zero.nodeRight t y
  | .bob m _ one, true :: t, y => m y = true ∧ one.nodeRight t y

theorem Protocol.node_fiber_rectangle (p : Protocol X Y) (t : List Bool) (x : X) (y : Y) :
    t.IsPrefix (p.trace x y) ↔ p.nodeLeft t x ∧ p.nodeRight t y := by
  induction p generalizing t with
  | leaf b => cases t <;> simp [trace, nodeLeft, nodeRight]
  | alice m zero one ih0 ih1 =>
      cases t with
      | nil => simp [nodeLeft, nodeRight]
      | cons bit t =>
          cases bit <;> cases hm : m x <;>
            simp [trace, nodeLeft, nodeRight, hm, ih0, ih1, and_assoc]
  | bob m zero one ih0 ih1 =>
      cases t with
      | nil => simp [nodeLeft, nodeRight]
      | cons bit t =>
          cases bit <;> cases hm : m y <;>
            simp [trace, nodeLeft, nodeRight, hm, ih0, ih1, and_assoc]

theorem Protocol.trace_rectangle (p : Protocol X Y) (t : List Bool) :
    ∃ (L : X → Prop) (R : Y → Prop), ∀ x y, p.trace x y = t ↔ L x ∧ R y := by
  by_cases ht : ∃ a : p.Leaf, p.leafTrace a = t
  · obtain ⟨a, rfl⟩ := ht
    exact ⟨p.leftFiber a, p.rightFiber a, p.transcript_fiber_rectangle a⟩
  · refine ⟨fun _ => False, fun _ => True, fun x y => ?_⟩
    have hn : p.trace x y ≠ t := by
      intro he
      exact ht ⟨p.leafFor x y, (p.leafTrace_leafFor x y).trans he⟩
    simp [hn]

def Protocol.leftFinset [Fintype X] (p : Protocol X Y) (t : p.Leaf) : Finset X :=
  univ.filter (p.leftFiber t)

def Protocol.rightFinset [Fintype Y] (p : Protocol X Y) (t : p.Leaf) : Finset Y :=
  univ.filter (p.rightFiber t)

end
end SetCover.Paper
