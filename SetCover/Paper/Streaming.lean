import SetCover.Paper.Basic

namespace SetCover.Paper

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

abbrev Memory (S : ℕ) := Fin S → Bool

/-- An item-by-item streaming machine. Time/pass/position may be used freely.
`prepare` includes any processing of the fixed known cheap prefix.
The final output may inspect the last input vector, which only strengthens the model. -/
structure StreamingMachine (p S v r s : ℕ) (Out : Type*) where
  initial : Memory S
  prepare : Fin p → Memory S → Memory S
  step : Fin p → (Fin r ⊕ Fin s) → Memory S → Cube v → Memory S
  finish : Memory S → Cube v → Out

def StreamingMachine.tableEquiv {p S v r s : ℕ} {Out : Type*} :
    StreamingMachine p S v r s Out ≃
      Memory S × (Fin p → Memory S → Memory S) ×
        (Fin p → (Fin r ⊕ Fin s) → Memory S → Cube v → Memory S) ×
        (Memory S → Cube v → Out) where
  toFun m := (m.initial, m.prepare, m.step, m.finish)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv m := by cases m; rfl
  right_inv t := by rcases t with ⟨a,b,c,d⟩; rfl

set_option synthInstance.maxSize 1024 in
instance {p S v r s : ℕ} {Out : Type*} [Fintype Out] :
    Fintype (StreamingMachine p S v r s Out) := by
  classical
  exact Fintype.ofEquiv _
    (StreamingMachine.tableEquiv (p := p) (S := S) (v := v) (r := r) (s := s) (Out := Out)).symm

def streamIndices (r s : ℕ) : List (Fin r ⊕ Fin s) :=
  (List.finRange r).map Sum.inl ++ (List.finRange s).map Sum.inr

def lastRight {v s : ℕ} (y : Block v s) : Cube v :=
  if h : 0 < s then y ⟨s - 1, by omega⟩ else zeroVector

def StreamingMachine.runPrefix {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (q : Fin p) (st : Memory S) (x : Block v r) :
    Memory S :=
  (List.finRange r).foldl (fun state i => m.step q (Sum.inl i) state (x i)) (m.prepare q st)

def StreamingMachine.runSuffix {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (q : Fin p) (st : Memory S) (y : Block v s) :
    Memory S :=
  (List.finRange s).foldl (fun state j => m.step q (Sum.inr j) state (y j)) st

def StreamingMachine.runPass {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (q : Fin p) (st : Memory S) (x : Input v r s) :
    Memory S :=
  (streamIndices r s).foldl (fun state i => m.step q i state (vectorAt x i)) (m.prepare q st)

theorem StreamingMachine.runPass_split {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (q : Fin p) (st : Memory S) (x : Input v r s) :
    m.runPass q st x = m.runSuffix q (m.runPrefix q st x.1) x.2 := by
  simp [runPass, runPrefix, runSuffix, streamIndices, List.foldl_append, List.foldl_map,
    vectorAt, Function.comp_def]

def StreamingMachine.runRounds {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (qs : List (Fin p)) (st : Memory S)
    (x : Input v r s) : Memory S :=
  qs.foldl (fun state q => m.runPass q state x) st

def StreamingMachine.run {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (x : Input v r s) : Out :=
  m.finish (m.runRounds (List.finRange p) m.initial x) (lastRight x.2)

def StreamingMachine.mapOutput {p S v r s : ℕ} {Out Out' : Type*}
    (m : StreamingMachine p S v r s Out) (f : Out → Out') :
    StreamingMachine p S v r s Out' where
  initial := m.initial
  prepare := m.prepare
  step := m.step
  finish st x := f (m.finish st x)

@[simp] theorem StreamingMachine.mapOutput_run {p S v r s : ℕ} {Out Out' : Type*}
    (m : StreamingMachine p S v r s Out) (f : Out → Out') (x : Input v r s) :
    (m.mapOutput f).run x = f (m.run x) := rfl

def sendAlice {X Y : Type*} :
    (S : ℕ) → (X → Memory S) → (Memory S → Protocol X Y) → Protocol X Y
  | 0, _, next => next (fun i => Fin.elim0 i)
  | S + 1, message, next =>
      .alice (fun x => message x 0)
        (sendAlice S (fun x i => message x i.succ) (fun tail => next (Fin.cons false tail)))
        (sendAlice S (fun x i => message x i.succ) (fun tail => next (Fin.cons true tail)))

def sendBob {X Y : Type*} :
    (S : ℕ) → (Y → Memory S) → (Memory S → Protocol X Y) → Protocol X Y
  | 0, _, next => next (fun i => Fin.elim0 i)
  | S + 1, message, next =>
      .bob (fun y => message y 0)
        (sendBob S (fun y i => message y i.succ) (fun tail => next (Fin.cons false tail)))
        (sendBob S (fun y i => message y i.succ) (fun tail => next (Fin.cons true tail)))

theorem sendAlice_run {X Y : Type*} (S : ℕ) (message : X → Memory S)
    (next : Memory S → Protocol X Y) (x : X) (y : Y) :
    (sendAlice S message next).run x y = (next (message x)).run x y := by
  induction S with
  | zero =>
      have h : (fun i : Fin 0 => Fin.elim0 i : Memory 0) = message x := by
        funext i
        exact Fin.elim0 i
      simp [sendAlice, h]
  | succ S ih =>
      simp only [sendAlice, Protocol.run]
      cases h : message x 0 <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      · rw [ih]
        have he : Fin.cons false (fun i => message x i.succ) = message x := by
          ext i
          cases i using Fin.cases <;> simp [h]
        rw [he]
      · rw [ih]
        have he : Fin.cons true (fun i => message x i.succ) = message x := by
          ext i
          cases i using Fin.cases <;> simp [h]
        rw [he]

theorem sendBob_run {X Y : Type*} (S : ℕ) (message : Y → Memory S)
    (next : Memory S → Protocol X Y) (x : X) (y : Y) :
    (sendBob S message next).run x y = (next (message y)).run x y := by
  induction S with
  | zero =>
      have h : (fun i : Fin 0 => Fin.elim0 i : Memory 0) = message y := by
        funext i
        exact Fin.elim0 i
      simp [sendBob, h]
  | succ S ih =>
      simp only [sendBob, Protocol.run]
      cases h : message y 0 <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      · rw [ih]
        have he : Fin.cons false (fun i => message y i.succ) = message y := by
          ext i
          cases i using Fin.cases <;> simp [h]
        rw [he]
      · rw [ih]
        have he : Fin.cons true (fun i => message y i.succ) = message y := by
          ext i
          cases i using Fin.cases <;> simp [h]
        rw [he]

theorem sendAlice_depth {X Y : Type*} (S : ℕ) (message : X → Memory S)
    (next : Memory S → Protocol X Y) {b : ℕ} (h : ∀ st, (next st).depth ≤ b) :
    (sendAlice S message next).depth ≤ S + b := by
  induction S with
  | zero => simpa [sendAlice] using h (fun i => Fin.elim0 i)
  | succ S ih =>
      simp only [sendAlice, Protocol.depth]
      have h₀ := ih (fun x i => message x i.succ) (fun tail => next (Fin.cons false tail))
        (fun st => h (Fin.cons false st))
      have h₁ := ih (fun x i => message x i.succ) (fun tail => next (Fin.cons true tail))
        (fun st => h (Fin.cons true st))
      omega

theorem sendBob_depth {X Y : Type*} (S : ℕ) (message : Y → Memory S)
    (next : Memory S → Protocol X Y) {b : ℕ} (h : ∀ st, (next st).depth ≤ b) :
    (sendBob S message next).depth ≤ S + b := by
  induction S with
  | zero => simpa [sendBob] using h (fun i => Fin.elim0 i)
  | succ S ih =>
      simp only [sendBob, Protocol.depth]
      have h₀ := ih (fun y i => message y i.succ) (fun tail => next (Fin.cons false tail))
        (fun st => h (Fin.cons false st))
      have h₁ := ih (fun y i => message y i.succ) (fun tail => next (Fin.cons true tail))
        (fun st => h (Fin.cons true st))
      omega

def StreamingMachine.protocolRounds {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (decideOutput : Out → Bool) :
    List (Fin p) → Memory S → Protocol (Block v r) (Block v s)
  | [], st => .bob (fun y => decideOutput (m.finish st (lastRight y))) (.leaf false) (.leaf true)
  | q :: qs, st =>
      sendAlice S (fun x => m.runPrefix q st x) (fun st₁ =>
        sendBob S (fun y => m.runSuffix q st₁ y) (fun st₂ =>
          m.protocolRounds decideOutput qs st₂))

theorem StreamingMachine.protocolRounds_run {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (decideOutput : Out → Bool)
    (qs : List (Fin p)) (st : Memory S) (x : Input v r s) :
    (m.protocolRounds decideOutput qs st).run x.1 x.2 =
      decideOutput (m.finish (m.runRounds qs st x) (lastRight x.2)) := by
  induction qs generalizing st with
  | nil =>
      simp only [protocolRounds, Protocol.run, runRounds, List.foldl_nil]
      cases decideOutput (m.finish st (lastRight x.2)) <;> rfl
  | cons q qs ih =>
      simp only [protocolRounds, sendAlice_run, sendBob_run, ih, runRounds,
        List.foldl_cons, runPass_split]

theorem StreamingMachine.protocolRounds_depth {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (decideOutput : Out → Bool)
    (qs : List (Fin p)) (st : Memory S) :
    (m.protocolRounds decideOutput qs st).depth ≤ 2 * qs.length * S + 1 := by
  induction qs generalizing st with
  | nil => simp [protocolRounds, Protocol.depth]
  | cons q qs ih =>
      have h : (m.protocolRounds decideOutput (q :: qs) st).depth ≤
          S + (S + (2 * qs.length * S + 1)) := by
        apply sendAlice_depth
        intro st₁
        apply sendBob_depth
        intro st₂
        exact ih st₂
      simp only [List.length_cons]
      nlinarith

def StreamingMachine.protocol {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (decideOutput : Out → Bool) :
    Protocol (Block v r) (Block v s) :=
  m.protocolRounds decideOutput (List.finRange p) m.initial

theorem StreamingMachine.protocol_run {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (decideOutput : Out → Bool) (x : Input v r s) :
    (m.protocol decideOutput).run x.1 x.2 = decideOutput (m.run x) :=
  m.protocolRounds_run decideOutput _ _ _

/-- The extra final state return is harmless. Keeping the `+1` avoids assuming S ≥ 1. -/
theorem StreamingMachine.protocol_depth {p S v r s : ℕ} {Out : Type*}
    (m : StreamingMachine p S v r s Out) (decideOutput : Out → Bool) :
    (m.protocol decideOutput).depth ≤ 2 * p * S + 1 := by
  simpa [protocol, List.length_finRange] using
    m.protocolRounds_depth decideOutput (List.finRange p) m.initial

end
end SetCover.Paper
