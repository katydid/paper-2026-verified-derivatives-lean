import Std

import Mathlib.Tactic.Linarith

import Validator.Std.State
import Validator.Std.Vec

abbrev MemTable {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a) :=
  Std.ExtDHashMap
    α
    (fun a =>
      { b: β a // b = f a }
    )

def MemTable.init {α: Type} {β: α -> Type} [DecidableEq α] [Hashable α]
  (f: (a: α) → β a): MemTable f := Std.ExtDHashMap.emptyWithCapacity

def MemTable.modifyGet
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type}
  (f: (a: α) -> β a)
  (a: α): MemTable f -> ({ b: β a // b = f a } × MemTable f) :=
  fun table =>
    match Std.ExtDHashMap.get? table a with
    | Option.none =>
      let b: { b: β a // b = f a } := Subtype.mk (f a) rfl
      (b, (Std.ExtDHashMap.insert table a b))
    | Option.some b =>
      (b, table)

def MemTable.call
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type}
  (f: (a: α) -> β a)
  [Monad m] [MonadState (MemTable f) m]
  (a: α): m { b: β a // b = f a } := do
  let table <- MonadState.get
  match Std.ExtDHashMap.get? table a with
  | Option.none =>
    let b: { b: β a // b = f a } := Subtype.mk (f a) rfl
    MonadState.set (Std.ExtDHashMap.insert table a b)
    return b
  | Option.some b => return b

private def MemTable.StateM.run
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type}
  (f: (a: α) -> β a) (a: α) (table: MemTable f): ({b: β a // b = f a} × MemTable f) :=
  MemTable.call (m := StateM (MemTable f)) f a table

private theorem MemTable.StateM.call_is_correct {α: Type} {β: α -> Type}
  [DecidableEq α] [Hashable α] (f: (a: α) -> β a)
  (table: MemTable f) (a: α):
  (MemTable.call (m := StateM (MemTable f)) f a table).fst.val = f a := by
  generalize ((MemTable.call (m := StateM (MemTable f)) f a table).fst) = x
  obtain ⟨x, hx⟩ := x
  simp only
  rw [hx]

-- consider {β: α -> outParam Type}
class Memoize {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} (f: (a: α) → β a) (m: Type -> Type u) where
  call : (a: α) -> m { b: β a // b = f a }
  -- An alternative would be to create a separate property from the call function, which would then be call : (a: α) -> m (β a)
  -- prop : (a: α) -> m Prop := fun a => (fun b => b = f a) <$> (call a)

def Memoize.call'
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  {m: Type -> Type u}
  [memf: Memoize f m]
  (a: α): m {b: β a // b = f a} :=
  memf.call a

def Memoize.StateM.call
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  [memf: Memoize f (StateM σ)]
  (a: α): StateM σ {b: β a // b = f a} :=
  memf.call a

def Memoize.STRef.call
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  [memf: Memoize f (ST.Ref σ)]
  (a: α): ST.Ref σ {b: β a // b = f a} :=
  memf.call a

theorem Memoize.StateM.call_is_correct
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  {σ: Type}
  [memf: Memoize f (StateM σ)]
  (a: α) (state: σ):
  (Memoize.StateM.call f a state).1 = f a := by
  generalize ((call f a state)) = x
  obtain ⟨⟨val, property⟩⟩ := x
  subst property
  simp only

def Memoize.StateM.run
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  {σ: Type}
  [memf: Memoize f (StateM σ)]
  (a: α) (state: σ): {b: β a // b = f a} × σ :=
  Memoize.StateM.call f a state

def Memoize.StateM.run'
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  {σ: Type}
  [memf: Memoize f (StateM σ)]
  (a: α) (state: σ): {b: β a // b = f a} :=
  (Memoize.StateM.run f a state).1

theorem Memoize.StateM.run'_is_correct {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  {σ: Type}
  [Memoize f (StateM σ)]
  (a: α) (state: σ):
  (Memoize.StateM.run' f a state) = f a := by
  generalize ((run' f a state)) = x
  obtain ⟨val, property⟩ := x
  subst property
  simp only

-- M version

class MemoizeStateM {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} (f: (a: α) → StateM σ (β a)) where
  call : (a: α) -> StateM σ { b: β a // ∀ state', b = (f a state').1 }

def MemoizeStateM.call'
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> StateM σ (β a))
  [memf: MemoizeStateM f]
  (a: α): StateM σ {b: β a // ∀ state', b = (f a state').1} :=
  memf.call a

theorem MemoizeStateM.call_is_correct
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  {σ: Type}
  (f: (a: α) -> StateM σ (β a))
  [memf: MemoizeStateM f]
  (a: α) (state: σ):
  (MemoizeStateM.call' f a state).1 = (f a state).1 := by
  generalize ((call' f a state)) = x
  obtain ⟨⟨val, property⟩⟩ := x
  rw [<- property]

def MemoizeStateM.run'
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  {σ: Type}
  (f: (a: α) -> StateM σ (β a))
  [memf: MemoizeStateM f]
  (a: α) (state: σ): {b: β a // ∀ state', b = (f a state').1} :=
  (MemoizeStateM.call' f a state).1

theorem MemoizeStateM.run'_is_correct {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  {σ: Type}
  (f: (a: α) -> StateM σ (β a))
  [MemoizeStateM f]
  (a: α) (state: σ):
  (MemoizeStateM.run' f a state) = (f a state).1 := by
  generalize ((run' f a state)) = x
  obtain ⟨val, property⟩ := x
  rw [<- property]

-- Example

private def fib (n: Nat): Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

instance [Monad m] [MonadState (MemTable fib) m]: Memoize fib m where
  call n := MemTable.call fib n

private def fibM' [Monad m] [MonadState (MemTable fib) m] [memfib: Memoize fib m] (n: Nat): m { b: Nat // b = fib n } := do
  match n with
  | 0 => pure ⟨0, rfl⟩
  | 1 => pure ⟨1, rfl⟩
  | n + 2 =>
    let fn1: { res: Nat // res = fib n } <- fibM' n
    let fn2: { res: Nat // res = fib (n + 1) } <- fibM' (n + 1)
    let result: { res: Nat // res = fib (n + 2) } := Subtype.mk
      (fn1.val + fn2.val)
      (by obtain ⟨fn1, hfn1⟩ := fn1; obtain ⟨fn2, hfn2⟩ := fn2; unfold fib; subst_vars; rfl)
    pure result

private def fibM (n: Nat): Nat :=
  (StateM.run (s := MemTable.init fib) (fibM' n)).1

private theorem fibM'_is_correct (table: MemTable fib) (n: Nat): fib n = (StateM.run (s := table) (fibM' n)).1 := by
  generalize (StateM.run (fibM' n) table) = x
  obtain ⟨⟨b, hb⟩, table'⟩ := x
  simp only
  rw [hb]

private theorem fibM_is_correct (n: Nat): fib n = fibM n := by
  unfold fibM
  rw [<- fibM'_is_correct]

def Vector.mapMemoize [Monad m]
  (puref: α -> β) (memf: (a: α) -> m {res // res = puref a}) (xs : Vector α n)
  : m {ys: (Vector β n) // ys = Vector.map puref xs } := do
  go 0 (Nat.zero_le n) ⟨#v[], by simp⟩
where
  go (k : Nat) (h : k ≤ n) (acc : {ys: (Vector β k) // ys = Vector.cast (by omega) (Vector.map puref (Vector.take xs k)) })
    : m {ys: (Vector β n) // ys = Vector.map puref xs } := do
      if h' : k < n then
        memf xs[k] >>=
          fun xsk =>
            go (k+1) (by omega) (Subtype.mk (acc.val.push xsk) (by
              obtain ⟨acc, hacc⟩ := acc
              simp only
              rw [hacc]
              obtain ⟨xsk, hxsk⟩ := xsk
              simp only
              rw [hxsk]
              apply Vector.eq
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [Vector.toList_take]
              rw [Vector.toList_push]
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [Vector.toList_take]
              rw [<- hxsk]
              cases n with
              | zero =>
                contradiction
              | succ n' =>
                rw [Vector.take_succ_toList (h := by omega)]
                rw [List.map_append]
                congr
            ))
      else
        return ⟨Vector.cast (by omega) acc.val, by
          generalize_proofs h1 h2
          obtain ⟨acc, hacc⟩ := acc
          simp only
          rw [hacc]
          aesop
        ⟩

def List.foldlMemoizeWithMembership [Monad m] (puref: β -> α -> β) (xs: List α)
  (memf: (acc: β) -> (a: {a': α // a' ∈ xs}) -> m {res: β // res = puref acc a } )
  (init: β)
  : m {res': β // res' = List.foldl puref init xs } :=
  match xs with
  | [] => pure ⟨init, rfl⟩
  | (x::xs') => do
    let fx <- memf init (Subtype.mk x (by simp))
    let fxs <- List.foldlMemoizeWithMembership puref xs' (fun acc a => do
      let ⟨b, hb⟩ := a
      let a'': { a' // a' ∈ x :: xs' } := Subtype.mk b (by
        aesop
      )
      let f': { res // res = puref acc a''.val } <- memf acc a''
      let f'': { res // res = puref acc b } := by
        subst a''
        simp only at f'
        assumption
      pure f''
    ) fx.val
    pure (Subtype.mk fxs.val (by
      obtain ⟨fxs, hfxs⟩ := fxs
      simp only
      obtain ⟨fx, hfx⟩ := fx
      simp only at hfxs
      rw [hfxs]
      rw [hfx]
      simp only
      simp only [List.foldl]
    ))
