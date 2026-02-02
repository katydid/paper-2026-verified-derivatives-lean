import Std

import VerifiedFilter.Std.State
import VerifiedFilter.Std.Vector
import VerifiedFilter.Std.Memoize.Memoize

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

def Memoize.StateM.call
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  [memf: Memoize f (StateM σ)]
  (a: α): StateM σ {b: β a // b = f a} :=
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
