import Std

import Mathlib.Tactic.Linarith

import Validator.Std.State
import Validator.Std.Vec
import Validator.Std.Memoize.Memoize

https://github.com/leanprover/lean4/blob/1bf16f710ed7677c8331fd24f6d06ba66fc72e1c/src/Init/Control/StateRef.Lean
https://github.com/leanprover/lean4/blob/0bcac0d46cc76fd7410e0abec06dcda33fddf4d7/src/Lean/Meta/Transform.lean#L143
https://github.com/leanprover/lean4/blob/0bcac0d46cc76fd7410e0abec06dcda33fddf4d7/src/Lean/Util/MonadCache.lean#L62
https://github.com/leanprover/lean4/blob/b44c7e161c13f54e8cd3da3259aa659da8f6ab70/src/Lean/Parser/Term.lean#L936
https://github.com/leanprover/lean4/blob/b44c7e161c13f54e8cd3da3259aa659da8f6ab70/src/Lean/Elab/Frontend.lean#L27
https://github.com/leanprover/lean4/pull/8435/files

abbrev MemTableRefT'
  {α: Type} {β: α → Type} [DecidableEq α] [Hashable α]
  (ω) (f: (a: α) → β a) (m : Type → Type)
  [Monad m] [MonadLiftT (ST ω) m]
  := StateRefT' ω (MemTable f) m

instance
  {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a)
  {ω} (m : Type → Type) [Monad m] [MonadLiftT (ST ω) m]:
  MonadState (MemTable f) (MemTableRefT' ω f m) :=
  inferInstance

private def MemTable.MemRefT.call
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} {ω} {m : Type → Type} [MonadLiftT (ST ω) m] [Monad m]
  (f: (a: α) -> β a) (a: α): MemTableRefT' ω f m ({b: β a // b = f a}) :=
  MemTable.call (m := MemTableRefT' ω f m) f a

private def MemTable.MemRefT.run
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} {ω} {m : Type → Type} [MonadLiftT (ST ω) m] [Monad m]
  (f: (a: α) -> β a) (a: α) (table: MemTable f): m ({b: β a // b = f a} × MemTable f) :=
  StateRefT'.run (MemTable.call (m := MemTableRefT' ω f m) f a) table

private def MemTable.MemRefT.run'
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} {ω} {m : Type → Type} [MonadLiftT (ST ω) m] [Monad m]
  (f: (a: α) -> β a) (a: α) (table: MemTable f): m ({b: β a // b = f a}) :=
  StateRefT'.run' (MemTable.call (m := MemTableRefT' ω f m) f a) table

-- Example

private def fib (n: Nat): Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

instance [Monad m] [MonadState (MemTable fib) m]: Memoize fib m where
  call n := MemTable.call fib n

private def fibM' [Monad m] [MonadState (MemTable fib) m] [Memoize fib m] (n: Nat): m { b: Nat // b = fib n } := do
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

abbrev MemTableRefTIO
  {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a)
  := StateRefT (MemTable f) IO

instance
  {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a):
  MonadState (MemTable f) (MemTableRefTIO f) :=
  inferInstance

instance : Memoize fib (MemTableRefTIO fib) :=
  inferInstance

#eval StateRefT'.run' (ω := IORealWorld Nat) (fibM' 4) (MemTable.init fib)

def MemTableRefTIO.run'
  (x : MemTableRefTIO fib Nat) (n: Nat) : IO { res: Nat // res = fib n } :=
  StateRefT'.run' (fibM' n) (MemTable.init fib)

private def fibM (n: Nat): IO Nat :=
  (StateRefT'.run' (fibM' n) (MemTable.init fib))

private theorem fibM'_is_correct (table: MemTable fib) (n: Nat): fib n = (StateM.run (s := table) (fibM' n)).1 := by
  generalize (StateM.run (fibM' n) table) = x
  obtain ⟨⟨b, hb⟩, table'⟩ := x
  simp only
  rw [hb]

private theorem fibM_is_correct (n: Nat): fib n = fibM n := by
  unfold fibM
  rw [<- fibM'_is_correct]
