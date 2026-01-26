import Std

import Mathlib.Tactic.Linarith

import Validator.Std.State
import Validator.Std.Vec
import Validator.Std.Memoize.Memoize

def MemRefT
  {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a)
  {ω} (m : Type → Type) [Monad m] [MonadLiftT (ST ω) m]
  := StateRefT' ω (MemTable f) m

instance
  {α: Type} {β: α → Type} [DecidableEq α] [Hashable α] (f: (a: α) → β a)
  {ω} (m : Type → Type) [Monad m] [MonadLiftT (ST ω) m]:
  MonadStateOf (MemTable f) (StateRefT' ω (MemTable f) m) :=
  inferInstance

def callme
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type}
  (f: (a: α) -> β a)
  [Monad m] [MonadStateOf (MemTable f) m]
  (a: α): m { b: β a // b = f a } := do
  let table <- MonadState.get
  match Std.ExtDHashMap.get? table a with
  | Option.none =>
    let b: { b: β a // b = f a } := Subtype.mk (f a) rfl
    MonadState.set (Std.ExtDHashMap.insert table a b)
    return b
  | Option.some b => return b

private def MemTable.MemRefT.call
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} {ω} {m : Type → Type} [MonadLiftT (ST ω) m] [Monad m]
  (f: (a: α) -> β a) (a: α): StateRefT' ω (MemTable f) m ({b: β a // b = f a}) :=
  callme (m := StateRefT' ω (MemTable f) m) f a

private def MemTable.MemRefT.run
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} {ω} {m : Type → Type} [MonadLiftT (ST ω) m] [Monad m]
  (f: (a: α) -> β a) (a: α) (table: MemTable f): m ({b: β a // b = f a} × MemTable f) :=
  StateRefT'.run (callme (m := StateRefT' ω (MemTable f) m) f a) table

private def MemTable.MemRefT.run'
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} {ω} {m : Type → Type} [MonadLiftT (ST ω) m] [Monad m]
  (f: (a: α) -> β a) (a: α) (table: MemTable f): m ({b: β a // b = f a}) :=
  StateRefT'.run' (callme (m := StateRefT' ω (MemTable f) m) f a) table
