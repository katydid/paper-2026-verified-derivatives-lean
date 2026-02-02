-- StateMemoize is an example of now VerifiedFilter.Std.Memoize.Memoize can be used to optimize fibonacci.

import VerifiedFilter.Std.State
import VerifiedFilter.Std.Memoize.Memoize

-- MemTable.StateM.run is an example of how we can run StateM when a state MemTable.
private def MemTable.StateM.run
  {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type}
  (f: (a: α) -> β a) (a: α) (table: MemTable f): ({b: β a // b = f a} × MemTable f) :=
  MemTable.call (m := StateM (MemTable f)) f a table

-- We prove that for any table, function and input, that
-- running with a State monad is the same as just calling the function.
private theorem MemTable.StateM.call_is_correct {α: Type} {β: α -> Type}
  [DecidableEq α] [Hashable α] (f: (a: α) -> β a)
  (table: MemTable f) (a: α):
  (MemTable.call (m := StateM (MemTable f)) f a table).fst.val = f a := by
  generalize ((MemTable.call (m := StateM (MemTable f)) f a table).fst) = x
  obtain ⟨x, hx⟩ := x
  simp only
  rw [hx]

-- Memoize.StateM.call is an example of how we can call the MemTable via the State monad,
-- generically, where no specific state instance (for example MemTable) has been specified.
private def Memoize.StateM.call
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  [memf: Memoize f (StateM σ)]
  (a: α): StateM σ {b: β a // b = f a} :=
  memf.call a

-- We prove that for any state, function and input, that
-- calling Memoize via the State monad is the same as just calling the function.
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

-- Memoize.StateM.run is an example of how we can run a Memoize State monad,
-- generically, where no specific state instance (for example MemTable) has been specified.
-- This returns the value and state outside of the monad.
private def Memoize.StateM.run
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  {σ: Type}
  [memf: Memoize f (StateM σ)]
  (a: α) (state: σ): {b: β a // b = f a} × σ :=
  Memoize.StateM.call f a state

-- Memoize.StateM.run' is an example of how we can run a Memoize State monad,
-- generically, where no specific state instance (for example MemTable) has been specified.
-- This returns just the value outside of the monad.
private def Memoize.StateM.run'
  {α: Type}
  [DecidableEq α] [Hashable α]
  {β: α -> Type}
  (f: (a: α) -> β a)
  {σ: Type}
  [memf: Memoize f (StateM σ)]
  (a: α) (state: σ): {b: β a // b = f a} :=
  (Memoize.StateM.run f a state).1

-- We prove that for any state, function and parameter,
-- generically, where no specific state instance (for example MemTable) has been specified,
-- that run Memoize via a State monad is the same as just calling the function.
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

-- Example of using memoization.

-- fib is a pure fibonacci function.
private def fib (n: Nat): Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- We declare a Memoize instance for any monad that implements MonadState where (MemTable fib) is the state.
private instance [Monad m] [MonadState (MemTable fib) m]: Memoize fib m where
  call n := MemTable.call fib n

-- fibM' is a helper function for fibM.
-- Every recursive fibonacci call, is a memoized call and returns a proof that the value is correctly calculated according to `fib`.
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

-- fibM is a recursively memoized version of fib.
private def fibM (n: Nat): Nat :=
  (StateM.run (s := MemTable.init fib) (fibM' n)).1

-- fibM'_is_correct is a helper proof for fibM_is_correct.
-- We prove that `fibM'` always returns the correct result according to `fib`.
private theorem fibM'_is_correct (table: MemTable fib) (n: Nat): fib n = (StateM.run (s := table) (fibM' n)).1 := by
  generalize (StateM.run (fibM' n) table) = x
  obtain ⟨⟨b, hb⟩, table'⟩ := x
  simp only
  rw [hb]

-- We prove that `fibM` always returns the correct result according to `fib`.
private theorem fibM_is_correct (n: Nat): fib n = fibM n := by
  unfold fibM
  rw [<- fibM'_is_correct]
