import Validator.Std.Hashable
import Validator.Std.Memoize

import Validator.Regex.Regex
import Validator.Regex.Leave

namespace Regex

abbrev leaveParam (σ: Type) := Σ (r: Regex σ), (Vector Bool (symbols r))
abbrev leaveResult {σ: Type} (_: leaveParam σ) := Regex σ

def leave2 {σ: Type}: (a: leaveParam σ) → leaveResult a
  | ⟨r, bools⟩ => leave r bools

abbrev leaveMemTable (σ: Type) [DecidableEq σ] [Hashable σ] := MemTable leave2 (α := leaveParam σ)

def MemTable.leaveM {σ: Type} [DecidableEq σ] [Hashable σ] [Monad m] [monadState: MonadState (leaveMemTable σ) m]
  (param: leaveParam σ): m { res // res = leave2 param } :=
  MemTable.call leave2 param

private theorem MemTable.leaveM_is_correct [DecidableEq σ] [Hashable σ] (param: leaveParam σ) (table: leaveMemTable σ):
  leave2 param = (StateM.run (s := table) (leaveM param)).1 := by
  generalize (StateM.run (leaveM param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]

instance {σ: Type} [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (leaveMemTable σ) m]:
  Memoize (α := leaveParam σ) (β := leaveResult) leave2 m where
  call param := MemTable.leaveM param

abbrev MemoizedLeave (σ: Type) [DecidableEq σ] [Hashable σ] := Memoize (@leave2 σ) (StateM (leaveMemTable σ))

private theorem Memoize.StateM.leaveM_is_correct
  [DecidableEq σ] [Hashable σ] [memleave: MemoizedLeave σ]
  (param: leaveParam σ) (table: leaveMemTable σ):
  leave2 param = (memleave.call param table).1 := by
  generalize (memleave.call param table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]
