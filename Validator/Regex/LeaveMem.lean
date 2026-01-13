import Validator.Std.Hashable
import Validator.Std.Memoize

import Validator.Regex.Regex
import Validator.Regex.Leave

namespace Regex

def leave2 {σ: Type}: (Σ (r: Regex σ), (Vector Bool (symbols r))) → Regex σ
  | ⟨r, bools⟩ => leave r bools

def leaveM {σ: Type} [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (MemTable leave2 (α := (Σ (r: Regex σ), (Vector Bool (symbols r))))) m]
  (param: Σ (r: Regex σ), (Vector Bool (symbols r))): m { res // res = leave2 param } :=
  MemTable.call leave2 param

instance {σ: Type} [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (MemTable leave2 (α := (Σ (r: Regex σ), (Vector Bool (symbols r))))) m]:
  Memoize (α := (Σ (r: Regex σ), (Vector Bool (symbols r)))) (β := fun _ => Regex σ) leave2 m where
  call param := leaveM param

private theorem leaveM_is_correct [DecidableEq σ] [Hashable σ] (param: Σ (r: Regex σ), (Vector Bool (symbols r))) (table: (MemTable (@leave2 σ))):
  leave2 param = (StateM.run (s := table) (leaveM param)).1 := by
  generalize (StateM.run (leaveM param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]
