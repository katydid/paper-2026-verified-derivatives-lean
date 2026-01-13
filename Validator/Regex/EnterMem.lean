import Validator.Std.Memoize

import Validator.Regex.Regex
import Validator.Regex.Enter

namespace Regex

def enterM [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (MemTable (@enter σ)) m]
  (param: Regex σ): m { res // res = enter param } :=
  MemTable.call enter param

instance [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (MemTable (@enter σ)) m]:
  Memoize (α := Regex σ) (β := fun r => Vector σ (symbols r)) enter m where
  call param := enterM param

private theorem enterM_is_correct [DecidableEq σ] [Hashable σ] (param: Regex σ) (table: (MemTable (@enter σ))):
  enter param = (StateM.run (s := table) (enterM param)).1 := by
  generalize (StateM.run (enterM param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]
