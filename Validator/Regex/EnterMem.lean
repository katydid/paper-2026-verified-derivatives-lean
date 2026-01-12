import Validator.Std.Memoize

import Validator.Regex.Regex
import Validator.Regex.Enter

namespace Regex

def enterM [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (MemTable (@enter σ)) m]
  (param: Regex σ): m { symbols // symbols = enter param } :=
  callM enter param

instance [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (MemTable (@enter σ)) m]:
  Memoize m (α := Regex σ) (β := fun r => Vector σ (symbols r)) enter where
  call param := enterM param

private theorem enterM_is_correct [DecidableEq σ] [Hashable σ] (param: Regex σ) (table: (MemTable (@enter σ))):
  enter param = (StateM.run (s := table) (enterM param)).1 := by
  have h := call_is_correct (@enter σ) table param
  unfold call at h
  unfold enterM
  rw [h]
