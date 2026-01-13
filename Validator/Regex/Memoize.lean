import Validator.Std.Vec
import Validator.Std.Memoize

import Validator.Regex.EnterMem
import Validator.Regex.Drawer
import Validator.Regex.Lang
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex

def Regex.Mem.derive
  [DecidableEq σ] [Hashable σ]
  [mementer: MemoizedEnter σ]
  (Φ: σ → Bool) (r: Regex σ): StateM (MemTable (@enter σ)) (Regex σ) := do
  let ⟨ss, _⟩ <- mementer.call r
  let bools := Vector.map Φ ss
  return leave r bools
