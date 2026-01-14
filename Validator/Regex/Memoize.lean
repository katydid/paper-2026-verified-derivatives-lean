import Validator.Std.Vec
import Validator.Std.Memoize

import Validator.Regex.EnterMem
import Validator.Regex.Drawer
import Validator.Regex.IfExpr
import Validator.Regex.Lang
import Validator.Regex.Leave
import Validator.Regex.LeaveMem
import Validator.Regex.Num
import Validator.Regex.Regex

namespace Regex

-- class Memoize {α: Type} [DecidableEq α] [Hashable α] {β: α -> Type} (f: (a: α) → β a) (m: Type -> Type u) where
--   call : (a: α) -> m { b: β a // b = f a }

class MemoizeRoom (m: Type -> Type u) (σ: Type) [DecidableEq σ] [Hashable σ] where
  enterM : (a: enterParam σ) -> m { b: enterResult a // b = enter a }
  leaveM : (a: leaveParam σ) -> m { b: leaveResult a // b = leave2 a }

instance (m: Type -> Type u) (σ: Type) [DecidableEq σ] [Hashable σ] [Monad m]
  [DecidableEq (enterParam σ)] [Hashable (enterParam σ)]
  [Memoize (α := enterParam σ) (β := enterResult) enter m]
  [enterState: MonadState (enterMemTable σ) m]
  [DecidableEq (leaveParam σ)] [Hashable (leaveParam σ)]
  [Memoize (α := leaveParam σ) (β := leaveResult) leave2 m]
  [leaveState: MonadState (leaveMemTable σ) m]
  : MemoizeRoom m σ where
  enterM param := MemTable.enterM (monadState := enterState) param
  leaveM param := MemTable.leaveM (monadState := leaveState) param

end Regex

def Regex.Mem.derive [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeRoom m σ]
  (Φ: σ → Bool) (r: Regex σ): m (Regex σ) := do
  let ifexpr <- MemoizeRoom.enterM r
  MemoizeRoom.leaveM ⟨r, IfExpr.eval Φ ifexpr⟩
