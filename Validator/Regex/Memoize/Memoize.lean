import Validator.Std.Vec
import Validator.Std.Memoize

import Validator.Regex.Drawer
import Validator.Regex.IfExpr
import Validator.Regex.Lang
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.Room

import Validator.Regex.Memoize.Enter
import Validator.Regex.Memoize.Leave

namespace Regex

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
  (Φ: σ → Bool) (r: Regex σ): m {dr: Regex σ // dr = Regex.Room.derive Φ r } := do
  let ⟨ifexpr, hifexpr⟩ <- MemoizeRoom.enterM r
  let ⟨res, hres⟩ <- MemoizeRoom.leaveM ⟨r, IfExpr.eval Φ ifexpr⟩
  let h: res = r.leave (IfExpr.eval Φ r.enter) := by
    unfold leave2 at hres
    simp only at hres
    rw [hifexpr] at hres
    assumption
  pure (Subtype.mk res h)

private def Regex.Mem.StateM.derive [DecidableEq σ] [Hashable σ] (Φ: σ → Bool) (r: Regex σ)
  : StateT (enterMemTable σ) (StateM (leaveMemTable σ)) (Regex σ) :=
  Regex.Mem.derive Φ r

private def Regex.Mem.StateM.derive.run [DecidableEq σ] [Hashable σ] (Φ: σ → Bool) (r: Regex σ)
  (enterState: Regex.enterMemTable σ) (leaveState: Regex.leaveMemTable σ): Regex σ :=
  ((StateM.run (StateT.run (Regex.Mem.derive Φ r) enterState) leaveState).1).1

theorem run_is_correct [DecidableEq σ] [Hashable σ] (Φ: σ → Bool) (r: Regex σ)
  (enterState: Regex.enterMemTable σ) (leaveState: Regex.leaveMemTable σ):
  Regex.Mem.StateM.derive.run Φ r enterState leaveState = Regex.Room.derive Φ r := by
  unfold Regex.Mem.StateM.derive.run
  generalize ((StateM.run (StateT.run (Regex.Mem.derive Φ r) enterState) leaveState)).1.1 = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

#guard Regex.Mem.StateM.derive.run (· == 'a') (Regex.or (Regex.symbol 'a') (Regex.symbol 'b')) (MemTable.init Regex.enter) (MemTable.init Regex.leave2)
  = Regex.or Regex.emptystr Regex.emptyset
