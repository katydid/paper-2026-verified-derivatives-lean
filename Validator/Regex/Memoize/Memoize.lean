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

namespace Regex.Memoize

class MemoizeRoom (m: Type -> Type u) (σ: Type) [DecidableEq σ] [Hashable σ] where
  enterM : (a: enterParam σ) -> m { b: enterResult a // b = enter a }
  leaveM : (a: leaveParam σ) -> m { b: leaveResult a // b = leave a }

instance (m: Type -> Type u) (σ: Type) [DecidableEq σ] [Hashable σ] [Monad m]
  [DecidableEq (enterParam σ)] [Hashable (enterParam σ)]
  [Memoize (α := enterParam σ) (β := enterResult) enter m]
  [enterState: MonadState (enterMemTable σ) m]
  [DecidableEq (leaveParam σ)] [Hashable (leaveParam σ)]
  [Memoize (α := leaveParam σ) (β := leaveResult) leave m]
  [leaveState: MonadState (leaveMemTable σ) m]
  : MemoizeRoom m σ where
  enterM param := MemTable.enter (monadState := enterState) param
  leaveM param := MemTable.leave (monadState := leaveState) param

def derive [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeRoom m σ]
  (Φ: σ → Bool) (r: Regex σ): m {dr: Regex σ // dr = Regex.Room.derive Φ r } := do
  let ⟨ifexpr, hifexpr⟩ <- MemoizeRoom.enterM r
  let ⟨res, hres⟩ <- MemoizeRoom.leaveM ⟨r, IfExpr.eval Φ ifexpr⟩
  let h: res = r.leave (IfExpr.eval Φ r.enter) := by
    unfold leave at hres
    simp only at hres
    rw [hifexpr] at hres
    assumption
  pure (Subtype.mk res h)

private def StateM.derive [DecidableEq σ] [Hashable σ] (Φ: σ → Bool) (r: Regex σ)
  : StateT (enterMemTable σ) (StateM (leaveMemTable σ)) (Regex σ) :=
  Regex.Memoize.derive Φ r

private def StateM.derive.run [DecidableEq σ] [Hashable σ]
  (enterState: enterMemTable σ) (leaveState: leaveMemTable σ)
  (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  ((StateM.run (StateT.run (Regex.Memoize.derive Φ r) enterState) leaveState).1).1

theorem run_is_correct [DecidableEq σ] [Hashable σ]
  (enterState: enterMemTable σ) (leaveState: leaveMemTable σ)
  (Φ: σ → Bool) (r: Regex σ):
  StateM.derive.run enterState leaveState Φ r = Regex.Room.derive Φ r := by
  unfold StateM.derive.run
  generalize ((StateM.run (StateT.run (Regex.Memoize.derive Φ r) enterState) leaveState)).1.1 = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

#guard StateM.derive.run (MemTable.init enter) (MemTable.init leave)
  (· == 'a') (Regex.or (Regex.symbol 'a') (Regex.symbol 'b'))
  = Regex.or Regex.emptystr Regex.emptyset
