import Validator.Std.Vec
import Validator.Std.Memoize

import Validator.Regex.Drawer
import Validator.Regex.Lang
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.Katydid

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

def Regex.Memoize.derive [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeRoom m σ]
  (Φ: σ → Bool) (r: Regex σ): m {dr: Regex σ // dr = Regex.Room.derive Φ r } := do
  let ⟨symbols, hsymbols⟩ <- MemoizeRoom.enterM r
  let ⟨res, hres⟩ <- MemoizeRoom.leaveM ⟨r, Vector.map Φ symbols⟩
  let h: res = Regex.Room.derive Φ r := by
    unfold leave at hres
    simp only at hres
    rw [hsymbols] at hres
    assumption
  pure (Subtype.mk res h)

abbrev StateMemoize σ [DecidableEq σ] [Hashable σ] := StateT (enterMemTable σ) (StateM (leaveMemTable σ))
abbrev memoizeState σ [DecidableEq σ] [Hashable σ] := (enterMemTable σ × leaveMemTable σ)
def memoizeState.init {σ: Type} [DecidableEq σ] [Hashable σ]: memoizeState σ := ((MemTable.init enter), (MemTable.init leave))

def StateMemoize.run {σ: Type} {β: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (f: StateMemoize σ β): β :=
  ((StateM.run (StateT.run f state.1) state.2).1).1

def StateMemoize.Regex.derive [DecidableEq σ] [Hashable σ] (Φ: σ → Bool) (r: Regex σ): StateMemoize σ (Regex σ) :=
  Regex.Memoize.derive Φ r

def StateMemoize.Regex.derive.run {σ: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  StateMemoize.run state (Regex.Memoize.derive Φ r)

#guard StateMemoize.Regex.derive.run memoizeState.init
  (· == 'a') (Regex.or (Regex.symbol 'a') (Regex.symbol 'b'))
  = Regex.or Regex.emptystr Regex.emptyset

def validate [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeRoom m σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): m Bool :=
  null <$> (List.foldlM (fun dr x => Regex.Memoize.derive (flip Φ x) dr) r xs)

def StateMemoize.Regex.validate [DecidableEq σ] [Hashable σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): StateMemoize σ Bool :=
  Regex.Memoize.validate Φ r xs

def StateMemoize.Regex.validate.run {σ: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Bool :=
  StateMemoize.run state (StateMemoize.Regex.validate Φ r xs)

#guard StateMemoize.Regex.validate.run memoizeState.init
  (· == ·) (Regex.or (Regex.symbol 'a') (Regex.symbol 'b')) ['a']
  = true

def filter  [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeRoom m σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): m (List (List α)) :=
  List.filterM (validate Φ r) xss

def StateMemoize.Regex.filter [DecidableEq σ] [Hashable σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): StateMemoize σ (List (List α)) :=
  Regex.Memoize.filter Φ r xss

def StateMemoize.Regex.filter.run [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ)
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): List (List α) :=
  StateMemoize.run state (StateMemoize.Regex.filter Φ r xss)

lemma StateMemoize.Regex.derive.run_unfold [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → Bool) (r: Regex σ):
  (StateMemoize.Regex.derive.run state Φ r) = StateMemoize.run state (Regex.Memoize.derive Φ r) :=
  rfl

theorem StateMemoize.Regex.derive.run_is_sound [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ)
  (Φ: σ → Bool) (r: Regex σ):
  StateMemoize.Regex.derive.run state Φ r = Regex.Room.derive Φ r := by
  rw [StateMemoize.Regex.derive.run_unfold]
  generalize StateMemoize.run state (Regex.Memoize.derive Φ r) = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

theorem Regex.StateMemoize.derive_commutes {σ: Type} {α: Type} [DecidableEq σ] [Hashable σ]
  (state: memoizeState σ) (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (a: α):
  denote Φ (StateMemoize.Regex.derive.run state (flip (decideRel Φ) a) r) = Lang.derive (denote Φ r) a := by
  rw [StateMemoize.Regex.derive.run_is_sound]
  rw [<- Regex.Room.derive_commutes]
