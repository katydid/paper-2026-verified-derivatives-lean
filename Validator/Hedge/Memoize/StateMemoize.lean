import Mathlib.Tactic.SimpRw

import Validator.Std.Decidable
import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Regex.Lang
import Validator.Regex.Katydid
import Validator.Regex.Enter
import Validator.Regex.Memoize.Memoize
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Hedge.Katydid
import Validator.Hedge.Lang
import Validator.Hedge.Denote

import Validator.Hedge.Memoize.Memoize

open Regex.Memoize

namespace Hedge

def StateMemoize.Grammar.derive.run {φ: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  StateMemoize.run state (Grammar.Memoize.derive G Φ r node)

lemma StateMemoize.Grammar.derive.run_unfold {φ: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α):
  (StateMemoize.Grammar.derive.run state G Φ r node) = StateMemoize.run state (Grammar.Memoize.derive G Φ r node) :=
  rfl

theorem StateMemoize.Grammar.derive.run_is_sound [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n))
  (Φ: φ → α → Bool) (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  StateMemoize.Grammar.derive.run state G Φ r node = Grammar.Katydid.derive G Φ r node := by
  rw [StateMemoize.Grammar.derive.run_unfold]
  generalize StateMemoize.run state (Grammar.Memoize.derive G Φ r node) = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

theorem StateMemoize.Grammar.derive_commutes [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n))
  (Φ: φ → α → Prop) [DecidableRel Φ]
  (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  Grammar.Rule.denote G Φ (StateMemoize.Grammar.derive.run state G (decideRel Φ) r node)
  = Lang.derive (Grammar.Rule.denote G Φ r) node := by
  rw [StateMemoize.Grammar.derive.run_is_sound]
  rw [<- Grammar.Katydid.derive_commutes]
