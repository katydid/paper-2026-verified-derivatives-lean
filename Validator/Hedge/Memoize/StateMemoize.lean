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

def StateMemoize.Grammar.validate.run [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α): Bool :=
  StateMemoize.run state (Grammar.Memoize.validate G Φ nodes)

def StateMemoize.Grammar.filter.run [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (xss: List (Hedge α)): List (Hedge α) :=
  StateMemoize.run state (Grammar.Memoize.filter G Φ xss)

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

lemma StateMemoize.Grammar.validate.run_unfold [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α):
  (StateMemoize.Grammar.validate.run state G Φ nodes) = StateMemoize.run state (Grammar.Memoize.validate G Φ nodes) :=
  rfl

theorem StateMemoize.validate.run_is_sound {φ: Type} {α: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (nodes: Hedge α):
  StateMemoize.Grammar.validate.run state G (decideRel Φ) nodes = Grammar.Katydid.validate G (decideRel Φ) nodes := by
  rw [StateMemoize.Grammar.validate.run_unfold]
  generalize StateMemoize.run state (Grammar.Memoize.validate G (decideRel Φ) nodes) = x
  obtain ⟨b, hd⟩ := x
  simp only
  assumption

theorem Regex.StateMemoize.validate_commutes {φ: Type} {α: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (nodes: Hedge α):
  StateMemoize.Grammar.validate.run state G (decideRel Φ) nodes = Grammar.denote G Φ nodes := by
  rw [StateMemoize.validate.run_is_sound]
  rw [<- Grammar.Katydid.validate_commutes]

lemma StateMemoize.Grammar.filter.run_unfold {φ: Type} {α: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (xss: List (Hedge α)):
  (StateMemoize.Grammar.filter.run state G Φ xss) = StateMemoize.run state (Grammar.Memoize.filter G Φ xss) :=
  rfl

theorem Grammar.StateMemoize.mem_filter {φ: Type} {α: Type} [DecidableEq φ] [Hashable φ]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (xss: List (Hedge α)):
  ∀ xs, (xs ∈ StateMemoize.Grammar.filter.run state G (decideRel Φ) xss) ↔ (Lang.MemFilter (Grammar.denote G Φ) xss xs) := by
  intro xs
  rw [StateMemoize.Grammar.filter.run_unfold]
  generalize StateMemoize.run state (Grammar.Memoize.filter G (decideRel Φ) xss) = x
  obtain ⟨res, hres⟩ := x
  simp only
  rw [hres]
  unfold Katydid.filter
  rw [List.mem_filter]
  unfold Lang.MemFilter
  rw [Katydid.validate_commutes]
