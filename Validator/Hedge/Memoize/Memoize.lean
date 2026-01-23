import Mathlib.Tactic.SimpRw

import Validator.Std.Decidable
import Validator.Std.Hedge

import Validator.Regex.Lang
import Validator.Regex.Room
import Validator.Regex.Memoize.Memoize
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Hedge.Room
import Validator.Hedge.Lang
import Validator.Hedge.Denote

import Validator.Regex.Memoize
open Regex.Memoize


namespace Hedge

-- def Grammar.Room.derive (G: Grammar n φ) (Φ: φ → α → Bool)
--   (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
--   let nodePred := (fun ((labelPred, ref): (φ × Ref n)) =>
--     let ⟨label, children⟩ := node
--     let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
--     Regex.null (List.foldl (Grammar.Room.derive G Φ) childr children)
--   )
--   Regex.Room.derive nodePred r

-- def Regex.Memoize.derive [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeRoom m σ]
--   (Φ: σ → Bool) (r: Regex σ): m {dr: Regex σ // dr = Regex.Room.derive Φ r } := do
--   let ⟨symbols, hsymbols⟩ <- MemoizeRoom.enterM r
--   let ⟨res, hres⟩ <- MemoizeRoom.leaveM ⟨r, Vector.map Φ symbols⟩
--   let h: res = Regex.Room.derive Φ r := by
--     unfold leave at hres
--     simp only at hres
--     rw [hsymbols] at hres
--     assumption
--   pure (Subtype.mk res h)

def Grammar.Memoize.derive [DecidableEq σ] [Hashable σ] [DecidableEq α] [Hashable α] [DecidableEq φ] [Hashable φ] (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): StateMemoize σ { dr: (Regex (φ × Ref n)) // dr = Grammar.Room.derive G Φ r node } :=
  let nodePred: (param: φ × Ref n) → StateMemoize σ {b: Bool // b = (fun ((labelPred, ref): (φ × Ref n)) =>
      let ⟨label, children⟩ := node
      let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
      Regex.null (List.foldl (Grammar.Room.derive G Φ) childr children)
    ) param } := (fun ((labelPred, ref): (φ × Ref n)) => do
    let ⟨label, children⟩ := node
    let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
    match List_foldlMemoize (Grammar.Memoize.derive G Φ) childr children with
    | res =>
      res >>= fun res' => pure (Subtype.mk (Regex.null res') (by
        simp





        subst childr






        change Regex.null (List.foldl (Grammar.Room.derive G Φ) childr children)

        sorry
      ))
  )
  Regex.Room.deriveM nodePred r

--  let symbols := enter r
--   let bools <- Vector.mapM Φ symbols
--   pure (leave r bools)

def StateMemoize.Grammar.derive.run {φ: Type} [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState φ) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  StateMemoize.run state (Grammar.Memoize.derive G Φ r node)

lemma StateMemoize.Grammar.derive.run_unfold {φ: Type} [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState φ) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α):
  (StateMemoize.Grammar.derive.run state G Φ r node) = StateMemoize.run state (Grammar.Memoize.derive G Φ r node) :=
  rfl

theorem StateMemoize.Grammar.derive.run_is_correct [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState φ)
  (Φ: φ → α → Bool) (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  StateMemoize.Grammar.derive.run state G Φ r node = Grammar.Room.derive G Φ r node := by
  rw [StateMemoize.Grammar.derive.run_unfold]
  generalize StateMemoize.run state (Grammar.Memoize.derive G Φ r node) = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

theorem StateMemoize.Grammar.derive_commutes [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState φ)
  (Φ: φ → α → Prop) [DecidableRel Φ]
  (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  Grammar.Rule.denote G Φ (StateMemoize.Grammar.derive.run state G (decideRel Φ) r node)
  = Lang.derive (Grammar.Rule.denote G Φ r) node := by
  rw [StateMemoize.Grammar.derive.run_is_correct]
  rw [<- Grammar.Room.derive_commutes]
