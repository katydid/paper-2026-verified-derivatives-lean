import Mathlib.Tactic.SimpRw

import Validator.Std.Decidable
import Validator.Std.Hedge

import Validator.Regex.Lang
import Validator.Regex.Room
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Hedge.Room
import Validator.Hedge.Lang

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
