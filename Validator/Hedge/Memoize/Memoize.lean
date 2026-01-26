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

import Validator.Regex.Memoize
open Regex.Memoize

namespace Hedge

def Regex.Memoize.deriveM [DecidableEq σ] [Hashable σ] [Monad m] [MemoizeKatydid m σ]
  (Φ': σ -> Bool) (Φ: (s: σ) → m { b // b = Φ' s }) (r: Regex σ):
  m {dr: Regex σ // dr = Regex.Katydid.derive Φ' r } := do
  let ⟨symbols, hsymbols⟩ <- MemoizeKatydid.enterM r
  let bools <- Vector.mapMemoize Φ' Φ symbols
  let ⟨res, hres⟩ <- MemoizeKatydid.leaveM ⟨r, bools⟩
  let h: res = Regex.Katydid.derive Φ' r := by
    unfold leave at hres
    simp only at hres
    subst_eqs
    rename_i hleave
    obtain ⟨bools, hbools⟩ := bools
    obtain ⟨leave, hleave⟩ := hleave
    simp only
    rw [hbools]
    rfl
  pure (Subtype.mk res h)

def pureNodePred (G: Grammar n φ) (Φ: φ → α → Bool) (node: Node α) (symbol: (φ × Ref n)) :=
    let ⟨label, children⟩ := node
    let childr := if Φ symbol.1 label then G.lookup symbol.2 else Regex.emptyset
    Regex.null (List.foldl (Grammar.Katydid.derive G Φ) childr children)

def Grammar.Memoize.derive' [DecidableEq φ] [Hashable φ] [Monad m] [MemoizeKatydid m (φ × Ref n)]
  (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (children: Hedge α) (node: { node': Node α // node' ∈ children})
  : m { dr: (Regex (φ × Ref n)) // dr = Grammar.Katydid.derive G Φ r node } := do
  let nodePred: (param: φ × Ref n) → m {b: Bool // b = pureNodePred G Φ node.val param } :=
    (fun ((labelPred, ref): (φ × Ref n)) =>
      match hnode: node with
      | Subtype.mk (Hedge.Node.mk label children) hhnode =>
      let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
      List.foldlMemoizeWithMembership (Grammar.Katydid.derive G Φ) children (Grammar.Memoize.derive' G Φ (children := children)) childr >>=
        fun dr =>
          let dn: Bool := Regex.null dr.val
          pure (Subtype.mk dn (by
            obtain ⟨dr, hdr⟩ := dr
            subst dn
            simp only
            rw [hdr]
            unfold pureNodePred
            simp only
            subst childr
            rfl
          ))
  )
  let dr <- Regex.Memoize.deriveM (pureNodePred G Φ node) nodePred r
  pure (Subtype.mk dr.val (by
    obtain ⟨dr, hdr⟩ := dr
    simp only
    rw [hdr]
    unfold Grammar.Katydid.derive
    rfl
  ))
  termination_by node.val
  decreasing_by
    · obtain ⟨node, hnode⟩ := node
      simp only
      apply Node.sizeOf_children hnode

def Grammar.Memoize.derive [DecidableEq φ] [Hashable φ] [Monad m] [MemoizeKatydid m (φ × Ref n)]
  (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): m { dr: (Regex (φ × Ref n)) // dr = Grammar.Katydid.derive G Φ r node } :=
  Grammar.Memoize.derive' G Φ r [node] (Subtype.mk node (by simp))

def Grammar.Memoize.validate [DecidableEq φ] [Hashable φ] [Monad m] [MemoizeKatydid m (φ × Ref n)]
  (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α)
  : m { valid: Bool // valid = Grammar.Katydid.validate G Φ nodes } := do
  let dr <- List.foldlMemoize (Grammar.Katydid.derive G Φ) (Grammar.Memoize.derive G Φ) G.start nodes
  pure (Subtype.mk (Regex.null dr.val) (by
    obtain ⟨dr, hdr⟩ := dr
    simp only
    rw [hdr]
    unfold Katydid.validate
    rfl
  ))

def Grammar.Memoize.filter [DecidableEq φ] [Hashable φ] [Monad m]
  [MemoizeKatydid m (φ × Ref n)] (G: Grammar n φ) (Φ: φ → α → Bool)
  (xs: List (Hedge α)) : m { xs' // xs' = Grammar.Katydid.filter G Φ xs } :=
  List.filterMemoize (Grammar.Katydid.validate G Φ) (Grammar.Memoize.validate G Φ) xs
