import Mathlib.Tactic.SimpRw

import Validator.Std.Decidable
import Validator.Std.Hedge
import Validator.Std.Vec

import Validator.Regex.Lang
import Validator.Regex.Room
import Validator.Regex.Enter
import Validator.Regex.Memoize.Memoize
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Hedge.Room
import Validator.Hedge.Lang
import Validator.Hedge.Denote

import Validator.Regex.Memoize
open Regex.Memoize


namespace Hedge

theorem take_succ_toList (xs: Vector α (n + 1)) (h: k <= n):
  (List.take (k + 1) xs.toList) = (List.take k (xs.toList)) ++ [xs.get ⟨k, by omega⟩] := by
  obtain ⟨⟨xs⟩, hxs⟩ := xs
  simp
  generalize_proofs hget
  have hk : k < xs.length := by
    simp at hxs
    omega
  have h: (Vector.mk (Array.mk xs) hxs).get ⟨k, hget⟩ = List.get xs ⟨k, hk⟩ := rfl
  rw [h]
  -- aesop?
  simp_all only [List.get_eq_getElem, List.take_append_getElem]

def Vec.mapM' [Monad m] (g: α -> β) (f: (a: α) -> m {res // res = g a}) (xs : Vector α n)
  : m {ys: (Vector β n) // ys = Vector.map g xs } := do
  go 0 (Nat.zero_le n) ⟨#v[], by simp⟩
where
  go (k : Nat) (h : k ≤ n) (acc : {ys: (Vector β k) // ys = Vector.cast (by omega) (Vector.map g (Vector.take xs k)) })
    : m {ys: (Vector β n) // ys = Vector.map g xs } := do
      if h' : k < n then
        f xs[k] >>=
          fun xsk =>
            go (k+1) (by omega) (⟨acc.val.push xsk, by
              obtain ⟨acc, hacc⟩ := acc
              simp only
              rw [hacc]
              obtain ⟨xsk, hxsk⟩ := xsk
              simp only
              rw [hxsk]
              apply Vector.eq
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [Vector.toList_take]
              rw [Vector.toList_push]
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [Vector.toList_take]
              rw [<- hxsk]
              -- generalize (xs.toList) = xs'
              cases n with
              | zero =>
                contradiction
              | succ n' =>
                rw [take_succ_toList (h := by omega)]
                rw [List.map_append]
                congr
          ⟩)
      else
        return ⟨Vector.cast (by omega) acc.val, by
          generalize_proofs h1 h2
          obtain ⟨acc, hacc⟩ := acc
          simp only
          rw [hacc]
          aesop
        ⟩

def Regex.StateMemoize.deriveM [DecidableEq σ] [Hashable σ]
  (Φ': σ -> Bool) (Φ: (s: σ) → StateMemoize σ { b // b = Φ' s }) (r: Regex σ):
  StateMemoize σ {dr: Regex σ // dr = Regex.Room.derive Φ' r } := do
  let ⟨symbols, hsymbols⟩ <- MemoizeRoom.enterM r
  let bools <- Vec.mapM' Φ' Φ symbols
  let ⟨res, hres⟩ <- MemoizeRoom.leaveM ⟨r, bools⟩
  let h: res = Regex.Room.derive Φ' r := by
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
    Regex.null (List.foldl (Grammar.Room.derive G Φ) childr children)

def List.foldlM'' [Monad m] (g: β -> α -> β) (xs: List α)
  (f: (acc: β) -> (a: {a': α // a' ∈ xs}) -> m {res: β // res = g acc a } )
  (init: β)
  : m {res': β // res' = List.foldl g init xs } :=
  match xs with
  | [] => pure ⟨init, rfl⟩
  | (x::xs') => do
    let fx <- f init (Subtype.mk x (by simp))
    let fxs <- List.foldlM'' g xs' (fun acc a => do
      let ⟨b, hb⟩ := a
      let a'': { a' // a' ∈ x :: xs' } := Subtype.mk b (by
        aesop
      )
      let f': { res // res = g acc a''.val } <- f acc a''
      let f'': { res // res = g acc b } := by
        subst a''
        simp only at f'
        assumption
      pure f''
    ) fx.val
    pure (Subtype.mk fxs.val (by
      obtain ⟨fxs, hfxs⟩ := fxs
      simp only
      obtain ⟨fx, hfx⟩ := fx
      simp only at hfxs
      rw [hfxs]
      rw [hfx]
      simp only
      simp only [List.foldl]
    ))

def Grammar.Room.derive'' (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  let nodePred: (param: φ × Ref n) → Bool := (fun ((labelPred, ref): (φ × Ref n)) =>
    let ⟨label, children⟩ := node
    let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (Grammar.Room.derive'' G Φ) childr children)
  )
  Regex.Room.derive nodePred r

def Grammar.StateMemoize.derive' [DecidableEq α] [Hashable α] [DecidableEq φ] [Hashable φ]
  (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (children: Hedge α) (node: { node': Node α // node' ∈ children}): StateMemoize (φ × Ref n) { dr: (Regex (φ × Ref n)) // dr = Grammar.Room.derive G Φ r node } := do
  let nodePred: (param: φ × Ref n) → StateMemoize (φ × Ref n) {b: Bool // b = pureNodePred G Φ node.val param } :=
    (fun ((labelPred, ref): (φ × Ref n)) =>
      match hnode: node with
      | Subtype.mk (Hedge.Node.mk label children) hhnode =>
      let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
      List.foldlM'' (Grammar.Room.derive G Φ) children (Grammar.StateMemoize.derive' G Φ (children := children)) childr >>=
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
  let dr <- Regex.StateMemoize.deriveM (pureNodePred G Φ node) nodePred r
  pure (Subtype.mk dr.val (by
    obtain ⟨dr, hdr⟩ := dr
    simp only
    rw [hdr]
    unfold Grammar.Room.derive
    rfl
  ))
  termination_by node.val
  decreasing_by
    · obtain ⟨node, hnode⟩ := node
      simp only
      apply Node.sizeOf_children hnode

def Grammar.StateMemoize.derive [DecidableEq α] [Hashable α] [DecidableEq φ] [Hashable φ]
  (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): StateMemoize (φ × Ref n) { dr: (Regex (φ × Ref n)) // dr = Grammar.Room.derive G Φ r node } :=
  Grammar.StateMemoize.derive' G Φ r [node] (Subtype.mk node (by simp))

def StateMemoize.Grammar.derive.run {φ: Type} [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  StateMemoize.run state (Grammar.StateMemoize.derive G Φ r node)

lemma StateMemoize.Grammar.derive.run_unfold {φ: Type} [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState (φ × Ref n)) (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (node: Node α):
  (StateMemoize.Grammar.derive.run state G Φ r node) = StateMemoize.run state (Grammar.StateMemoize.derive G Φ r node) :=
  rfl

theorem StateMemoize.Grammar.derive.run_is_correct [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState (φ × Ref n))
  (Φ: φ → α → Bool) (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  StateMemoize.Grammar.derive.run state G Φ r node = Grammar.Room.derive G Φ r node := by
  rw [StateMemoize.Grammar.derive.run_unfold]
  generalize StateMemoize.run state (Grammar.StateMemoize.derive G Φ r node) = x
  obtain ⟨dr, hdr⟩ := x
  simp only
  rw [hdr]

theorem StateMemoize.Grammar.derive_commutes [DecidableEq φ] [Hashable φ] [DecidableEq α] [Hashable α]
  (state: memoizeState (φ × Ref n))
  (Φ: φ → α → Prop) [DecidableRel Φ]
  (G: Grammar n φ) (r: Regex (φ × Ref n)) (node: Node α):
  Grammar.Rule.denote G Φ (StateMemoize.Grammar.derive.run state G (decideRel Φ) r node)
  = Lang.derive (Grammar.Rule.denote G Φ r) node := by
  rw [StateMemoize.Grammar.derive.run_is_correct]
  rw [<- Grammar.Room.derive_commutes]
