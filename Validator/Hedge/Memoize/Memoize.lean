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

-- def List_foldlMemoize
--   {α: Type}
--   [DecidableEq α] [Hashable α]
--   {β: Type}
--   [DecidableEq β] [Hashable β]
--   (f: (b: β) -> (a: α) -> m β)
--   {σ: Type}
--   [Monad m]
--   (init: β) (xs: List α): m {b': m β // b' = List.foldlM f init xs} :=
--   match xs with
--   | [] => pure ⟨init, rfl⟩
--   | (x::xs) => do
--     let x': { b // b = f init x } := ⟨f init x, rfl⟩
--     let xs': { b' // b' = List.foldl f (↑x') xs } <- List_foldlMemoize (σ := σ) f x' xs
--     pure (Subtype.mk xs' (by
--       obtain ⟨x', hx'⟩ := x'
--       simp only at xs'
--       obtain ⟨xs', hxs'⟩ := xs'
--       simp only
--       rw [hx'] at hxs'
--       simp only [List.foldl]
--       exact hxs'
--     ))

def Vec.mapM [Monad m] (g: α -> β) (f: (a: α) -> m {res // res = g a})  (xs: Vector α n)
  : m (Vector β n) :=
  Vector.mapM (fun a => (·.1) <$> (f a)) xs

def List.mappyM [Monad m] {g: α -> β} (f: (a: α) -> m {res // res = g a}) (xs: List α)
  : m {ys: (List β) // ys = List.map g xs } :=
  match xs with
  | [] => pure ⟨[], rfl⟩
  | (x::xs') => do
    let ⟨fx, hfx⟩ <- f x
    let ⟨fxs, hfxs⟩ <- List.mappyM f xs'
    pure (Subtype.mk (fx::fxs) (by
      simp only [List.map]
      rw [hfx]
      rw [hfxs]
    ))

theorem eq (xs ys: Vector α n) (h: Vector.toList xs = Vector.toList ys): xs = ys := by
  obtain ⟨⟨xs⟩, hxs⟩ := xs
  obtain ⟨⟨ys⟩, hxs⟩ := ys
  simp_all

theorem take_toList (xs: Vector α l):
  (Vector.take xs n).toList = List.take n xs.toList := by
  sorry

theorem push_toList (xs: Vector α n) (x: α):
  (Vector.push xs x).toList = xs.toList ++ [x] := by
  sorry

theorem take1_toList (xs: Vector α (n + 1)) (h: k <= n):
  (List.take (k + 1) xs.toList) = (List.take k (xs.toList)) ++ [xs.get ⟨k, by omega⟩] := by
  sorry

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
              apply eq
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [take_toList]
              rw [push_toList]
              rw [Vector.cast_toList]
              rw [Vector.map_toList]
              rw [take_toList]
              rw [<- hxsk]
              -- generalize (xs.toList) = xs'
              cases n with
              | zero =>
                contradiction
              | succ n' =>
                rw [take1_toList (h := by omega)]
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

def List.foldlM' [Monad m] (g: β -> α -> β) (f: (acc: β) -> (a: α) -> m {res: β // res = g acc a } ) (init: β) (xs: List α)
  : m {res': β // res' = List.foldl g init xs } := by
  sorry

def List.foldlM'' [Monad m] (g: β -> α -> β) (xs: List α)
  (f: (acc: β) -> (a: {a': α // a' ∈ xs}) -> m {res: β // res = g acc a } )
  (init: β)
  : m {res': β // res' = List.foldl g init xs } := by
  sorry

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
