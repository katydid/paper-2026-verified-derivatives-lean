import Mathlib.Tactic.SimpRw

import Validator.Std.Decidable
import Validator.Std.Hedge

import Validator.Regex.Lang
import Validator.Regex.Room
import Validator.Hedge.Denote
import Validator.Hedge.Grammar
import Validator.Hedge.Lang

namespace Hedge

def Grammar.Room.derive (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  let nodePred := (fun ((labelPred, ref): (φ × Ref n)) =>
    let ⟨label, children⟩ := node
    let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (Grammar.Room.derive G Φ) childr children)
  )
  Regex.Room.derive nodePred r

def Grammar.Room.validate
  (G: Hedge.Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (hedge: Hedge α): Bool :=
  Regex.null (List.foldl (Grammar.Room.derive G Φ) r hedge)

lemma Grammar.Room.unapply_hedge_param_and_flip
  (G: Grammar n φ) (Φ: φ → α → Bool) (node: Node α):
  (fun ((pred, ref): (φ × Ref n)) =>
    let ⟨label, children⟩ := node
    let childr: Regex (φ × Ref n) := if Φ pred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (derive G Φ) childr children)
  )
  =
  (flip fun ((pred, ref): (φ × Ref n)) (node': Node α) =>
    let ⟨label, children⟩ := node'
    let childr: Regex (φ × Ref n) := if Φ pred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (derive G Φ) childr children)
  ) node := by
  rfl

lemma Grammar.Room.derive_emptyset {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (a: Node α):
  Grammar.Room.derive G Φ Regex.emptyset a = Regex.emptyset := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_emptystr (G: Grammar n φ) Φ (x: Node α):
  Grammar.Room.derive G Φ Regex.emptystr x = Regex.emptyset := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_symbol (G: Grammar n φ) Φ (x: Node α):
  Grammar.Room.derive G Φ (Regex.symbol (pred, ref)) x
    = Regex.onlyif ((let ⟨label, children⟩ := x
        (List.foldl (Grammar.Room.derive  G Φ)
          (if Φ pred label then G.lookup ref else Regex.emptyset)
          children
        ).null) = true) Regex.emptystr := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_or {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Room.derive G Φ (Regex.or r1 r2) a
  = Regex.or (Grammar.Room.derive G Φ r1 a) (Grammar.Room.derive G Φ r2 a) := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_concat (G: Grammar n φ) Φ r1 r2 (x: Node α):
  Grammar.Room.derive G Φ (Regex.concat r1 r2) x
    = Regex.or
      (Regex.concat (Grammar.Room.derive G Φ r1 x) r2)
      (Regex.onlyif (Regex.null r1) (Grammar.Room.derive G Φ r2 x)) := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_star {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1: Regex (φ × Ref n)) (a: Node α):
  Grammar.Room.derive G Φ (Regex.star r1) a
  = Regex.concat (Grammar.Room.derive G Φ r1 a) (Regex.star r1) := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_interleave {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Room.derive G Φ (Regex.interleave r1 r2) a
  = Regex.or
    (Regex.interleave (Grammar.Room.derive G Φ r1 a) r2)
    (Regex.interleave (Grammar.Room.derive G Φ r2 a) r1) := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_and {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Room.derive G Φ (Regex.and r1 r2) a
  = Regex.and (Grammar.Room.derive G Φ r1 a) (Grammar.Room.derive G Φ r2 a) := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.derive_compliment {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1: Regex (φ × Ref n)) (a: Node α):
  Grammar.Room.derive G Φ (Regex.compliment r1) a
  = Regex.compliment (Grammar.Room.derive G Φ r1 a) := by
  unfold Grammar.Room.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Room.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Room.and_start {α: Type} (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (label: α) (children: Hedge α):
  ((List.foldl (derive G (decideRel Φ)) (if decideRel Φ p label then G.lookup ref else Regex.emptyset) children).null = true)
  = (Φ p label /\ ((List.foldl (derive G (decideRel Φ)) (G.lookup ref) children).null = true)) := by
  generalize (G.lookup ref) = r
  split_ifs
  case pos h =>
    simp_all [decideRel]
  case neg h =>
    simp_all only [decideRel, decide_eq_true_eq, eq_iff_iff, false_and, iff_false,
      Bool.not_eq_true]
    induction children with
    | nil =>
      simp only [Regex.null, List.foldl_nil, Regex.null]
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [derive_emptyset]
      rw [ih]

lemma Grammar.Room.derive_denote_symbol_is_onlyif {α: Type} (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (label: α) (children: Hedge α):
  Lang.derive
    (Rule.denote G Φ
      (Regex.symbol (pred, ref))
    )
    (Node.mk label children)
  =
    Lang.onlyif
      (Φ pred label ∧ Rule.denote G Φ (G.lookup ref) children)
      Lang.emptystr
  := by
  funext xs
  rw [Grammar.denote_symbol]
  rw [Lang.derive_iff_tree]
  simp only [decide_eq_true_eq]

theorem Grammar.Room.derive_commutes (G: Grammar n φ) (Φ: φ → α → Prop)
  [DecidableRel Φ] (r: Regex (φ × Ref n)) (node: Node α):
  Rule.denote G Φ (Grammar.Room.derive G (decideRel Φ) r node)
  = Lang.derive (Rule.denote G Φ r) node := by
  induction r with
  | emptyset =>
    rw [Grammar.Room.derive_emptyset]
    rw [Grammar.denote_emptyset]
    rw [Lang.derive_emptyset]
  | emptystr =>
    rw [Grammar.Room.derive_emptystr]
    rw [Grammar.denote_emptystr]
    rw [Grammar.denote_emptyset]
    rw [Lang.derive_emptystr]
  | symbol s =>
    obtain ⟨pred, ref⟩ := s
    obtain ⟨label, children⟩ := node

    rw [Grammar.Room.derive_symbol]

    rw [derive_denote_symbol_is_onlyif]
    rw [Grammar.denote_onlyif]
    rw [Grammar.denote_emptystr]
    congr

    simp only [and_start]
    congr

    generalize G.lookup ref = r
    have ihr := fun r' x (hx: x ∈ children) =>
      derive_commutes G Φ r' x
    induction children generalizing r with
    | nil =>
      simp only [List.foldl_nil]
      rw [Grammar.denote_nil_is_null]
    | cons x2 xs ihxs =>
      simp only [List.foldl]
      rw [ihxs]
      · rw [ihr]
        · rfl
        · simp only [List.mem_cons, true_or]
      · intro x r' hxs
        rw [ihr]
        simp only [List.mem_cons]
        apply Or.inr hxs
  | or r1 r2 ih1 ih2 =>
    rw [Grammar.Room.derive_or]
    rw [Grammar.denote_or]
    rw [Grammar.denote_or]
    rw [Lang.derive_or]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    rw [Grammar.Room.derive_concat]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_or]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_onlyif]
    rw [Lang.derive_concat]
    rw [<- ih1]
    rw [<- ih2]
    congr
    apply Grammar.null_commutes
  | star r1 ih1 =>
    rw [Grammar.Room.derive_star]
    rw [Grammar.denote_star]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_star]
    rw [Lang.derive_star]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    rw [Grammar.Room.derive_interleave]
    rw [Grammar.denote_or]
    rw [Grammar.denote_interleave]
    rw [Grammar.denote_interleave]
    rw [ih1]
    rw [ih2]
    rw [Grammar.denote_interleave]
    rw [Lang.derive_interleave]
  | and r1 r2 ih1 ih2 =>
    rw [Grammar.Room.derive_and]
    rw [Grammar.denote_and]
    rw [Grammar.denote_and]
    rw [Lang.derive_and]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    rw [Grammar.Room.derive_compliment]
    rw [Hedge.Grammar.denote_compliment]
    rw [ih1]
    rw [Hedge.Grammar.denote_compliment]
    rw [Lang.derive_compliment]
    unfold Lang.compliment
    rfl
  termination_by node
  decreasing_by
    apply Node.sizeOf_children hx

theorem Grammar.Room.derive_commutesb (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (x: Node α):
  Rule.denote G (fun s a => Φ s a) (Grammar.Room.derive G Φ r x)
  = Lang.derive (Rule.denote G (fun s a => Φ s a) r) x := by
  have h1: (fun s a => Φ s a) = decideRel (fun s a => Φ s a) := by
    unfold decideRel
    aesop
  have h2: (fun s a => Φ s a) = Φ := by
    rfl
  nth_rewrite 2 [<- h2]
  rw [h1]
  rw [derive_commutes]

theorem Grammar.Room.derives_commutes (G: Hedge.Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (r: Regex (φ × Ref n)) (nodes: Hedge α):
  Hedge.Grammar.Rule.denote G Φ (List.foldl (Grammar.Room.derive G (decideRel Φ)) r nodes) = Lang.derives (Hedge.Grammar.Rule.denote G Φ r) nodes := by
  rw [Lang.derives_foldl]
  induction nodes generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes G Φ r x
    have ih' := ih (Grammar.Room.derive G (decideRel Φ) r x)
    rw [h] at ih'
    exact ih'

theorem Grammar.Room.validate_commutes (G: Hedge.Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (r: Regex (φ × Ref n)) (nodes: Hedge α):
  (validate G (decideRel Φ) r nodes = true) = (Hedge.Grammar.Rule.denote G Φ r) nodes := by
  rw [<- Lang.validate (Hedge.Grammar.Rule.denote G Φ r) nodes]
  unfold validate
  rw [<- derives_commutes]
  rw [<- Hedge.Grammar.null_commutes]
