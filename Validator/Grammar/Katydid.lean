import Mathlib.Tactic.SimpRw

import Validator.Std.Decidable
import Validator.Std.Hedge

import Validator.Regex.Lang
import Validator.Regex.Katydid

import Validator.Grammar.Denote
import Validator.Grammar.Grammar
import Validator.Grammar.Lang

import Validator.Pred.AnyEq
import Validator.Pred.Compare

open Hedge

def Grammar.Katydid.derive (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) :=
  let nodePred: (param: φ × Ref n) → Bool := (fun ((labelPred, ref): (φ × Ref n)) =>
    let ⟨label, children⟩ := node
    let childr := if Φ labelPred label then G.lookup ref else Regex.emptyset
    Regex.null (List.foldl (Grammar.Katydid.derive G Φ) childr children)
  )
  Regex.Katydid.derive nodePred r

namespace Grammar.Katydid

def validate (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α): Bool :=
  Regex.null (List.foldl (derive G Φ) G.start nodes)
def filter (G: Grammar n φ) (Φ: φ → α → Bool)
  (hedges: List (Hedge α)): List (Hedge α) := List.filter (validate G Φ) hedges
end Grammar.Katydid

lemma Grammar.Katydid.unapply_hedge_param_and_flip
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

lemma Grammar.Katydid.derive_emptyset {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (a: Node α):
  Grammar.Katydid.derive G Φ Regex.emptyset a = Regex.emptyset := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_emptystr (G: Grammar n φ) Φ (x: Node α):
  Grammar.Katydid.derive G Φ Regex.emptystr x = Regex.emptyset := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_symbol (G: Grammar n φ) Φ (x: Node α):
  Grammar.Katydid.derive G Φ (Regex.symbol (pred, ref)) x
    = Regex.onlyif ((let ⟨label, children⟩ := x
        (List.foldl (Grammar.Katydid.derive  G Φ)
          (if Φ pred label then G.lookup ref else Regex.emptyset)
          children
        ).null) = true) Regex.emptystr := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_or (G: Grammar n φ) Φ r1 r2 (node: Node α):
  Grammar.Katydid.derive G Φ (Regex.or r1 r2) node = Regex.or
    (Grammar.Katydid.derive G Φ r1 node) (Grammar.Katydid.derive G Φ r2 node) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_concat (G: Grammar n φ) Φ r1 r2 (x: Node α):
  Grammar.Katydid.derive G Φ (Regex.concat r1 r2) x
    = Regex.or
      (Regex.concat (Grammar.Katydid.derive G Φ r1 x) r2)
      (Regex.onlyif (Regex.null r1) (Grammar.Katydid.derive G Φ r2 x)) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_star {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.star r1) a
  = Regex.concat (Grammar.Katydid.derive G Φ r1 a) (Regex.star r1) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_interleave {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.interleave r1 r2) a
  = Regex.or
    (Regex.interleave (Grammar.Katydid.derive G Φ r1 a) r2)
    (Regex.interleave (Grammar.Katydid.derive G Φ r2 a) r1) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_and {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1 r2: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.and r1 r2) a
  = Regex.and (Grammar.Katydid.derive G Φ r1 a) (Grammar.Katydid.derive G Φ r2 a) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.derive_compliment {α: Type} (G: Grammar n φ) (Φ: φ → α → Bool) (r1: Regex (φ × Ref n)) (a: Node α):
  Grammar.Katydid.derive G Φ (Regex.compliment r1) a
  = Regex.compliment (Grammar.Katydid.derive G Φ r1 a) := by
  unfold Grammar.Katydid.derive
  rw [unapply_hedge_param_and_flip]
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  simp only [Regex.derive]

lemma Grammar.Katydid.and_start {α: Type} (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (label: α) (children: Hedge α):
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

lemma Grammar.Katydid.derive_denote_symbol_is_onlyif {α: Type} (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (label: α) (children: Hedge α):
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

theorem Grammar.Katydid.derive_commutes (G: Grammar n φ) Φ [DecidableRel Φ]
  (r: Regex (φ × Ref n)) (node: Node α):
  Rule.denote G Φ (Grammar.Katydid.derive G (decideRel Φ) r node)
  = Lang.derive (Rule.denote G Φ r) node := by
  induction r with
  | emptyset =>
    rw [Grammar.Katydid.derive_emptyset]
    rw [Grammar.denote_emptyset]
    rw [Lang.derive_emptyset]
  | emptystr =>
    rw [Grammar.Katydid.derive_emptystr]
    rw [Grammar.denote_emptystr]
    rw [Grammar.denote_emptyset]
    rw [Lang.derive_emptystr]
  | symbol s =>
    obtain ⟨pred, ref⟩ := s
    obtain ⟨label, children⟩ := node

    rw [Grammar.Katydid.derive_symbol]

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
    rw [Grammar.Katydid.derive_or]
    rw [Grammar.denote_or]
    rw [Grammar.denote_or]
    rw [Lang.derive_or]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_concat]
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
    rw [Grammar.Katydid.derive_star]
    rw [Grammar.denote_star]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_star]
    rw [Lang.derive_star]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_interleave]
    rw [Grammar.denote_or]
    rw [Grammar.denote_interleave]
    rw [Grammar.denote_interleave]
    rw [ih1]
    rw [ih2]
    rw [Grammar.denote_interleave]
    rw [Lang.derive_interleave]
  | and r1 r2 ih1 ih2 =>
    rw [Grammar.Katydid.derive_and]
    rw [Grammar.denote_and]
    rw [Grammar.denote_and]
    rw [Lang.derive_and]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    rw [Grammar.Katydid.derive_compliment]
    rw [Grammar.denote_compliment]
    rw [ih1]
    rw [Grammar.denote_compliment]
    rw [Lang.derive_compliment]
    unfold Lang.compliment
    rfl
  termination_by node
  decreasing_by
    apply Node.sizeOf_children hx

theorem Grammar.Katydid.derive_commutesb (G: Grammar n φ) (Φ: φ → α → Bool) (r: Regex (φ × Ref n)) (x: Node α):
  Rule.denote G (fun s a => Φ s a) (Grammar.Katydid.derive G Φ r x)
  = Lang.derive (Rule.denote G (fun s a => Φ s a) r) x := by
  have h1: (fun s a => Φ s a) = decideRel (fun s a => Φ s a) := by
    unfold decideRel
    aesop
  have h2: (fun s a => Φ s a) = Φ := by
    rfl
  nth_rewrite 2 [<- h2]
  rw [h1]
  rw [derive_commutes]

theorem Grammar.Katydid.derives_commutes (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (r: Regex (φ × Ref n)) (nodes: Hedge α):
  Grammar.Rule.denote G Φ (List.foldl (Grammar.Katydid.derive G (decideRel Φ)) r nodes) = Lang.derives (Grammar.Rule.denote G Φ r) nodes := by
  rw [Lang.derives_foldl]
  induction nodes generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes G Φ r x
    have ih' := ih (Grammar.Katydid.derive G (decideRel Φ) r x)
    rw [h] at ih'
    exact ih'

theorem Grammar.Katydid.validate_commutes (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (nodes: Hedge α):
  (Grammar.Katydid.validate G (decideRel Φ) nodes = true)
  = Grammar.denote G Φ nodes := by
  unfold Grammar.denote
  rw [<- Lang.validate (Grammar.Rule.denote G Φ G.start) nodes]
  unfold validate
  rw [<- derives_commutes]
  rw [<- Grammar.null_commutes]

namespace Grammar.Katydid.Paper

theorem derive_commutes (G: Grammar n φ) Φ [DecidableRel Φ]
  (r: Regex (φ × Ref n)) (node: Node α):
  Rule.denote G Φ (derive G (decideRel Φ) r node)
  = Lang.derive (Rule.denote G Φ r) node := by
  apply Grammar.Katydid.derive_commutes

theorem validate_commutes (G: Grammar n φ) Φ [DecidableRel Φ] (nodes: Hedge α):
  (validate G (decideRel Φ) nodes = true) = Grammar.denote G Φ nodes := by
  apply Grammar.Katydid.validate_commutes

def filter  (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: List (Hedge α)): List (Hedge α) :=
  List.filter (validate G Φ) nodes

end Grammar.Katydid.Paper

theorem mem_filter (Φ: φ → α → Prop) [DecidableRel Φ] (G: Grammar n φ) (xss: List (Hedge α)) :
  ∀ xs, (xs ∈ Grammar.Katydid.filter G (decideRel Φ) xss) ↔ (Lang.MemFilter (Grammar.denote G Φ) xss xs) := by
  unfold Grammar.Katydid.filter
  intro xs
  rw [List.mem_filter]
  unfold Lang.MemFilter
  apply Iff.intro
  case mp =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [<- Grammar.Katydid.validate_commutes]
    assumption
  case mpr =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [Grammar.Katydid.validate_commutes]
    assumption

-- Tests

namespace Grammar.Katydid

open Pred

def run [DecidableEq α] (G: Grammar n (AnyEq.Pred α)) (nodes: Hedge α): Bool :=
  validate G AnyEq.Pred.evalb nodes

abbrev contains (r: Regex σ) := Regex.contains r
abbrev symbol (s: σ) := Regex.symbol s
abbrev emptystr : Regex σ := Regex.emptystr
abbrev interleave (r1 r2: Regex σ) := Regex.interleave r1 r2
abbrev or (r1 r2: Regex σ) := Regex.or r1 r2
abbrev and (r1 r2: Regex σ) := Regex.and r1 r2
abbrev optional (r: Regex σ) := Regex.optional r
abbrev starAny: Regex σ := Regex.starAny

#guard run
  (Grammar.singleton Regex.emptyset)
  [node "a" [node "b" [], node "c" [node "d" []]]] =
  false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[Regex.emptystr]
  )
  [node "a" []] =
  true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[Regex.emptystr]
  )
  [node "a" [node "b" []]] =
  false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.symbol (AnyEq.Pred.eq "b", 1))
      , Regex.emptystr
    ]
  )
  [node "a" [node "b" []]]
  = true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq "b", 1))
        (Regex.symbol (AnyEq.Pred.eq "c", 1))
      )
      , Regex.emptystr
    ]
  )
  [node "a" [node "b" [], node "c" []]] =
  true

#guard run
  (Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq "b", 1))
        (Regex.symbol (AnyEq.Pred.eq "c", 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq ("d"), 1))
    ]
  )
  [node "a" [node "b" [], node "c" [node "d" []]]] =
  true

-- modified example from https://books.xmlschemata.org/relaxng/relax-CHP-5-SECT-4.html

private def example_grammar_library: Grammar 5 (Option String) :=
  Grammar.mk
    (start := Regex.symbol (some "library", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol (some "book", 1)),
      Regex.concat
        (Regex.symbol (some "isbn", 3))
        (Regex.concat
          (Regex.symbol (some "title", 3))
          (Regex.oneOrMore (Regex.symbol (some "author", 2)))
        ),
      Regex.concat
        (Regex.symbol (some "name", 3))
        (Regex.optional (Regex.symbol (some "born", 3))),
      Regex.symbol (Option.none, 4),
      Regex.emptystr
    ])

#guard validate
  example_grammar_library
  (fun s a =>
    match s with
    | Option.none => true
    | Option.some s' => s' == a
  )
  [node "library"
    [node "book" [
      (node "isbn" [node "123" []]),
      (node "title" [node "numbers" []]),
      (node "author" [node "name" [node "Brink" []]]),
      (node "author" [node "name" [node "Paul" []], node "born" [node "July" []]])
    ]]
  ]
  = true

-- no authors fails
#guard validate
  example_grammar_library
  (fun s a =>
    match s with
    | Option.none => true
    | Option.some s' => s' == a
  )
  [node "library"
    [node "book" [
      (node "isbn" [node "456" []]),
      (node "title" [node "numbers" []])
    ]]
  ]
  = false

-- modified example from Taxonomy of XML Section 6.5

private def example_grammar_doc: Grammar 3 String :=
  Grammar.mk (start := Regex.symbol ("doc", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol ("para", 1)),
      Regex.symbol ("pcdata", 2),
      Regex.emptystr,
    ])

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" []]]
  = false

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
  = true

-- modified example from Taxonomy of XML Section 7.1
private def example_grammar_sec: Grammar 2 String :=
  Grammar.mk
    (start := Regex.oneOrMore (Regex.symbol ("sec", 0)))
    (prods := #v[
      Regex.oneOrMore (Regex.or
        (Regex.symbol ("sec", 0))
        (Regex.symbol ("p", 1))
      ),
      Regex.emptystr
    ])

#guard validate example_grammar_sec (· == ·)
  [node "sec" [node "p" []]]
  = true

#guard validate example_grammar_sec (· == ·)
  [node "sec" [node "p" []], node "sec" [node "sec" [node "p" []], node "sec" [node "p" []], node "sec" [node "p" []]]]
  = true

#guard validate example_grammar_sec (· == ·)
  [node "sec" []]
  = false

#guard validate example_grammar_sec (· == ·)
  [node "p" []]
  = false

private def example_benchmark_nested_contains: Grammar 3 String :=
  mk (contains (symbol ("A",0))) #v[contains (symbol ("B",1)), symbol ("C",2), emptystr]

#guard validate example_benchmark_nested_contains (· == ·)
  [node "A" [node "B" [node "C" []]]]

#guard validate example_benchmark_nested_contains (· == ·)
  [node "a" [], node "A" [node "B" [node "D" []], node "B" [node "C" []], node "B" [node "D" []]], node "a" []]

#guard validate example_benchmark_nested_contains (· == ·)
  [node "a" [node "B" [node "C" []]], node "A" [node "D" [node "C" []], node "B" [node "D" []], node "D" [node "D" []]], node "a" []]
  = false

private def example_interleave: Grammar 5 String :=
  mk (interleave (symbol ("A",0)) (interleave (symbol ("B",1)) (optional (symbol ("C",2))))) #v[
    interleave (symbol ("A1", 3)) (symbol ("A2",3)),
    interleave (symbol ("Bb", 3)) starAny,
    contains (symbol ("Cc", 3)),
    symbol ("t", 4), emptystr]

#guard validate example_interleave (· == ·)
  [node "A" [node "A1" [node "t" []], node "A2" [node "t" []]], node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]]]

#guard validate example_interleave (· == ·)
  [node "D" [], node "A" [node "A1" [node "t" []], node "A2" [node "t" []]], node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]]]
  = false

#guard validate example_interleave (· == ·)
  [node "B" [node "B1" [node "t" []], node "B2" [node "t" []], node "Bb" [node "t" []]], node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]]
  = true

#guard validate example_interleave (· == ·)
  [
    node "B" [node "B1" [node "t" []], node "Bb" [node "t" []]],
    node "C" [node "C1" [node "t" []], node "Cc" [node "t" []], node "C2" [node "t" []]],
    node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]
  ]
  = true

#guard validate example_interleave (· == ·)
  [
    node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]],
    node "A" [node "C1" [node "t" []], node "Cc" [node "t" []], node "C2" [node "t" []]],
    node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]
  ]
  = false

#guard validate example_interleave (· == ·)
  [
    node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]],
    node "C" [node "C1" [node "t" []], node "Cc" [node "g" []], node "C2" [node "t" []]],
    node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]
  ]
  = false

-- Benchmark tests

open Pred.Compare

def eq (v: α × Fin n) := symbol (Pred.eq v.1, v.2)
def field (v: α × Fin n) := contains (symbol (Pred.eq v.1, v.2))

def simple: Grammar 2 (Pred String) :=
  mk (field ("Category", 1)) #v[emptystr, eq ("Computer Science", 0)]

#guard validate simple Pred.evalb
  [node "Category" [node "Computer Science" []]]

#guard validate simple Pred.evalb
  [node "Name" [node "ITP" []], node "Category" [node "Computer Science" []]]

#guard validate simple Pred.evalb
  [node "Name" [node "ICFP" []], node "Category" [node "Functional Programming" []]]
  = false

def complex : Grammar 7 (Pred String) :=
  mk (interleave (eq ("Due", 1)) (interleave (eq ("Loc", 5)) starAny)) #v[emptystr,
    or (field ("Year", 2)) (and (field ("Year", 3)) (field ("Month", 4))),
    eq ("2026", 0), eq ("2025", 0), symbol (Pred.ge "10", 0),
    field ("Cont", 6), eq ("EU", 0),
  ]

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
      node "City" [node "Lisbon" []]
    ],
    node "Due" [
      node "Year" [node "2026" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
      node "City" [node "Amsterdam" []]
    ],
    node "Due" [
      node "Year" [node "2025" []],
      node "Month" [node "11" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
    ],
    node "Due" [
      node "Y" [node "2027" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]
  = false

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "AN" []],
    ],
    node "Due" [
      node "Y" [node "2026" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]
  = false
