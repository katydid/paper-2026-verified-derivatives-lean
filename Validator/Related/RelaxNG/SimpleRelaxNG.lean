import Mathlib.Tactic.NthRewrite

import Validator.Std.Hedge

-- Copied from https://relaxng.org/jclark/derivative.html and added translations for Lean
import Validator.Related.RelaxNG.StdHaskell

namespace SimpleRelaxNG

inductive NameClass where
  | AnyName
  | AnyNameExcept (n: NameClass)
  | Name (n: String)
  | NameClassChoice (n1 n2: NameClass)
  deriving Repr, DecidableEq

inductive Pattern (φ: Type) (n: Nat) where
  | Empty
  | NotAllowed
  | Choice (p1 p2: Pattern φ n)
  | Interleave (p1 p2: Pattern φ n)
  | Group (p1 p2: Pattern φ n)
  | OneOrMore (p1: Pattern φ n)
  | Element (name: φ) (p1: Fin n)
  | After (p1 p2: Pattern φ n)
  deriving Repr, DecidableEq

structure Grammar (φ: Type) (n: Nat) where
  start: Pattern φ n
  prods: Vector (Pattern φ n) n

def Grammar.lookup (G: Grammar φ n) (ref: Fin n): Pattern φ n :=
  Vector.get G.prods ref

def Pattern.nullable : Pattern φ n -> Bool
  | (Group p1 p2) => nullable p1 && nullable p2
  | (Interleave p1 p2) => nullable p1 && nullable p2
  | (Choice p1 p2) => nullable p1 || nullable p2
  | (OneOrMore p) => nullable p
  | (Element _ _) => false
  | NotAllowed => false
  | Empty => true
  | (After _ _) => false

def choice : Pattern φ n -> Pattern φ n -> Pattern φ n
  | p1, p2 => Pattern.Choice p1 p2

def group : Pattern φ n -> Pattern φ n -> Pattern φ n
  | p1, p2 => Pattern.Group p1 p2

def interleave : Pattern φ n -> Pattern φ n -> Pattern φ n
  | p1, p2 => Pattern.Interleave p1 p2

def after : Pattern φ n -> Pattern φ n -> Pattern φ n
  | p1, p2 => Pattern.After p1 p2


def oneOrMore : Pattern φ n -> Pattern φ n
  | p => Pattern.OneOrMore p

def applyAfter : (Pattern φ n -> Pattern φ n) -> Pattern φ n -> Pattern φ n
  | f, (Pattern.After p1 p2) => after p1 (f p2)
  | f, (Pattern.Choice p1 p2) => choice (applyAfter f p1) (applyAfter f p2)
  | _, Pattern.NotAllowed => Pattern.NotAllowed
  | _, _ => Pattern.NotAllowed -- only defined to make the function total for Lean's sake

def startTagOpenDeriv (g: Grammar φ n) (Φ: φ -> α -> Bool) (p: Pattern φ n) (qn: α): Pattern φ n :=
  match p with
  | Pattern.Choice p1 p2 =>
    choice (startTagOpenDeriv g Φ p1 qn) (startTagOpenDeriv g Φ p2 qn)
  | Pattern.Element nc ref =>
    if Φ nc qn then after (g.lookup ref) Pattern.Empty else Pattern.NotAllowed
  | Pattern.Interleave p1 p2 =>
    choice (applyAfter (flip interleave p2) (startTagOpenDeriv g Φ p1 qn))
           (applyAfter (interleave p1) (startTagOpenDeriv g Φ p2 qn))
  | Pattern.OneOrMore p =>
    applyAfter (flip group (choice (Pattern.OneOrMore p) Pattern.Empty))
               (startTagOpenDeriv g Φ p qn)
  | Pattern.Group p1 p2 =>
    let x := applyAfter (flip group p2) (startTagOpenDeriv g Φ p1 qn)
    if Pattern.nullable p1 then
      choice x (startTagOpenDeriv g Φ p2 qn)
    else
      x
  | Pattern.After p1 p2 =>
    applyAfter (flip after p2) (startTagOpenDeriv g Φ p1 qn)
  | _ => Pattern.NotAllowed

def endTagDeriv: Pattern φ n -> Pattern φ n
  | Pattern.Choice p1 p2 => choice (endTagDeriv p1) (endTagDeriv p2)
  | Pattern.After p1 p2 => if Pattern.nullable p1 then p2 else Pattern.NotAllowed
  | _ => Pattern.NotAllowed

def childDeriv (g: Grammar φ n) (Φ: φ -> α -> Bool) (p: Pattern φ n) (node: Hedge.Node α): Pattern φ n :=
  match node with
  | Hedge.Node.mk qn children =>
      let p1 := startTagOpenDeriv g Φ p qn
      let p4 := List.foldl (childDeriv g Φ) p1 children
      endTagDeriv p4

def childrenDeriv (g: Grammar φ n) (Φ: φ -> α -> Bool) (p: Pattern φ n) (children: Hedge α): Pattern φ n :=
   List.foldl (childDeriv g Φ) p children

-- Examples

def childDerivStart (g: Grammar φ n) (Φ: φ -> α -> Bool) (node: Hedge.Node α): Pattern φ n :=
  childDeriv g Φ g.start node

def Pattern.optional (p: Pattern φ n): Pattern φ n :=
  Pattern.Choice p Pattern.Empty

-- element

#guard childDerivStart (Grammar.mk (Pattern.Element "hey" 0) #v[Pattern.Empty]) (· == ·) (Hedge.Node.mk "hey" [])
  = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element "hey" 0) #v[Pattern.Empty]) (· == ·) (Hedge.Node.mk "hello" [])
  = Pattern.NotAllowed

def node (name: α) (children: Hedge α): Hedge.Node α :=
  Hedge.Node.mk name children

-- recursive

#guard childDerivStart (Grammar.mk (Pattern.Element "doc" 0) #v[Pattern.Element "div" 1, Pattern.Empty]) (· == ·) (node "doc" [node "div" []])
  = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element "doc" 0) #v[Pattern.Choice (Pattern.Element "div" 0) Pattern.Empty]) (· == ·) (node "doc" [node "div" []])
 = Pattern.Choice (Pattern.Empty) (Pattern.NotAllowed)
  -- = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element "doc" 0) #v[Pattern.Choice (Pattern.Element "div" 0) Pattern.Empty]) (· == ·) (node "doc" [node "div" [node "div" []]])
 = Pattern.Choice (Pattern.Choice (Pattern.Empty) (Pattern.NotAllowed)) (Pattern.NotAllowed)
  -- = Pattern.Empty

-- after_buildup

namespace example_after_buildup_1

def qn := "hey"
def children: List ChildNode := []
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "hey" 0) #v[Pattern.Empty])
def p := g.start

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern String 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p1 = startTagOpenDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- endTagDeriv o p4
def p5: Pattern String 1 := Pattern.Empty
#guard p5 = endTagDeriv p4

end example_after_buildup_1

namespace example_after_buildup_2

def qn := "<div>"
def children: List ChildNode := []
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "<div>" 0) #v[Pattern.Choice (Pattern.Element "<div>" 0) Pattern.Empty])
def p0 := g.lookup 0
def p := g.lookup 0

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern String 1 := Pattern.Choice (Pattern.After (Pattern.Choice (Pattern.Element "<div>" 0) (Pattern.Empty)) (Pattern.Empty)) (Pattern.NotAllowed)
#guard p1 = startTagOpenDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.Choice (Pattern.After (Pattern.Choice (Pattern.Element "<div>" 0) (Pattern.Empty)) (Pattern.Empty)) (Pattern.NotAllowed)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- endTagDeriv o p4
def p5: Pattern String 1 := Pattern.Choice (Pattern.Empty) (Pattern.NotAllowed)
#guard p5 = endTagDeriv p4

#guard p5.nullable

end example_after_buildup_2

namespace example_after_buildup_3

-- Note that approximately equals:
-- childrenDeriv o cx g children ~= List.foldl (childDeriv o cx g) p children
-- So for a single recursive element (not an empty list or single text node) this would be:
-- childrenDeriv o cx g [child] ~= childDeriv o cx g p child

def qn := "<div>"
def children: Hedge String := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "div" 0) #v[Pattern.Choice (Pattern.Element "<div>" 0) Pattern.Empty])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern String 1 := Pattern.Choice (Pattern.After (Pattern.Choice (Pattern.Element "<div>" 0) (Pattern.Empty)) (Pattern.Empty)) (Pattern.NotAllowed)

-- let p1 := startTagOpenDeriv o g p qn
-- def p1: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element "<div>" 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.Empty))
def p1: Pattern String 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.After
      (Pattern.Choice
        (Pattern.Element "<div>" 0)
        (Pattern.Empty))
      (Pattern.After (Pattern.Empty) (Pattern.Empty)))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p1 = startTagOpenDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.Choice
      (Pattern.After
        (Pattern.Empty)
        (Pattern.After (Pattern.Empty) (Pattern.Empty)))
      (Pattern.NotAllowed))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- endTagDeriv o p4
def p5: Pattern String 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.Choice
      (Pattern.After (Pattern.Empty) (Pattern.Empty))
      (Pattern.NotAllowed))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p5 = endTagDeriv p4

#guard (endTagDeriv p5).nullable

end example_after_buildup_3

namespace example_after_buildup_4

def qn := "<div>"
def children: Hedge String := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "div" 0) #v[Pattern.Choice (Pattern.Element "<div>" 0) Pattern.Empty])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern String 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.After
      (Pattern.Choice
        (Pattern.Element "<div>" 0)
        (Pattern.Empty))
      (Pattern.After (Pattern.Empty) (Pattern.Empty)))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern String 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.Choice
      (Pattern.After
        (Pattern.Choice
          (Pattern.Element "<div>" 0)
          (Pattern.Empty))
        (Pattern.After
          (Pattern.Empty)
          (Pattern.After (Pattern.Empty) (Pattern.Empty))))
      (Pattern.NotAllowed))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p1 = startTagOpenDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.Choice
      (Pattern.Choice
        (Pattern.After
          (Pattern.Empty)
          (Pattern.After
            (Pattern.Empty)
            (Pattern.After (Pattern.Empty) (Pattern.Empty))))
        (Pattern.NotAllowed))
      (Pattern.NotAllowed))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- endTagDeriv o p4
def p5: Pattern String 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.Choice
      (Pattern.Choice
        (Pattern.After
          (Pattern.Empty)
          (Pattern.After (Pattern.Empty) (Pattern.Empty)))
        (Pattern.NotAllowed))
      (Pattern.NotAllowed))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p5 = endTagDeriv p4

#guard (endTagDeriv (endTagDeriv p5)).nullable

end example_after_buildup_4

-- helper functions to help make clear how the build up of close tags is happening if we keep recursing.
abbrev symbol (s: String × Fin n): Pattern String n :=
  Pattern.Element s.1 s.2
abbrev or (p1 p2: Pattern φ n): Pattern φ n :=
  Pattern.Choice p1 p2
abbrev emptystr : Pattern φ n := Pattern.Empty
abbrev closeDiv: Pattern φ n := Pattern.Empty
abbrev optional (p: Pattern φ n): Pattern φ n := Pattern.Choice p Pattern.Empty


namespace keep_uncles_and_aunts

def concat (p1 p2: Pattern φ n): Pattern φ n :=
  Pattern.Group p1 p2

def qn := "<head>"
def children: Hedge String := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := Grammar.mk (concat (symbol ("<head>", 0)) (symbol ("<body>", 0))) #v[optional (symbol ("<div>", 0))]
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern String 1 := g.start

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern String 1 := SimpleRelaxNG.Pattern.After
  (SimpleRelaxNG.Pattern.Choice
    (SimpleRelaxNG.Pattern.Element "<div>" 0)
    (SimpleRelaxNG.Pattern.Empty))
  (SimpleRelaxNG.Pattern.Group
    (SimpleRelaxNG.Pattern.Empty)
    (SimpleRelaxNG.Pattern.Element "<body>" 0))
#guard p1 = startTagOpenDeriv g (· == ·) p qn

end keep_uncles_and_aunts
