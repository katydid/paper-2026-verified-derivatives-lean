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

inductive Pattern (n: Nat) where
  | Empty
  | NotAllowed
  | Choice (p1 p2: Pattern n)
  | Interleave (p1 p2: Pattern n)
  | Group (p1 p2: Pattern n)
  | OneOrMore (p1: Pattern n)
  | Element (name: NameClass) (p1: Fin n)
  | After (p1 p2: Pattern n)
  deriving Repr, DecidableEq

structure Grammar (n: Nat) where
  start: Pattern n
  prods: Vector (Pattern n) n

def Grammar.lookup (G: Grammar n) (ref: Fin n): Pattern n :=
  Vector.get G.prods ref

abbrev ChildNode := Hedge.Node String

def NameClass.contains: NameClass -> String -> Bool
  | AnyName, _ => true
  | AnyNameExcept nc, n => not (contains nc n)
  | Name ln1, ln2 => (ln1 == ln2)
  | NameClassChoice nc1 nc2, n => (contains nc1 n) || (contains nc2 n)

def Pattern.nullable : Pattern n -> Bool
  | (Group p1 p2) => nullable p1 && nullable p2
  | (Interleave p1 p2) => nullable p1 && nullable p2
  | (Choice p1 p2) => nullable p1 || nullable p2
  | (OneOrMore p) => nullable p
  | (Element _ _) => false
  | NotAllowed => false
  | Empty => true
  | (After _ _) => false

def choice : Pattern n -> Pattern n -> Pattern n
  | p1, p2 => Pattern.Choice p1 p2

def group : Pattern n -> Pattern n -> Pattern n
  | p1, p2 => Pattern.Group p1 p2

def interleave : Pattern n -> Pattern n -> Pattern n
  | p1, p2 => Pattern.Interleave p1 p2

def after : Pattern n -> Pattern n -> Pattern n
  | p1, p2 => Pattern.After p1 p2


def oneOrMore : Pattern n -> Pattern n
  | p => Pattern.OneOrMore p

def applyAfter : (Pattern n -> Pattern n) -> Pattern n -> Pattern n
  | f, (Pattern.After p1 p2) => after p1 (f p2)
  | f, (Pattern.Choice p1 p2) => choice (applyAfter f p1) (applyAfter f p2)
  | _, Pattern.NotAllowed => Pattern.NotAllowed
  | _, _ => Pattern.NotAllowed -- only defined to make the function total for Lean's sake

def startTagOpenDeriv (g: Grammar n) (p: Pattern n) (qn: String): Pattern n :=
  match p with
  | Pattern.Choice p1 p2 =>
    choice (startTagOpenDeriv g p1 qn) (startTagOpenDeriv g p2 qn)
  | Pattern.Element nc ref =>
    if NameClass.contains nc qn then after (g.lookup ref) Pattern.Empty else Pattern.NotAllowed
  | Pattern.Interleave p1 p2 =>
    choice (applyAfter (flip interleave p2) (startTagOpenDeriv g p1 qn))
           (applyAfter (interleave p1) (startTagOpenDeriv g p2 qn))
  | Pattern.OneOrMore p =>
    applyAfter (flip group (choice (Pattern.OneOrMore p) Pattern.Empty))
               (startTagOpenDeriv g p qn)
  | Pattern.Group p1 p2 =>
    let x := applyAfter (flip group p2) (startTagOpenDeriv g p1 qn)
    if Pattern.nullable p1 then
      choice x (startTagOpenDeriv g p2 qn)
    else
      x
  | Pattern.After p1 p2 =>
    applyAfter (flip after p2) (startTagOpenDeriv g p1 qn)
  | _ => Pattern.NotAllowed

def endTagDeriv: Pattern n -> Pattern n
  | Pattern.Choice p1 p2 => choice (endTagDeriv p1) (endTagDeriv p2)
  | Pattern.After p1 p2 => if Pattern.nullable p1 then p2 else Pattern.NotAllowed
  | _ => Pattern.NotAllowed

def childDeriv (g: Grammar n) (p: Pattern n) (node: ChildNode): Pattern n :=
  match node with
  | Hedge.Node.mk qn children =>
      let p1 := startTagOpenDeriv g p qn
      let p4 := List.foldl (childDeriv g) p1 children
      endTagDeriv p4

def childrenDeriv (g: Grammar n) (p: Pattern n) (children: List ChildNode): Pattern n :=
   List.foldl (childDeriv g) p children

-- Examples

def childDerivStart (g: Grammar n) (node: ChildNode): Pattern n :=
  childDeriv g g.start node

def Pattern.optional (p: Pattern n): Pattern n :=
  Pattern.Choice p Pattern.Empty

-- basics

def ChildNode.mkElement (name: String) (children: List ChildNode): ChildNode :=
  (Hedge.Node.mk name children)

def NameClass.mk (name: String): NameClass :=
  NameClass.Name name

-- element

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "hey") 0) #v[Pattern.Empty]) (ChildNode.mkElement "hey" [])
  = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "hey") 0) #v[Pattern.Empty]) (ChildNode.mkElement "hello" [])
  = Pattern.NotAllowed

def node (name: String) (children: List ChildNode): ChildNode :=
  ChildNode.mkElement name children

-- recursive

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "doc") 0) #v[Pattern.Element (NameClass.mk "div") 1, Pattern.Empty]) (node "doc" [node "div" []])
  = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "doc") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "div") 0) Pattern.Empty]) (node "doc" [node "div" []])
 = Pattern.Choice (Pattern.Empty) (Pattern.NotAllowed)
  -- = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "doc") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "div") 0) Pattern.Empty]) (node "doc" [node "div" [node "div" []]])
 = Pattern.Choice (Pattern.Choice (Pattern.Empty) (Pattern.NotAllowed)) (Pattern.NotAllowed)
  -- = Pattern.Empty

-- after_buildup

namespace example_after_buildup_1

def qn := "hey"
def children: List ChildNode := []
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "hey") 0) #v[Pattern.Empty])
def p := g.start

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p1 = startTagOpenDeriv g p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p4 = childrenDeriv g p1 children

-- endTagDeriv o p4
def p5: Pattern 1 := Pattern.Empty
#guard p5 = endTagDeriv p4

end example_after_buildup_1

namespace example_after_buildup_2

def qn := "<div>"
def children: List ChildNode := []
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "<div>") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "<div>") 0) Pattern.Empty])
def p0 := g.lookup 0
def p := g.lookup 0

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern 1 := Pattern.Choice (Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "<div>") 0) (Pattern.Empty)) (Pattern.Empty)) (Pattern.NotAllowed)
#guard p1 = startTagOpenDeriv g p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern 1 := Pattern.Choice (Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "<div>") 0) (Pattern.Empty)) (Pattern.Empty)) (Pattern.NotAllowed)
#guard p4 = childrenDeriv g p1 children

-- endTagDeriv o p4
def p5: Pattern 1 := Pattern.Choice (Pattern.Empty) (Pattern.NotAllowed)
#guard p5 = endTagDeriv p4

#guard p5.nullable

end example_after_buildup_2

namespace example_after_buildup_3

-- Note that approximately equals:
-- childrenDeriv o cx g children ~= List.foldl (childDeriv o cx g) p children
-- So for a single recursive element (not an empty list or single text node) this would be:
-- childrenDeriv o cx g [child] ~= childDeriv o cx g p child

def qn := "<div>"
def children: List ChildNode := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "div") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "<div>") 0) Pattern.Empty])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern 1 := Pattern.Choice (Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "<div>") 0) (Pattern.Empty)) (Pattern.Empty)) (Pattern.NotAllowed)

-- let p1 := startTagOpenDeriv o g p qn
-- def p1: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.Empty))
def p1: Pattern 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.After
      (Pattern.Choice
        (Pattern.Element (NameClass.Name "<div>") 0)
        (Pattern.Empty))
      (Pattern.After (Pattern.Empty) (Pattern.Empty)))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p1 = startTagOpenDeriv g p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.Choice
      (Pattern.After
        (Pattern.Empty)
        (Pattern.After (Pattern.Empty) (Pattern.Empty)))
      (Pattern.NotAllowed))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p4 = childrenDeriv g p1 children

-- endTagDeriv o p4
def p5: Pattern 1 := Pattern.Choice
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
def children: List ChildNode := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "div") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "<div>") 0) Pattern.Empty])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.After
      (Pattern.Choice
        (Pattern.Element (NameClass.Name "<div>") 0)
        (Pattern.Empty))
      (Pattern.After (Pattern.Empty) (Pattern.Empty)))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern 1 := Pattern.Choice
  (Pattern.Choice
    (Pattern.Choice
      (Pattern.After
        (Pattern.Choice
          (Pattern.Element (NameClass.Name "<div>") 0)
          (Pattern.Empty))
        (Pattern.After
          (Pattern.Empty)
          (Pattern.After (Pattern.Empty) (Pattern.Empty))))
      (Pattern.NotAllowed))
    (Pattern.NotAllowed))
  (Pattern.NotAllowed)
#guard p1 = startTagOpenDeriv g p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern 1 := Pattern.Choice
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
#guard p4 = childrenDeriv g p1 children

-- endTagDeriv o p4
def p5: Pattern 1 := Pattern.Choice
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
abbrev symbol (s: String × Fin n): Pattern n :=
  Pattern.Element (NameClass.mk s.1) s.2
abbrev or (p1 p2: Pattern n): Pattern n :=
  Pattern.Choice p1 p2
abbrev emptystr : Pattern n := Pattern.Empty
abbrev closeDiv: Pattern n := Pattern.Empty
abbrev optional (p: Pattern n): Pattern n := Pattern.Choice p Pattern.Empty


namespace keep_uncles_and_aunts

def concat (p1 p2: Pattern n): Pattern n :=
  Pattern.Group p1 p2

def qn := "<head>"
def children: List ChildNode := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := Grammar.mk (concat (symbol ("<head>", 0)) (symbol ("<body>", 0))) #v[optional (symbol ("<div>", 0))]
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern 1 := g.start

-- let p1 := startTagOpenDeriv o g p qn
def p1: Pattern 1 := SimpleRelaxNG.Pattern.After
  (SimpleRelaxNG.Pattern.Choice
    (SimpleRelaxNG.Pattern.Element (SimpleRelaxNG.NameClass.Name "<div>") 0)
    (SimpleRelaxNG.Pattern.Empty))
  (SimpleRelaxNG.Pattern.Group
    (SimpleRelaxNG.Pattern.Empty)
    (SimpleRelaxNG.Pattern.Element (SimpleRelaxNG.NameClass.Name "<body>") 0))
#guard p1 = startTagOpenDeriv g p qn

end keep_uncles_and_aunts
