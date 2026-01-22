import Mathlib.Tactic.NthRewrite

import Validator.Std.Hedge

namespace SimpleRelaxNG

inductive Pattern (φ: Type) (n: Nat) where
  | EmptyStr
  | EmptySet
  | Or (p1 p2: Pattern φ n)
  | Interleave (p1 p2: Pattern φ n)
  | Concat (p1 p2: Pattern φ n)
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
  | (Concat p1 p2) => nullable p1 && nullable p2
  | (Interleave p1 p2) => nullable p1 && nullable p2
  | (Or p1 p2) => nullable p1 || nullable p2
  | (OneOrMore p) => nullable p
  | (Element _ _) => false
  | EmptySet => false
  | EmptyStr => true
  | (After _ _) => false

def applyAfter : (Pattern φ n -> Pattern φ n) -> Pattern φ n -> Pattern φ n
  | f, (Pattern.After p1 p2) => Pattern.After p1 (f p2)
  | f, (Pattern.Or p1 p2) => Pattern.Or (applyAfter f p1) (applyAfter f p2)
  | _, Pattern.EmptySet => Pattern.EmptySet
  | _, p => p -- only defined to make the function total for Lean's sake

def openDeriv (g: Grammar φ n) (Φ: φ -> α -> Bool) (p: Pattern φ n) (label: α): Pattern φ n :=
  match p with
  | Pattern.EmptySet => Pattern.EmptySet
  | Pattern.EmptyStr => Pattern.EmptySet
  | Pattern.Element nc ref => if Φ nc label
    then Pattern.After (g.lookup ref) Pattern.EmptyStr
    else Pattern.EmptySet
  | Pattern.Or p1 p2 =>
    Pattern.Or (openDeriv g Φ p1 label) (openDeriv g Φ p2 label)
  | Pattern.Concat p1 p2 =>
    let x := applyAfter (flip Pattern.Concat p2) (openDeriv g Φ p1 label)
    if Pattern.nullable p1
    then Pattern.Or x (openDeriv g Φ p2 label)
    else x
  | Pattern.OneOrMore p => let zeroOrMore := Pattern.Or (Pattern.OneOrMore p) Pattern.EmptyStr
    applyAfter (flip Pattern.Concat zeroOrMore) (openDeriv g Φ p label)
  | Pattern.Interleave p1 p2 => Pattern.Or
      (applyAfter (Pattern.Interleave p2) (openDeriv g Φ p1 label))
      (applyAfter (Pattern.Interleave p1) (openDeriv g Φ p2 label))
  | Pattern.After p1 p2 =>
    applyAfter (flip Pattern.After p2) (openDeriv g Φ p1 label)

def closeDeriv: Pattern φ n -> Pattern φ n
  | Pattern.Or p1 p2 => Pattern.Or (closeDeriv p1) (closeDeriv p2)
  | Pattern.After p1 p2 => if Pattern.nullable p1 then p2 else Pattern.EmptySet
  | _ => Pattern.EmptySet

def childDeriv (g: Grammar φ n) (Φ: φ -> α -> Bool) (p: Pattern φ n) (node: Hedge.Node α): Pattern φ n :=
  match node with
  | Hedge.Node.mk label children =>
    let opened := openDeriv g Φ p label
    let p' := List.foldl (childDeriv g Φ) opened children
    closeDeriv p'

def childrenDeriv (g: Grammar φ n) (Φ: φ -> α -> Bool) (p: Pattern φ n) (children: Hedge α): Pattern φ n :=
   List.foldl (childDeriv g Φ) p children

-- Examples

def childDerivStart (g: Grammar φ n) (Φ: φ -> α -> Bool) (node: Hedge.Node α): Pattern φ n :=
  childDeriv g Φ g.start node

def Pattern.optional (p: Pattern φ n): Pattern φ n :=
  Pattern.Or p Pattern.EmptyStr

-- element

#guard childDerivStart (Grammar.mk (Pattern.Element "hey" 0) #v[Pattern.EmptyStr]) (· == ·) (Hedge.Node.mk "hey" [])
  = Pattern.EmptyStr

#guard childDerivStart (Grammar.mk (Pattern.Element "hey" 0) #v[Pattern.EmptyStr]) (· == ·) (Hedge.Node.mk "hello" [])
  = Pattern.EmptySet

def node (name: α) (children: Hedge α): Hedge.Node α :=
  Hedge.Node.mk name children

-- recursive

#guard childDerivStart (Grammar.mk (Pattern.Element "doc" 0) #v[Pattern.Element "div" 1, Pattern.EmptyStr]) (· == ·) (node "doc" [node "div" []])
  = Pattern.EmptyStr

#guard childDerivStart (Grammar.mk (Pattern.Element "doc" 0) #v[Pattern.Or (Pattern.Element "div" 0) Pattern.EmptyStr]) (· == ·) (node "doc" [node "div" []])
 = Pattern.Or (Pattern.EmptyStr) (Pattern.EmptySet)
  -- = Pattern.EmptyStr

#guard childDerivStart (Grammar.mk (Pattern.Element "doc" 0) #v[Pattern.Or (Pattern.Element "div" 0) Pattern.EmptyStr]) (· == ·) (node "doc" [node "div" [node "div" []]])
 = Pattern.Or (Pattern.Or (Pattern.EmptyStr) (Pattern.EmptySet)) (Pattern.EmptySet)
  -- = Pattern.EmptyStr

-- after_buildup

namespace example_after_buildup_1

def qn := "hey"
def children: List ChildNode := []
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "hey" 0) #v[Pattern.EmptyStr])
def p := g.start

-- let p1 := openDeriv o g p qn
def p1: Pattern String 1 := Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr)
#guard p1 = openDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- closeDeriv o p4
def p5: Pattern String 1 := Pattern.EmptyStr
#guard p5 = closeDeriv p4

end example_after_buildup_1

namespace example_after_buildup_2

def qn := "<div>"
def children: List ChildNode := []
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "<div>" 0) #v[Pattern.Or (Pattern.Element "<div>" 0) Pattern.EmptyStr])
def p0 := g.lookup 0
def p := g.lookup 0

-- let p1 := openDeriv o g p qn
def p1: Pattern String 1 := Pattern.Or (Pattern.After (Pattern.Or (Pattern.Element "<div>" 0) (Pattern.EmptyStr)) (Pattern.EmptyStr)) (Pattern.EmptySet)
#guard p1 = openDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.Or (Pattern.After (Pattern.Or (Pattern.Element "<div>" 0) (Pattern.EmptyStr)) (Pattern.EmptyStr)) (Pattern.EmptySet)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- closeDeriv o p4
def p5: Pattern String 1 := Pattern.Or (Pattern.EmptyStr) (Pattern.EmptySet)
#guard p5 = closeDeriv p4

#guard p5.nullable

end example_after_buildup_2

namespace example_after_buildup_3

-- Note that approximately equals:
-- childrenDeriv o cx g children ~= List.foldl (childDeriv o cx g) p children
-- So for a single recursive element (not an EmptyStr list or single text node) this would be:
-- childrenDeriv o cx g [child] ~= childDeriv o cx g p child

def qn := "<div>"
def children: Hedge String := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "div" 0) #v[Pattern.Or (Pattern.Element "<div>" 0) Pattern.EmptyStr])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern String 1 := Pattern.Or (Pattern.After (Pattern.Or (Pattern.Element "<div>" 0) (Pattern.EmptyStr)) (Pattern.EmptyStr)) (Pattern.EmptySet)

-- let p1 := openDeriv o g p qn
-- def p1: Pattern 1 := Pattern.After (Pattern.Or (Pattern.Element "<div>" 0) (Pattern.EmptyStr)) (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr))
def p1: Pattern String 1 := Pattern.Or
  (Pattern.Or
    (Pattern.After
      (Pattern.Or
        (Pattern.Element "<div>" 0)
        (Pattern.EmptyStr))
      (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr)))
    (Pattern.EmptySet))
  (Pattern.EmptySet)
#guard p1 = openDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.Or
  (Pattern.Or
    (Pattern.Or
      (Pattern.After
        (Pattern.EmptyStr)
        (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr)))
      (Pattern.EmptySet))
    (Pattern.EmptySet))
  (Pattern.EmptySet)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- closeDeriv o p4
def p5: Pattern String 1 := Pattern.Or
  (Pattern.Or
    (Pattern.Or
      (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr))
      (Pattern.EmptySet))
    (Pattern.EmptySet))
  (Pattern.EmptySet)
#guard p5 = closeDeriv p4

#guard (closeDeriv p5).nullable

end example_after_buildup_3

namespace example_after_buildup_4

def qn := "<div>"
def children: Hedge String := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := (Grammar.mk (Pattern.Element "div" 0) #v[Pattern.Or (Pattern.Element "<div>" 0) Pattern.EmptyStr])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern String 1 := Pattern.Or
  (Pattern.Or
    (Pattern.After
      (Pattern.Or
        (Pattern.Element "<div>" 0)
        (Pattern.EmptyStr))
      (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr)))
    (Pattern.EmptySet))
  (Pattern.EmptySet)

-- let p1 := openDeriv o g p qn
def p1: Pattern String 1 := Pattern.Or
  (Pattern.Or
    (Pattern.Or
      (Pattern.After
        (Pattern.Or
          (Pattern.Element "<div>" 0)
          (Pattern.EmptyStr))
        (Pattern.After
          (Pattern.EmptyStr)
          (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr))))
      (Pattern.EmptySet))
    (Pattern.EmptySet))
  (Pattern.EmptySet)
#guard p1 = openDeriv g (· == ·) p qn

-- let p4 := childrenDeriv o cx g p3 children
def p4: Pattern String 1 := Pattern.Or
  (Pattern.Or
    (Pattern.Or
      (Pattern.Or
        (Pattern.After
          (Pattern.EmptyStr)
          (Pattern.After
            (Pattern.EmptyStr)
            (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr))))
        (Pattern.EmptySet))
      (Pattern.EmptySet))
    (Pattern.EmptySet))
  (Pattern.EmptySet)
#guard p4 = childrenDeriv g (· == ·) p1 children

-- closeDeriv o p4
def p5: Pattern String 1 := Pattern.Or
  (Pattern.Or
    (Pattern.Or
      (Pattern.Or
        (Pattern.After
          (Pattern.EmptyStr)
          (Pattern.After (Pattern.EmptyStr) (Pattern.EmptyStr)))
        (Pattern.EmptySet))
      (Pattern.EmptySet))
    (Pattern.EmptySet))
  (Pattern.EmptySet)
#guard p5 = closeDeriv p4

#guard (closeDeriv (closeDeriv p5)).nullable

end example_after_buildup_4

-- helper functions to help make clear how the build up of close tags is happening if we keep recursing.
abbrev symbol (s: String × Fin n): Pattern String n :=
  Pattern.Element s.1 s.2
abbrev or (p1 p2: Pattern φ n): Pattern φ n :=
  Pattern.Or p1 p2
abbrev EmptyStrstr : Pattern φ n := Pattern.EmptyStr
abbrev closeDiv: Pattern φ n := Pattern.EmptyStr
abbrev optional (p: Pattern φ n): Pattern φ n := Pattern.Or p Pattern.EmptyStr


namespace keep_uncles_and_aunts

def concat (p1 p2: Pattern φ n): Pattern φ n :=
  Pattern.Concat p1 p2

def qn := "<head>"
def children: Hedge String := [Hedge.Node.mk qn []]
def childNode := Hedge.Node.mk qn children

def g := Grammar.mk (concat (symbol ("<head>", 0)) (symbol ("<body>", 0))) #v[optional (symbol ("<div>", 0))]
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern String 1 := g.start

-- let p1 := openDeriv o g p qn
def p1: Pattern String 1 := SimpleRelaxNG.Pattern.After
  (SimpleRelaxNG.Pattern.Or
    (SimpleRelaxNG.Pattern.Element "<div>" 0)
    (SimpleRelaxNG.Pattern.EmptyStr))
  (SimpleRelaxNG.Pattern.Concat
    (SimpleRelaxNG.Pattern.EmptyStr)
    (SimpleRelaxNG.Pattern.Element "<body>" 0))
#guard p1 = openDeriv g (· == ·) p qn

end keep_uncles_and_aunts
