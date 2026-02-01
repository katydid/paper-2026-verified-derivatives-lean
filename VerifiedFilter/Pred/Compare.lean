-- A simple predicate with comparisons.
namespace Pred.Compare

inductive Pred (α: Type): Type where
  | any
  | eq (t: α)
  | ge (t: α)
  | gt (t: α)
  | le (t: α)
  | lt (t: α)
  deriving DecidableEq, Ord, Repr, Hashable

def Pred.evalb {α: Type} [DecidableEq α] [LE α] [LT α] [DecidableLE α] [DecidableLT α] (p: Pred α) (x: α): Bool :=
  match p with
  | Pred.any => true
  | Pred.eq y => x = y
  | Pred.ge y => x >= y
  | Pred.gt y => x > y
  | Pred.le y => x <= y
  | Pred.lt y => x < y
