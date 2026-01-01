import Validator.Std.Vec

import Validator.Regex.Regex
import Validator.Hedge.Grammar
import Validator.Hedge.Types

namespace Hedge

private def Grammar.evalif (G: Grammar n φ) (Φ: φ -> α -> Bool)
  : (s: Symbol n φ) -> (a: α) -> Rule n φ
  | (cnd, thn), a => if Φ cnd a then G.lookup thn else Regex.emptyset

end Hedge

namespace Hedge.Grammar

def evalifs {α: Type} {n: Nat}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (ifExprs: Symbols n φ l) (t: α): Rules n φ l :=
  Vec.map ifExprs (fun x => evalif G Φ x t)

theorem evalifs_nil_is_nil {α: Type} {n: Nat}
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (a: α):
  evalifs G Φ (n := n) Vec.nil a = Vec.nil := by
  unfold evalifs
  simp only [Vec.map_nil]
