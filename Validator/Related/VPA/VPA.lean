import Validator.Regex.Regex
import Validator.Hedge.Grammar

namespace Vpa

-- mock implementation
def Stack := Unit

-- mock implementation
def VPA.call: Regex (φ × Ref n) -> α -> (Stack × Regex (φ × Ref n))
  | r, _ => ((), r)

-- mock implementation
def VPA.return : Stack -> Regex (φ × Ref n) -> α -> Regex (φ × Ref n)
  | _, r, _ => r
