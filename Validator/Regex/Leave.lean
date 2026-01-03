import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Point
import Validator.Regex.Regex
import Validator.Regex.Replace

namespace Regex

def leave (r: Regex σ) (bools: Vector Bool (Symbol.num r)): Regex σ :=
  let points := Vector.zip (Symbol.extract r).2 bools
  let r' := Symbol.replace (Symbol.extract r).1 points
  Regex.Point.derive r'
