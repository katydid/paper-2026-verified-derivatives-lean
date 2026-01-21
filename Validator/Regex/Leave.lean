import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Point
import Validator.Regex.Regex
import Validator.Regex.Replace

namespace Regex

def leave (r: Regex σ) (bools: Vector Bool (symbols r)): Regex σ :=
  let points: Vector (σ × Bool) r.symbols := Vector.zip (extract r).2 bools
  let rpoint: Regex (σ × Bool) := replace (extract r).1 points
  Regex.Point.derive rpoint
