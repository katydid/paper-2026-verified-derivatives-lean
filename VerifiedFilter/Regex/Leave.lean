import VerifiedFilter.Regex.Extract
import VerifiedFilter.Regex.Num
import VerifiedFilter.Regex.Point
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Replace

namespace Regex

def leave (r: Regex σ) (bools: Vector Bool (symbols r)): Regex σ :=
  let points: Vector (σ × Bool) r.symbols := Vector.zip (extract r).2 bools
  let rpoint: Regex (σ × Bool) := replace (extract r).1 points
  Regex.Point.derive rpoint
