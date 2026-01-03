import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Point
import Validator.Regex.Regex
import Validator.Regex.Replace

namespace Regex

def leave (r: Regex σ): Vector Bool (Symbol.num r) -> Regex σ :=
  fun bools => Regex.Point.derive (
    Vector.zip (Symbol.extract r).2 bools |>
    Symbol.replace (Symbol.extract r).1
  )
