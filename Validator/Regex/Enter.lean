import Validator.Std.Vec

import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Regex

namespace Regex

def enter (r: Regex σ): Vector σ (Symbol.num r) :=
  (Symbol.extract r).2

#guard enter (Regex.or (Regex.symbol 'a') (Regex.symbol 'b'))
  = #v['a', 'b']
