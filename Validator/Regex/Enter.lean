import Validator.Std.Vec

import Validator.Regex.Extract
import Validator.Regex.Num
import Validator.Regex.Regex

namespace Regex

def enter (r: Regex σ): Vector σ (symbols r) := (extract r).2

#guard enter (or (symbol 'a') (symbol 'b')) = #v['a','b']
