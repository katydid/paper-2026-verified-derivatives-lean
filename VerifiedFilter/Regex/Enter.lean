import VerifiedFilter.Std.Vec

import VerifiedFilter.Regex.Extract
import VerifiedFilter.Regex.Num
import VerifiedFilter.Regex.Regex

namespace Regex

def enter (r: Regex σ): Vector σ (symbols r) := (extract r).2

#guard enter (or (symbol 'a') (star (symbol 'b'))) = #v['a','b']
