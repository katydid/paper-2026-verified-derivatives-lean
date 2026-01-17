import Validator.Std.Vec

import Validator.Regex.Extract
import Validator.Regex.IfExpr.IfExpr
import Validator.Regex.Num
import Validator.Regex.Regex

namespace Regex

def IfExpr.enter (r: Regex σ): IfExpr σ (symbols r) := IfExpr.mk (extract r).2

#guard IfExpr.enter (or (symbol 'a') (symbol 'b')) =
  IfExpr.expr 'a'
    (IfExpr.expr 'b' (IfExpr.res  #v[true, true]) (IfExpr.res  #v[true, false]))
    (IfExpr.expr 'b' (IfExpr.res  #v[false, true]) (IfExpr.res  #v[false, false]))
