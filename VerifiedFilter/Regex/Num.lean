-- symbols returns the number of symbols in a regular expression.

import VerifiedFilter.Regex.Regex

namespace Regex

@[reducible, simp]
def symbols: (r: Regex σ) → Nat
  | emptyset => 0 | emptystr => 0 | symbol _ => 1 | star r1 => symbols r1
  | or r1 r2 => symbols r1 + symbols r2 | concat r1 r2 => symbols r1 + symbols r2
  | interleave r1 r2 => symbols r1 + symbols r2
  | and r1 r2 => symbols r1 + symbols r2 | compliment r1 => symbols r1

#guard symbols (or (symbol 'a') (star (symbol 'b'))) = 2
