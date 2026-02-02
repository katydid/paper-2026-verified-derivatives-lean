-- StdHaskell is a substandard implementaton of the Haskell standard library functions used by RelaxNG.
-- It serves its purpose, as it allows us to play around with RelaxNG,
-- outside of some whitespace edge cases that this library needs to be improved for to properly cover.

-- TODO: write a better isSpace
def isSpace: Char -> Bool
  | c => c == ' '

-- TODO: write a better words
def words (xs: String): List (String) :=
  String.splitToList xs isSpace

-- TODO: write a better unwords
def unwords s := String.join s
