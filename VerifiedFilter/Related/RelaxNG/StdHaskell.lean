
-- TODO: write a better isSpace
def isSpace: Char -> Bool
  | c => c == ' '

-- TODO: write a better words
def words (xs: String): List (String) :=
  String.splitToList xs isSpace

-- TODO: write a better unwords
def unwords s := String.join s
