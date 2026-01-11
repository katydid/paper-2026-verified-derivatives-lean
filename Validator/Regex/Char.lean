import Validator.Regex.Regex

def Regex.Char.derive (r: Regex Char) (a: Char): Regex Char := match r with
  | emptyset => emptyset | emptystr => emptyset
  | symbol s => onlyif (s == a) emptystr
  | or r1 r2 => or (derive r1 a) (derive r2 a)
  | concat r1 r2 => or
      (concat (derive r1 a) r2)
      (onlyif (null r1) (derive r2 a))
  | star r1 => concat (derive r1 a) (star r1)
  | interleave r1 r2 => or
      (interleave (derive r1 a) r2)
      (interleave (derive r2 a) r1)

theorem Regex.Char.derive_is_derive_symbol:
  Regex.Char.derive r a = Regex.derive (fun s a => s == a) r a := by
  induction r with
  | emptyset => rfl
  | emptystr => rfl
  | symbol s => rfl
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
