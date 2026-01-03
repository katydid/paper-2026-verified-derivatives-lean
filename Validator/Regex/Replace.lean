import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex

def Symbol.replaceLE (r: RegexID n) (xs: Vector σ l) (h: n <= l): Regex σ :=
  match r with
  | emptyset => emptyset | emptystr => emptystr
  | symbol ⟨s, hs⟩ => symbol (Vector.get xs (Fin.mk s (by omega)))
  | or r1 r2 => or (replaceLE r1 xs h) (replaceLE r2 xs h)
  | concat r1 r2 => concat (replaceLE r1 xs h) (replaceLE r2 xs h)
  | star r1 => star (replaceLE r1 xs h)

def Symbol.replace (r: RegexID n) (xs: Vector σ n): Regex σ :=
  replaceLE r xs (Nat.le_refl n)

end Regex

namespace Regex.Symbol

theorem replaceLE_cast_both (r: RegexID n) (xs: Vector σ n) (h: n = l):
  replaceLE r xs (by omega) = replaceLE (RegexID.cast r h) (Vector.cast h xs) (by omega) := by
  subst h
  simp only [Vector.cast_rfl]
  rfl

theorem replaceLE_cast_symbols (r: RegexID n) (xs: Vector σ n) (h: n = l):
  replaceLE r xs (by omega) = replaceLE r (Vector.cast h xs) (by omega) := by
  subst h
  simp only [Vector.cast_rfl]

theorem replaceLE_take (r: RegexID n) (xs: Vector σ (n + l)):
  replaceLE r (Vector.take xs n) (by omega) = replaceLE r xs (by omega):= by
  induction r with
  | emptyset =>
    simp only [replaceLE]
  | emptystr =>
    simp only [replaceLE]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp only [replaceLE]
    obtain ⟨s, hs⟩ := s
    simp only [Regex.symbol.injEq]
    generalize_proofs h3 h4
    rw [Vector.take_get]
    omega
  | or r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.or.injEq]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.concat.injEq]
    generalize_proofs h1 h2 at *
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replaceLE]
    generalize_proofs h1 at *
    rw [<- ih1]

theorem replaceLE_regexid_add (r: RegexID n) (xs: Vector σ (n + l)):
  replaceLE r xs (by omega) = replaceLE (RegexID.cast_add l r) xs (by omega):= by
  generalize_proofs h1 h2
  induction r with
  | emptyset =>
    simp only [replaceLE, RegexID.cast_add, Regex.map]
  | emptystr =>
    simp only [replaceLE, RegexID.cast_add, Regex.map]
  | symbol s =>
    generalize_proofs h1 h2 at *
    simp only [replaceLE, RegexID.cast_add, Regex.map, Fin.coe_castLE]
  | or r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.or.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.concat.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.star.injEq]
    generalize_proofs h1 h2 at *
    rw [ih1]
    rfl
