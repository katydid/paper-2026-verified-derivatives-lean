import VerifiedFilter.Regex.Num
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.RegexID

namespace Regex

def replaceLE (r: RegexID n) (xs: Vector σ l) (h: n <= l): Regex σ :=
  match r with
  | emptyset => emptyset | emptystr => emptystr
  | symbol ⟨s, hs⟩ => symbol (Vector.get xs (Fin.mk s (by omega)))
  | or r1 r2 => or (replaceLE r1 xs h) (replaceLE r2 xs h)
  | concat r1 r2 => concat (replaceLE r1 xs h) (replaceLE r2 xs h)
  | star r1 => star (replaceLE r1 xs h)
  | interleave r1 r2 => interleave (replaceLE r1 xs h) (replaceLE r2 xs h)
  | and r1 r2 => and (replaceLE r1 xs h) (replaceLE r2 xs h)
  | compliment r1 => compliment (replaceLE r1 xs h)

def replace (r: Regex (Fin n)) (xs: Vector σ n): Regex σ :=
  replaceLE r xs (Nat.le_refl n)

#guard replace (or (symbol 0) (star (symbol 1))) #v['a', 'b']
  = (or (symbol 'a') (star (symbol 'b')))

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
    simp only [replaceLE]
    obtain ⟨s, hs⟩ := s
    simp only [Regex.symbol.injEq]
    rw [Vector.take_get]
    omega
  | or r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.or.injEq]
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.concat.injEq]
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replaceLE]
    rw [<- ih1]
  | interleave r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.interleave.injEq]
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | and r1 r2 ih1 ih2 =>
    simp only [replaceLE, Regex.and.injEq]
    rw [<- ih1]
    rw [<- ih2]
    apply And.intro rfl rfl
  | compliment r1 ih1 =>
    simp only [replaceLE]
    rw [<- ih1]

theorem replaceLE_regexid_add (r: RegexID n) (xs: Vector σ (n + l)):
  replaceLE r xs (by omega) = replaceLE (RegexID.cast_add l r) xs (by omega):= by
  induction r with
  | emptyset =>
    simp only [replaceLE, RegexID.cast_add, Regex.map]
  | emptystr =>
    simp only [replaceLE, RegexID.cast_add, Regex.map]
  | symbol s =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Fin.val_castLE]
  | or r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.or.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.concat.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | star r1 ih1 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.star.injEq]
    rw [ih1]
    rfl
  | interleave r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.interleave.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | and r1 r2 ih1 ih2 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.and.injEq]
    rw [ih1]
    rw [ih2]
    apply And.intro rfl rfl
  | compliment r1 ih1 =>
    simp only [replaceLE, RegexID.cast_add, Regex.map, Regex.compliment.injEq]
    rw [ih1]
    rfl
