import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.RegexID

namespace Regex

theorem Symbol.lt_add_symbol:
  n < n + num (symbol s) := by
  simp only [num]
  omega

def Symbol.extract (r: Regex σ) (acc: Vec σ n): RegexID (n + num r) × Vec σ (n + num r) :=
  match r with
  | emptyset => (emptyset, acc)
  | emptystr => (emptystr, acc)
  | symbol s => (symbol (Fin.mk n lt_add_symbol), Vec.snoc acc s)
  | or r1 r2 =>
    let (rid1, acc1) := extract r1 acc
    let (rid2, acc2) := extract r2 acc1
    (or (rid1.cast_add (num r2)).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | concat r1 r2 =>
    let (rid1, acc1) := extract r1 acc
    let (rid2, acc2) := extract r2 acc1
    (concat (rid1.cast_add (num r2)).cast_assoc rid2.cast_assoc, acc2.cast_assoc)
  | star r1 => let (rid1, acc1) := extract r1 acc; (star rid1, acc1)

def Symbol.extractFrom (r: Regex σ): RegexID (num r) × Vec σ (num r) :=
  let (rid, xs) := extract r Vec.nil
  (RegexID.cast rid (by omega), Vec.cast xs (by omega))

end Regex

namespace Regex.Symbol

theorem extract_append_toList (acc: Vec σ n) (r: Regex σ):
  Vec.toList (extract r acc).2 = Vec.toList (Vec.append acc (extract r Vec.nil).2) := by
  induction r generalizing acc n  with
  | emptyset =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | emptystr =>
    simp only [Symbol.num, Nat.add_zero, extract, Vec.append_nil, Vec.cast_toList]
  | symbol s =>
    simp only [extract, Vec.snoc]
    rw [Vec.snoc_append]
  | or r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vec.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vec.cast_assoc]
    generalize_proofs h4
    rw [Vec.toList_append]
    rw [Vec.cast_toList]
    rw [Vec.cast_toList]
    rw [ih2]
    rw [Vec.toList_append]
    rw [ih1]
    rw [Vec.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vec.toList_append]
    ac_rfl
  | concat r1 r2 ih1 ih2 =>
    simp only [extract]
    rw [Vec.cast_assoc]
    generalize_proofs h1 h2 h3
    rw [Vec.cast_assoc]
    generalize_proofs h4
    rw [Vec.toList_append]
    rw [Vec.cast_toList]
    rw [Vec.cast_toList]
    rw [ih2]
    rw [Vec.toList_append]
    rw [ih1]
    rw [Vec.toList_append]
    nth_rewrite 2 [ih2]
    rw [Vec.toList_append]
    ac_rfl
  | star r1 ih1 =>
    simp only [extract]
    rw [ih1]

theorem extract_take_toList (acc: Vec σ l):
  (Vec.toList
    (Vec.take
      (l + Symbol.num r1)
      (extract r2
      (extract r1 acc).2).2
    )
  )
  =
  (Vec.toList (extract r1 acc).2) := by
  rw [<- Vec.toList_take]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  rw [List.take_left']
  rw [Vec.toList_length]

theorem extract_take (acc: Vec σ l):
  (Vec.take
    (l + Symbol.num r1)
    (extract r2
      (extract r1 acc).2).2
  )
  =
    Vec.cast
    (extract r1 acc).2
    (by omega) := by
  apply Vec.eq
  rw [extract_take_toList]
  rw [<- Vec.cast_toList]

theorem extract_take_toList_fmap (acc: Vec σ l):
  (Vec.toList
    (Vec.take
      (l + Symbol.num r1)
      (Vec.map
        (extract r2
        (extract r1 acc).2).2
        f
      )
    )
  )
  =
  (Vec.toList
    (Vec.map
      (extract r1 acc).2
      f
    )
  ) := by
  rw [<- Vec.toList_take]
  rw [Vec.map_toList]
  rw [extract_append_toList]
  rw [Vec.toList_append]
  simp_all only [List.map_append, Vec.toList_map]
  rw [List.take_left']
  rw [<- Vec.map_toList]
  rw [Vec.toList_length]

theorem extract_take_fmap (acc: Vec α l) (f: α -> β):
  (Vec.take
    (l + Symbol.num r1)
    (Vec.map
      (extract r2
        (extract r1 acc).2).2
      f
    )
  )
  =
    Vec.cast
    (Vec.map
      (extract r1 acc).2
      f
    )
    (by omega) := by
  apply Vec.eq
  rw [extract_take_toList_fmap]
  rw [<- Vec.cast_toList]
