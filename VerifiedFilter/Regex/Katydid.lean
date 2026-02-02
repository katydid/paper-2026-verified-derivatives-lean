import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.Enter
import VerifiedFilter.Regex.Drawer
import VerifiedFilter.Regex.Lang
import VerifiedFilter.Regex.Leave
import VerifiedFilter.Regex.Num
import VerifiedFilter.Regex.Regex

-- Katydid, since we enter and leave
-- Also this a power in One Piece, which seems appropriate: https://onepiece.fandom.com/wiki/Ope_Ope_no_Mi
def Regex.Katydid.derive (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  enter r |> Vector.map Φ |> leave r

def Regex.Katydid.validate (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Bool :=
  null (List.foldl (fun dr x => Regex.Katydid.derive (flip Φ x) dr) r xs)

theorem Regex.Katydid.derive_is_Regex_derive (Φ: σ → α → Bool) (r: Regex σ) a:
  Regex.Katydid.derive (flip Φ a) r = Regex.derive Φ r a := by
  simp only [Katydid.derive, enter, leave, <- Vector.map_zip_is_zip_map, flip]
  rw [<- Regex.extract_replace_is_map]
  rw [Regex.Point.regex_derive_is_point_derive]

namespace Regex.Katydid

theorem derive_emptyset {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  Katydid.derive (flip Φ a) emptyset = emptyset := by
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  rw [Regex.derive_emptyset]

theorem derive_emptystr {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  Katydid.derive (flip Φ a) emptystr = emptyset := by
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  rw [Regex.derive_emptystr]

theorem derive_symbol {α: Type} {σ: Type} (Φ: σ → α → Bool) (s: σ) (a: α):
  Katydid.derive (flip Φ a) (symbol s) = onlyif (Φ s a) emptystr := by
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  rw [Regex.derive_symbol]

theorem derive_or {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  Katydid.derive (flip Φ a) (or r1 r2) = or (Katydid.derive (flip Φ a) r1) (Katydid.derive (flip Φ a) r2) := by
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  rw [Regex.derive_or]

theorem derive_concat {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  Katydid.derive (flip Φ a) (concat r1 r2)
    = or
      (concat (Katydid.derive (flip Φ a) r1) r2)
      (onlyif (null r1) (Katydid.derive (flip Φ a) r2)) := by
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  rw [Regex.derive_concat]

theorem derive_star {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1: Regex σ) (a: α):
  Katydid.derive (flip Φ a) (star r1) = concat (Katydid.derive (flip Φ a) r1) (star r1) := by
  repeat rw [Regex.Katydid.derive_is_Regex_derive]
  rw [Regex.derive_star]

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.denote (fun s a => Φ s a) (Katydid.derive (flip Φ a) r)
  = Lang.derive (Regex.denote (fun s a => Φ s a) r) a := by
  rw [Regex.Katydid.derive_is_Regex_derive]
  rw [<- Regex.derive_commutesb]

theorem derive_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (a: α):
  denote Φ (Katydid.derive (flip (decideRel Φ) a) r) = Lang.derive (denote Φ r) a := by
  rw [Regex.Katydid.derive_is_Regex_derive]
  rw [<- Regex.derive_commutes]
  congr

theorem derives_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  denote Φ ((List.foldl (fun dr x => Regex.Katydid.derive (flip (decideRel Φ) x) dr)) r xs) = Lang.derives (denote Φ r) xs := by
  rw [Lang.derives_foldl]
  induction xs generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes Φ r x
    have ih' := ih (derive (flip (decideRel Φ) x) r)
    rw [h] at ih'
    exact ih'

theorem validate_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  (Katydid.validate (decideRel Φ) r xs = true) = (denote Φ r) xs := by
  rw [<- Lang.validate (denote Φ r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

def filter (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): List (List α) :=
  List.filter (Katydid.validate Φ r) xss

theorem mem_filter (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xss: List (List α)) :
  ∀ xs, (xs ∈ Katydid.filter (decideRel Φ) r xss) ↔ (Lang.MemFilter (denote Φ r) xss xs) := by
  unfold filter
  intro xs
  rw [List.mem_filter]
  unfold Lang.MemFilter
  apply Iff.intro
  case mp =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [<- validate_commutes]
    assumption
  case mpr =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [validate_commutes]
    assumption
