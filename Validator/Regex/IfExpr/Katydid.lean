import Validator.Std.Vec

import Validator.Regex.Drawer
import Validator.Regex.Lang
import Validator.Regex.Leave
import Validator.Regex.Num
import Validator.Regex.Regex
import Validator.Regex.Katydid

import Validator.Regex.IfExpr.Enter
import Validator.Regex.IfExpr.IfExpr

namespace Regex.IfExpr

-- Katydid, since we enter and leave
-- Also this a power in One Piece, which seems appropriate: https://onepiece.fandom.com/wiki/Ope_Ope_no_Mi
def Regex.IfExpr.derive (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  enter r |> IfExpr.eval Φ |> leave r

def Regex.IfExpr.validate (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Bool :=
  null (List.foldl (fun dr x => Regex.IfExpr.derive (flip Φ x) dr) r xs)

lemma Regex.Katydid.derive_is_Regex.Katydid.derive (Φ: σ → Bool) (r: Regex σ):
  Regex.IfExpr.derive Φ r = Regex.Katydid.derive Φ r := by
  unfold Regex.IfExpr.derive
  unfold Regex.Katydid.derive
  unfold Regex.IfExpr.enter
  unfold Regex.enter
  rw [IfExpr.eval_is_map]

lemma Regex.IfExpr.derive_is_Regex_derive (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.IfExpr.derive (flip Φ a) r = Regex.derive Φ r a := by
  simp only [Regex.IfExpr.derive, enter, leave, <- Vector.map_zip_is_zip_map, flip, IfExpr.eval_is_map]
  rw [<- Regex.extract_replace_is_map]
  rw [Regex.Point.regex_derive_is_point_derive]

theorem derive_emptyset {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  Regex.IfExpr.derive (flip Φ a) emptyset = emptyset := by
  repeat rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [Regex.derive_emptyset]

theorem derive_emptystr {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  Regex.IfExpr.derive (flip Φ a) emptystr = emptyset := by
  repeat rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [Regex.derive_emptystr]

theorem derive_symbol {α: Type} {σ: Type} (Φ: σ → α → Bool) (s: σ) (a: α):
  Regex.IfExpr.derive (flip Φ a) (symbol s) = onlyif (Φ s a) emptystr := by
  repeat rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [Regex.derive_symbol]

theorem derive_or {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  Regex.IfExpr.derive (flip Φ a) (or r1 r2) = or (Regex.IfExpr.derive (flip Φ a) r1) (Regex.IfExpr.derive (flip Φ a) r2) := by
  repeat rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [Regex.derive_or]

theorem derive_concat {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  Regex.IfExpr.derive (flip Φ a) (concat r1 r2)
    = or
      (concat (Regex.IfExpr.derive (flip Φ a) r1) r2)
      (onlyif (null r1) (Regex.IfExpr.derive (flip Φ a) r2)) := by
  repeat rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [Regex.derive_concat]

theorem derive_star {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1: Regex σ) (a: α):
  Regex.IfExpr.derive (flip Φ a) (star r1) = concat (Regex.IfExpr.derive (flip Φ a) r1) (star r1) := by
  repeat rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [Regex.derive_star]

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.denote (fun s a => Φ s a) (Regex.IfExpr.derive (flip Φ a) r)
  = Lang.derive (Regex.denote (fun s a => Φ s a) r) a := by
  rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [<- Regex.derive_commutesb]

theorem derive_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (a: α):
  denote Φ (Regex.IfExpr.derive (flip (decideRel Φ) a) r) = Lang.derive (denote Φ r) a := by
  rw [Regex.IfExpr.derive_is_Regex_derive]
  rw [<- Regex.derive_commutes]
  congr

theorem derives_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  denote Φ ((List.foldl (fun dr x => Regex.IfExpr.derive (flip (decideRel Φ) x) dr)) r xs) = Lang.derives (denote Φ r) xs := by
  rw [Lang.derives_foldl]
  induction xs generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes Φ r x
    have ih' := ih (Regex.IfExpr.derive (flip (decideRel Φ) x) r)
    rw [h] at ih'
    exact ih'

theorem validate_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  (Regex.IfExpr.validate (decideRel Φ) r xs = true) = (denote Φ r) xs := by
  rw [<- Lang.validate (denote Φ r) xs]
  unfold Regex.IfExpr.validate
  rw [<- derives_commutes]
  rw [<- null_commutes]
