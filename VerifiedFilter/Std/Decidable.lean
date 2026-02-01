-- A Decidable library that suppliments Lean's standard Decidable definitions.

def decideRel (p : α → β → Prop) [DecidableRel p]: α → β → Bool :=
  fun a b => decide (p a b)
