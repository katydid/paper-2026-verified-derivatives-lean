-- A State library that suppliments Lean's standard State type with definitions.

@[always_inline, inline, expose]
def StateM.run {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : α × σ :=
  x s

@[always_inline, inline, expose]
def StateM.run' {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : α :=
  (x s).1
