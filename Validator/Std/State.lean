import Lean.Elab.Tactic

@[always_inline, inline, expose]
def StateM.run {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : α × σ :=
  x s

@[always_inline, inline, expose]
def StateM.run' {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : α :=
  (x s).1

elab "simp_state" : tactic => do
  Lean.Elab.Tactic.evalTactic (←
  `(tactic| simp only [
    getThe,
    Bind.bind,
    Functor.map,
    MonadState.get,
    MonadState.set,
    MonadStateOf.get,
    MonadStateOf.set,
    Pure.pure,
    StateT.bind,
    StateT.get,
    StateT.map,
    StateT.pure,
    StateT.run,
    StateT.set,
    StateM.run] at *
  ))
