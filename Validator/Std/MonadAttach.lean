-- Copied from https://github.com/leanprover/lean4/blob/13c88f960f40b7c163b99e742010bbbbdbe8bba7/src/Init/Control/MonadAttach.lean#L30
-- TODO: Delete this when updating to new lean version.

set_option linter.missingDocs false in
public class MonadAttach (m : Type u → Type v) where
  /--
  A predicate that can be assumed to be true for all return values {name}`a` of actions {name}`x`
  in {name}`m`, in all situations.
  -/
  CanReturn {α : Type u} : (x : m α) → (a : α) → Prop
  /--
  Attaches a proof of {name}`MonadAttach.CanReturn` to the return value of {name}`x`. This proof
  can be used to prove the termination of well-founded recursive functions.
  -/
  attach {α : Type u} (x : m α) : m (Subtype (CanReturn x))

-- verso docstring is added below
set_option linter.missingDocs false in
public class WeaklyLawfulMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m] where
  map_attach {α : Type u} {x : m α} : Subtype.val <$> MonadAttach.attach x = x

/--
This type class ensures that {name}`MonadAttach.CanReturn` is the unique strongest possible
postcondition.
-/
public class LawfulMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m] extends
    WeaklyLawfulMonadAttach m where
  canReturn_map_imp {α : Type u} {P : α → Prop} {x : m (Subtype P)} {a : α} :
      MonadAttach.CanReturn (Subtype.val <$> x) a → P a

/--
Like {name}`Bind.bind`, {name}`pbind` sequences two computations {lean}`x : m α` and {lean}`f`,
allowing the second to depend on the value computed by the first.
But other than with {name}`Bind.bind`, the second computation can also depend on a proof that
the return value {given}`a` of {name}`x` satisfies {lean}`MonadAttach.CanReturn x a`.
-/
public def MonadAttach.pbind [Monad m] [MonadAttach m]
    (x : m α) (f : (a : α) → MonadAttach.CanReturn x a → m β) : m β :=
  MonadAttach.attach x >>= (fun ⟨a, ha⟩ => f a ha)

/--
A {lean}`MonadAttach` instance where all return values are possible and {name}`attach` adds no
information to the return value, except a trivial proof of {name}`True`.

This instance is used whenever no more useful {name}`MonadAttach` instance can be implemented.
It always has a {name}`WeaklyLawfulMonadAttach`, but usually no {name}`LawfulMonadAttach` instance.
-/
@[expose]
public protected def MonadAttach.trivial {m : Type u → Type v} [Monad m] : MonadAttach m where
  CanReturn _ _ := True
  attach x := (⟨·, .intro⟩) <$> x


public theorem LawfulMonadAttach.canReturn_bind_imp' [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    {x : m α} {f : α → m β} :
    MonadAttach.CanReturn (x >>= f) b → Exists fun a => MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b := by
  intro h
  let P (b : β) := Exists fun a => MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b
  have h' : (x >>= f) = Subtype.val <$> (MonadAttach.attach x >>= (fun a => (do
      let b ← MonadAttach.attach (f a)
      return ⟨b.1, a.1, a.2, b.2⟩ : m (Subtype P)))) := by
    simp only [map_bind, map_pure]
    simp only [bind_pure_comp, WeaklyLawfulMonadAttach.map_attach]
    rw (occs := [1]) [← WeaklyLawfulMonadAttach.map_attach (x := x)]
    simp
  rw [h'] at h
  have := LawfulMonadAttach.canReturn_map_imp h
  exact this

public theorem LawfulMonadAttach.eq_of_canReturn_pure [Monad m] [MonadAttach m]
    [LawfulMonad m] [LawfulMonadAttach m] {a b : α}
    (h : MonadAttach.CanReturn (m := m) (pure a) b) :
    a = b := by
  let x : m (Subtype (a = ·)) := pure ⟨a, rfl⟩
  have : pure a = Subtype.val <$> x := by simp [x]
  rw [this] at h
  exact LawfulMonadAttach.canReturn_map_imp h

public theorem LawfulMonadAttach.canReturn_map_imp' [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    {x : m α} {f : α → β} :
    MonadAttach.CanReturn (f <$> x) b → Exists fun a => MonadAttach.CanReturn x a ∧ f a = b := by
  rw [map_eq_pure_bind]
  intro h
  obtain ⟨a, h, h'⟩ := canReturn_bind_imp' h
  exact ⟨a, h, eq_of_canReturn_pure h'⟩

public theorem LawfulMonadAttach.canReturn_liftM_imp'
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [LawfulMonadAttach n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {x : m α} {a : α} :
    MonadAttach.CanReturn (liftM (n := n) x) a → MonadAttach.CanReturn x a := by
  intro h
  simp only [← WeaklyLawfulMonadAttach.map_attach (x := x), liftM_map] at h
  exact canReturn_map_imp h

public theorem WeaklyLawfulMonadAttach.attach_bind_val
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    {x : m α} {f : α → m β} :
    MonadAttach.attach x >>= (fun a => f a.val) = x >>= f := by
  conv => rhs; simp only [← map_attach (x := x), bind_map_left]

public theorem WeaklyLawfulMonadAttach.bind_attach_of_nonempty
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [Nonempty (m β)]
    {x : m α} {f : Subtype (MonadAttach.CanReturn x) → m β} :
    open scoped Classical in
    MonadAttach.attach x >>= f = x >>= (fun a => if ha : MonadAttach.CanReturn x a then f ⟨a, ha⟩ else Classical.ofNonempty) := by
  conv => rhs; simp +singlePass only [← map_attach (x := x)]
  simp [Subtype.property]

public theorem MonadAttach.attach_bind_eq_pbind
    [Monad m] [MonadAttach m]
    {x : m α} {f : Subtype (MonadAttach.CanReturn x) → m β} :
    MonadAttach.attach x >>= f = MonadAttach.pbind x (fun a ha => f ⟨a, ha⟩) := by
  simp [MonadAttach.pbind]

public theorem WeaklyLawfulMonadAttach.pbind_eq_bind
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    {x : m α} {f : α → m β} :
    MonadAttach.pbind x (fun a _ => f a) = x >>= f := by
  conv => rhs; rw [← map_attach (x := x)]
  simp [MonadAttach.pbind]

public theorem WeaklyLawfulMonadAttach.pbind_eq_bind'
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    {x : m α} {f : α → m β} :
    MonadAttach.pbind x (fun a _ => f a) = x >>= f := by
  conv => rhs; rw [← map_attach (x := x)]
  simp [MonadAttach.pbind]

instance : MonadAttach Id where
  CanReturn x a := x.run = a
  attach x := pure ⟨x.run, rfl⟩

instance : LawfulMonadAttach Id where
  map_attach := rfl
  canReturn_map_imp := by
    intro _ _ x _ h
    cases h
    exact x.run.2

instance inst1 [Monad m] [MonadAttach m] : MonadAttach (StateT σ m) where
  CanReturn x a := Exists fun s => Exists fun s' => MonadAttach.CanReturn (x.run s) (a, s')
  attach x := fun s => (fun ⟨⟨a, s'⟩, h⟩ => ⟨⟨a, s, s', h⟩, s'⟩) <$> MonadAttach.attach (x.run s)

instance inst2 [Monad m] [MonadAttach m] : MonadAttach (StateT σ m) where
  CanReturn x a := Exists fun s => Exists fun s' => MonadAttach.CanReturn (x.run s) (a, s')
  attach x := fun s => (fun ⟨⟨a, s'⟩, h⟩ => (Subtype.mk a (Exists.intro s (Exists.intro s' h)), s')) <$> MonadAttach.attach (x.run s)

instance instForAll : MonadAttach (StateM σ) where
  -- CanReturn {α : Type u} : (x : m α) → (a : α) → Prop
  CanReturn x a := ∀ s, (x.run s).1 = a
  -- attach {α : Type u} (x : m α) : m (Subtype (CanReturn x))
  attach x := fun s => by
    refine pure (Subtype.mk (x.run s).1 rfl)
    sorry
  -- attach x := fun s => (fun ⟨⟨a, s'⟩, h⟩ => (Subtype.mk a (fun s s' => h), s')) <$> MonadAttach.attach (x.run s)

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] :
    WeaklyLawfulMonadAttach (StateT σ m) where
  map_attach := by
    intro α x
    simp only [Functor.map, StateT, funext_iff, StateT.map, bind_pure_comp, MonadAttach.attach,
      Functor.map_map]
    exact fun s => WeaklyLawfulMonadAttach.map_attach

public instance [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m] :
    LawfulMonadAttach (StateT σ m) where
  canReturn_map_imp := by
    simp only [Functor.map, MonadAttach.CanReturn, StateT.run, StateT.map, bind_pure_comp]
    rintro _ _ x a ⟨s, s', h⟩
    obtain ⟨a, h, h'⟩ := LawfulMonadAttach.canReturn_map_imp' h
    cases h'
    exact a.1.2
