import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.RewriteSearch

namespace List

theorem list_elem_lt [SizeOf α] {xs: List α} (h: x ∈ xs): sizeOf x ≤ sizeOf xs := by
  rw [show (x ∈ xs) = List.Mem x xs from rfl] at h
  induction h with
  | head xs' =>
    simp +arith
  | tail _ _ ih =>
    apply Nat.le_trans ih
    simp +arith

theorem list_sizeOf_cons [SizeOf α] (xs ys: List α):
  sizeOf xs < sizeOf (y::ys ++ xs) := by
  induction ys with
  | nil =>
    simp +arith only [List.cons_append, List.cons.sizeOf_spec]
    simp only [List.nil_append, Nat.le_add_left]
  | cons y ys ih =>
    simp only [List.cons_append] at *
    simp only [List.cons.sizeOf_spec] at *
    omega

theorem list_sizeOf_cons_lt_cons [SizeOf α] (x: α) {ys xs: List α} (h_lt: sizeOf ys < sizeOf xs):
  sizeOf (x :: ys) < sizeOf (x :: xs) := by
  simp only [cons.sizeOf_spec, Nat.add_lt_add_iff_left]
  exact h_lt

theorem list_sizeOf_lt_cons_eq [SizeOf α] (x: α) {ys xs: List α} (h_eq: ys = xs):
  sizeOf ys < sizeOf (x :: xs) := by
  rw [h_eq]
  simp [cons.sizeOf_spec]
  exact Nat.pos_of_neZero (1 + sizeOf x)

theorem list_sizeOf_lt_cons_lt [SizeOf α] (x: α) {ys xs: List α} (h_lt: sizeOf ys < sizeOf xs):
  sizeOf ys < sizeOf (x :: xs) := by
  simp [cons.sizeOf_spec]
  exact Nat.lt_add_left (1 + sizeOf x) h_lt

theorem list_length_drop_lt_cons {n: Nat} {xs: List α}:
  (List.drop n xs).length < (x :: xs).length := by
  simp only [length_drop, length_cons]
  omega

theorem list_drop_exists (n: Nat) (xs: List α): ∃ ys, xs = ys ++ (List.drop n xs) := by
  cases n with
  | zero =>
    rw [drop_zero]
    exists []
  | succ n' =>
    cases xs with
    | nil =>
      rewrite [drop_nil]
      exists []
    | cons x xs =>
      simp only [List.drop_succ_cons]
      exists (x::List.take n' xs)
      simp only [cons_append]
      congr
      simp only [take_append_drop]


-- interleaves

def interleaves (xs: List α) (acc: List (List α × List α) := [([], [])])
  : List (List α × List α) := match xs with
  | [] => acc
  | (x::xs) => (interleaves xs acc).map (fun res => (x::res.1, res.2))
            ++ (interleaves xs acc).map (fun res => (res.1, x::res.2))

#guard (interleaves [1,2,3,4]).contains ([1,3],[2,4])
#guard (interleaves [1,2,3,4]).contains ([3],[1,2,4])
#guard (interleaves [1,2,3,4]).contains ([3],[1,2,4])

def interleavesAcc_length (xs: List α) (acc: List (List α × List α)): Nat :=
  acc.length * (2 ^ xs.length)

theorem interleavesAcc_length_is_correct (xs: List α) (acc: List (List α × List α)):
  (interleaves xs acc).length = interleavesAcc_length xs acc := by
  unfold interleavesAcc_length
  induction xs with
  | nil =>
    simp [interleaves]
  | cons x xs ih =>
    simp [interleaves]
    rw [ih]
    simp +arith
    rw [Nat.mul_left_comm]
    rw [Nat.pow_add']

def interleaves_length (xs: List α): Nat := 2 ^ xs.length

theorem interleaves_length_is_correct (xs: List α):
  (interleaves xs).length = interleaves_length xs := by
  unfold interleaves_length
  rw [interleavesAcc_length_is_correct]
  unfold interleavesAcc_length
  simp

theorem interleaves_mem_swap (xs: List α) :
  p ∈ interleaves xs → (p.2, p.1) ∈ interleaves xs := by
  induction xs generalizing p with
  | nil =>
    intro hp
    simp [interleaves, interleaves] at *
    subst hp
    simp only [and_self]
  | cons x xs ih =>
    intro hp
    simp [interleaves, interleaves, List.mem_append] at hp
    rcases hp with hp | hp
    · rcases hp with ⟨a, b, hab, heq⟩
      simp [interleaves, interleaves, List.mem_append]
      right
      exists b
      exists a
      and_intros
      · exact ih hab
      · rw [←heq]
      · rw [←heq]
    · rcases hp with ⟨a, b, hab, heq⟩
      simp [interleaves, interleaves, List.mem_append]
      left
      exists b
      and_intros
      · rw [←heq]
        exact ih hab
      · rw [←heq]

theorem interleaves1_length_is_le (xs: List α):
  ∀ ys ∈ (List.map (·.1) (interleaves xs)),
    ys.length <= length xs
  := by
  intro ys hys
  induction xs generalizing ys with
    | nil =>
      simp [interleaves, interleaves] at hys
      rw [hys]
      simp
    | cons x xs ih =>
      simp [interleaves, interleaves, List.map_append] at hys
      simp [List.mem_map] at ih
      rcases hys with hys | hys
      · rcases hys with ⟨fst, ⟨snd, hpair⟩, hys⟩
        have hlen := ih fst snd hpair
        rw [←hys]
        simp only [length_cons, Nat.add_le_add_iff_right]
        assumption
      · rcases hys with ⟨snd, hpair⟩
        have hlen := ih ys snd hpair
        rw [length_cons]
        exact Nat.le_succ_of_le hlen

theorem interleaves_contains_itself_fst (xs: List α):
  ∃ p ∈ interleaves xs, p.1 = xs := by
  induction xs with
  | nil =>
    simp only [interleaves, interleaves, mem_cons, not_mem_nil, or_false, exists_eq_left]
  | cons x xs ih =>
    rcases ih with ⟨p, hp_mem, p_fst_eq_xs⟩
    exists (x :: p.1, p.2)
    constructor
    · simp [interleaves, interleaves, List.mem_append, List.mem_map]
      apply Or.inl
      apply hp_mem
    · simp only [cons.injEq, true_and]
      assumption

theorem interleaves_contains_itself_fst_idx (xs: List α):
  ∃ i, ((List.interleaves xs).get i).1 = xs := by
  have hmem := interleaves_contains_itself_fst xs
  rcases hmem with ⟨p, hp_mem, hp_eq⟩
  rcases (mem_iff_get).1 hp_mem with ⟨i, hi⟩
  exists i
  rw [hi]
  exact hp_eq

theorem interleaves_sizeOf1 (xs: List α) [SizeOf α]:
  ∀ p ∈ interleaves xs, p.1 = xs \/ sizeOf p.1 < sizeOf xs := by
  induction xs with
  | nil =>
    intro p hp
    simp [interleaves, interleaves] at hp
    left
    rw [hp]
  | cons x xs ih =>
    intro p hp
    simp [interleaves, interleaves] at hp
    rcases hp with hp | hp
    · rcases hp with ⟨fst, snd, hp_mem, hp_eq⟩
      obtain h_eq | h_lt := ih (fst, snd) hp_mem
      · left
        rw [←hp_eq]
        exact congrArg (List.cons x) h_eq
      · right
        rw [←hp_eq]
        exact list_sizeOf_cons_lt_cons x h_lt
    · rcases hp with ⟨fst, snd, hp_mem, hp_eq⟩
      obtain h_eq | h_lt := ih (fst, snd) hp_mem
      · right
        rw [←hp_eq]
        exact list_sizeOf_lt_cons_eq x h_eq
      · right
        rw [←hp_eq]
        exact list_sizeOf_lt_cons_lt x h_lt

theorem interleaves_sizeOf1_idx (xs: List α) [SizeOf α] (i: Fin (List.interleaves xs).length):
  ((List.interleaves xs).get i).1 = xs \/ sizeOf ((List.interleaves xs).get i).1 < sizeOf xs := by
  exact interleaves_sizeOf1 xs ((interleaves xs).get i) (get_mem _ _)

theorem interleaves_sizeOf2 [SizeOf α] (xs: List α):
  ∀ p ∈ interleaves xs, p.2 = xs \/ sizeOf p.2 < sizeOf xs := by
  induction xs with
  | nil =>
    intro p hp
    simp [interleaves, interleaves] at hp
    left
    rw [hp]
  | cons x xs ih =>
    intro p hp
    simp [interleaves, interleaves] at hp
    rcases hp with hp | hp
    · rcases hp with ⟨fst, snd, hp_mem, hp_eq⟩
      obtain h_eq | h_lt := ih (fst, snd) hp_mem
      · right
        rw [←hp_eq]
        exact list_sizeOf_lt_cons_eq x h_eq
      · right
        rw [←hp_eq]
        exact list_sizeOf_lt_cons_lt x h_lt
    · rcases hp with ⟨fst, snd, hp_mem, hp_eq⟩
      obtain h_eq | h_lt := ih (fst, snd) hp_mem
      · left
        rw [←hp_eq]
        exact congrArg (List.cons x) h_eq
      · right
        rw [←hp_eq]
        exact list_sizeOf_cons_lt_cons x h_lt

theorem interleaves_sizeOf2_idx [SizeOf α] (xs: List α) (i: Fin (List.interleaves xs).length):
  ((List.interleaves xs).get i).2 = xs \/ sizeOf ((List.interleaves xs).get i).2 < sizeOf xs := by
  exact interleaves_sizeOf2 xs ((interleaves xs).get i) (get_mem _ _)
