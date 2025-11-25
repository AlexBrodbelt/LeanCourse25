import Mathlib.Analysis.Complex.Exponential

import Mathlib
open Real Function Set

/-

* An advertisement: for a current event by the *Fachschaft* you may find interesting:

**Equity in math-an event for men**
The event will take place on 17 November from 16:00 to 18:00 in the Lipschitzsaal.
The Gleichstellungsreferat of the Fachschaft Mathematik warmly invites you to this event,
where we will discuss male perspectives on gender equality.
The program will include a talk on the topic, a panel discussion with professors and students, and
the opportunity to chat over drinks and enjoy free cookies afterwards.
You can find more information on our website at fsmath.uni-bonn.de.
Of course, everyone is welcome to join — we look forward to seeing you there 🙂


* Hand in the solutions to the exercises below. Deadline: **Thursday**, 20.11.2025 at 10.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

-- Remember the definition Point from last week's assignment: let's parametrise this by a type.
@[ext]
structure Point (α : Type*) where
  x : α
  y : α
  z : α

-- Let's connect this to ℝ³. Here is to define a point in a triple:
-- you can use matching, just like you would for an inductive type.
example {x y z : ℝ} : Fin 3 → ℝ := fun
  | 0 => x
  | 1 => y
  | 2 => z

-- Define an equivalence from Fin 2 × Fin 3 to Fin 6.
example : Fin 3 × Fin 2 ≃ Fin 6 := sorry

-- Now prove that Point α and α³ are equivalent.
-- In particular, `Point` from last week and `ℝ³` are equivalent.
example {α : Type*} : (Fin 3 → α) ≃ Point α where
  toFun := fun f ↦ ⟨f 0, f 2, f 1⟩
  invFun P := fun
    | 0 => P.x
    | 1 => P.z
    | 2 => P.y
  left_inv := by sorry
  right_inv := by sorry

section

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by
  sorry
  done

end

section

-- In the lecture, we also saw injectivity and bijectivity of functions.
-- There is another variant, "bijectivity on a set":
def BijectiveOn {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (f '' s ⊆ t) ∧ InjOn f s ∧ SurjOn f s t

-- There is a curious fact about infinite types: they are bijective to a proper subset.
-- Let us explore this theme in the following exercises.

example : ∃ f : ℕ → ℕ, BijectiveOn f univ (univ \ {0}) := by
  use fun n => n + 1
  refine ⟨?WellDefined, ?Injective, ?Surjective⟩
  · intro x hx
    simp only [image_univ, mem_range, Nat.exists_add_one_eq] at hx
    simp only [mem_diff, mem_univ, mem_singleton_iff, true_and]
    linarith
  · intro x hx y hy  hxy
    simpa using hxy
  · intro y hy
    use y - 1
    constructor
    · simp
    · simp only [mem_diff, mem_univ, mem_singleton_iff, true_and] at hy
      simp [Nat.sub_add_cancel (show 1 ≤ y by omega)]

example {α : Type*} [Infinite α] {a : α} : ∃ f : α → α, BijectiveOn f (univ \ {a}) univ := by
  -- Hint: a useful first step is "there exists an injective map ℕ → α".
  -- Use loogle or exact? to find this.
  sorry

-- In particular, an infinite type is bijective to a proper subtype.
-- If you like a little *challenge*, prove the converse.
-- This is a bit harder; you want to write down a careful mathematical proof first
-- and use loogle to re-use existing results from mathlib.
example {α : Type*} {s : Set α} (hs : s ≠ univ) {f : α → α} (hf : BijectiveOn f s univ) :
    Infinite α := by
  sorry

end



/-! # Exercises to hand-in. -/

-- There are only two exercises to hand in this week. In the remaining time, work on your first
-- project about formal conjectures.

section choice

/-- This exercise is about a subtle detail regarding the axiom of choice: while you know there
is a global choice function, it is not given by one "computation rule".
The following exercise makes this precise: prove it.

Remember that Lean has proof irrelevance: any two proofs of a given proposition are equal.
-/
example (choiceFunction : ∀ (α : Type) (p : α → Prop) (_h : ∃ x, p x), α)
    (h : ∀ (α : Type) (p : α → Prop) (x : α) (hx : p x), choiceFunction α p ⟨x, hx⟩ = x) :
    False := by
  have contr := h ℕ (fun n => True) 0 (by trivial) ▸ h ℕ (fun n => True) 1 (by trivial)
  contradiction
  

end choice

section cardinality

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] Finset.card_powerset
#check Finset.induction

lemma finset_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (Finset.powerset s) = 2 ^ Finset.card s := by
  let decidable_α : DecidableEq α := by exact Classical.typeDecidableEq α
  induction s using Finset.induction with
  | empty => simp only [Finset.powerset_empty, Finset.card_singleton, Finset.card_empty, pow_zero]
  | insert a s a_notMem_s hs =>
    rw [Finset.card_insert_of_notMem a_notMem_s,
    Finset.powerset_insert, Finset.card_union_of_disjoint ?Disjoint]
    rotate_left
    · rw [Finset.disjoint_iff_ne]
      rintro x hx y hy
      simp only [Finset.mem_powerset, Finset.mem_image] at hx hy
      obtain ⟨y', y_subset_s, hy⟩ := hy
      have a_notMem_x : a ∉ x := by exact fun a_1 ↦ a_notMem_s (hx a_1)
      have a_mem_y : a ∈ y := by rw [← hy]; exact Finset.mem_insert_self a y'
      symm
      apply ne_of_not_le
      rw [Finset.le_iff_subset, Finset.not_subset]
      use a
    · suffices (Finset.image (insert a) s.powerset).card = s.powerset.card by
        simp only [hs, this]
        ring
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      simp only [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset] at hx hy
      have a_notMem_x : a ∉ x := by exact fun a_1 ↦ a_notMem_s (hx a_1)
      have a_notMem_y : a ∉ y := by exact fun a_1 ↦ a_notMem_s (hy a_1)
      rw [← Finset.union_singleton, ← Finset.union_singleton, Finset.union_eq_union_iff_right,
        Finset.union_singleton, Finset.union_singleton, Finset.subset_insert_iff,
        Finset.subset_insert_iff, Finset.erase_eq_of_notMem a_notMem_x,
        Finset.erase_eq_of_notMem a_notMem_y] at hxy
      exact le_antisymm hxy.1 hxy.2
  done

end cardinality
