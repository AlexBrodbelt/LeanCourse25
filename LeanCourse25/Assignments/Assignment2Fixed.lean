import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Finite.Basic

open Real Function Set Nat

/-

* Hand in the solutions to the exercises below. Deadline: 30.10.2025 at 10:00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (p q r s : Prop) (h : p ∧ q → r) (hp : p) (h' : q → s) : q → r ∧ s := by
  intro hq
  constructor
  ·
    apply h
    constructor
    ·
      assumption
    ·
      assumption
  ·
    apply h'
    assumption
  done


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by
  rintro ⟨x, hpx⟩
  use x
  exact h x hpx
  done

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  contrapose!
  intro h
  exfalso
  apply @OfNat.one_ne_ofNat ℕ _ _ (2 : ℕ)
  exact h
  done

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by
  constructor
  ·
    intro h x hpx
    exact h ⟨x, hpx⟩
  ·
    intro h ⟨x, hpx⟩
    exact h x hpx
  done

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
  constructor
  ·
    intro ⟨x, hpx, hr⟩
    exact ⟨⟨x, hpx⟩, hr⟩
  ·
    intro ⟨⟨x, hpx⟩, hr⟩
    exact ⟨x, hpx, hr⟩
  done

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by
  constructor
  ·
    intro ⟨x, hpx⟩ hpx'
    specialize hpx' x
    tauto
  ·
    intro h
    by_contra h'
    apply h
    intro x
    tauto
  done

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun _n : ℕ ↦ a) a := by
  unfold SequentialLimit
  intro ε ε_pos
  use 0
  intro n _
  rwa [sub_self, abs_zero]
  done

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  calc
  (n)! ∣ (m)! := by
    exact factorial_dvd_factorial h
  _ ∣ (m + 1)! := by
    exact Dvd.intro_left m.succ rfl
    done

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by
  apply _root_.add_le_add
  ·
    trans b
    ·
      exact h
    ·
      exact le_of_lt h2
  ·
    rw [exp_le_exp, ← add_zero x]
    apply _root_.add_le_add
    ·
      exact h3
    ·
      norm_num
  done

-- Use `rw?` or `rw??` to help you in the following calculation.
-- Alternatively, write out a calc block by hand.
example {G : Type*} [Group G] {a b c d : G}
    (h : a⁻¹ * b * c * c⁻¹ * a * b⁻¹ * a * a⁻¹ = b) (h' : b * c = c * b) : b = 1 := by
  rw [mul_assoc, mul_inv_cancel, mul_one, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc c,
    mul_inv_cancel, one_mul] at h
  nth_rewrite 2 [← inv_inv a] at h
  rw [← mul_inv_rev] at h
  sorry

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  constructor <;> intro h <;> linarith
  done


/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
  -- nlinarith
  rw [sub_le_iff_le_add, add_assoc]
  calc
  n ≤ n + (0 + 0) := by linarith
  _ ≤ n + (3 + m^2) := by gcongr; norm_num; apply sq_nonneg


example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  linarith [h 2]
  done



/-! # Exercises to hand-in. -/

section Logic
-- Prove the following statements with basic tactics,
-- in particular without using `tauto`, `grind` or lemmas from mathlib.

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ) := ∀ x, ContinuousAtPoint f x

-- Exercise for you. Remember that you can use `unfold` to expand a definition.
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
  unfold Continuous'
  constructor
  · intro h x
    rw [← hfg]
    exact h x
  · intro h x
    rw [hfg]
    exact h x
  done

def All (p : ℝ → Prop) := ∀ x, p x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    All p ↔ All q := by
  unfold All
  simp_rw [h]

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    (∃ x, p x) ↔ (∃ x, q x) := by
  simp_rw [h]

-- Is the following true? If yes, prove it in Lean.
-- If not, give a counterexample and prove it. (What do you have to do to do so?)
example (p q : ℕ → Prop) (h : (∃ x, p x) ↔ (∃ x, q x)) : ∀ x, p x ↔ q x := by
  sorry

-- We show a counterexample to the exercise above
example : ∃ (p q : ℕ → Prop), ((∃ x, p x) ↔ (∃ x, q x)) ∧ (¬ ∀ x, p x ↔ q x) := by
  set p : ℕ → Prop := fun n => 1 ≤ n with hp
  set q : ℕ → Prop := fun n => 2 ≤ n with hq
  use p, q
  constructor
  ·
    constructor <;>
    intro h <;>
    use 2; linarith
  ·
    push_neg
    use 1
    left
    tauto

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  ·
    rintro ⟨x, (hpx | hqx)⟩
    ·
      left
      use x
    ·
      right
      use x
  ·
    rintro (⟨x, hpx⟩ | ⟨x, hqx⟩)
    ·
      use x
      left
      assumption
    ·
      use x
      right
      assumption
  done

end Logic

section Functions

-- Let us investigate the function example from the lecture further.

-- This is how to say "a natural number p is prime" in mathlib.
#check Nat.Prime

-- The following theorem is the key ingredient to it.
-- (You have not seen the syntax `[hp: Fact (Nat.Prime p)]` yet: this is related to implicit arguments.
--  You can assume it says `(hp: Nat.Prime p)`. We will discuss the precise difference later.)
--
-- Use `exact?`, `apply?` or `rw??` to find this theorem in mathlib.
-- Describe what you are doing.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x := by
  exact ZMod.pow_card x
  done

-- The above theorem has a name. What is it?
-- Use this name to find the same result using leansearch.net.
-- Describe every step you're performing.

-- Use `rw??` to find the following theorem in mathlib.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (k : ZMod p) (hk : k ≠ 0) : k ^ (p - 1) = 1 := by
  rw [ZMod.pow_card_sub_one_eq_one hk]
  done

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] :
    (fun k ↦ k ^ p + 2 * k ^ (2 * (p - 1) + 1) : ZMod p → ZMod p) = (fun k ↦ 3 * k) := by
  funext x
  by_cases hx : x = 0
  ·
    simp [hx]
  · rw [ZMod.pow_card, pow_add, pow_one, mul_comm 2, pow_mul', ZMod.pow_card_sub_one_eq_one hx]
    ring
  done

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (3 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  ·
    simp [hk]
  ·
    rw [pow_add, pow_one, pow_mul', ZMod.pow_card_sub_one_eq_one hk]
    ring
  done

example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (5 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  ·
    simp [hk]
  ·
    rw [pow_add, pow_one, pow_mul', ZMod.pow_card_sub_one_eq_one hk]
    ring
  done

end Functions


/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  obtain ⟨N, hN⟩ := hs (ε / 2) (half_pos εpos)
  obtain ⟨M, hM⟩ := ht (ε / 2) (half_pos εpos)
  use max M N
  intro n hn
  simp only
  calc
  |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
  _ ≤ |(s n - a)| + |(t n - b)| := abs_add_le (s n - a) (t n - b)
  _ < ε / 2 + ε / 2 := by
    gcongr
    ·
      refine hN n ?_
      trans max M N
      ·
        exact hn
      ·
        exact Nat.le_max_right M N

    ·
      refine hM n ?_
      trans max M N
      ·
        exact hn
      ·
        exact Nat.le_max_left M N
    -- grw [hM n (by sorry), hN n (by sorry)] should of worked, potentially a bug
  _ = ε := by ring

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε εpos
  by_cases hc : c = 0
  · simp only [ge_iff_le, hc, zero_mul, sub_self, abs_zero]
    tauto
  obtain ⟨N, hN⟩ := hs (ε / |c|) (by refine _root_.div_pos εpos (abs_pos.2 hc))
  use N
  intro n hn
  simp
  rw [← mul_sub, abs_mul]
  calc
  |c| * |s n - a| < |c| * (ε / |c|) :=
    mul_lt_mul' (le_refl _) (hN n hn) (abs_nonneg _) (abs_pos.2 hc)
  _ = ε := by field_simp [hc]



/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by
  have n_le_two : n ≤ 2 := by nlinarith
  nlinarith
  done


section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp

example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intro n hn
  simp only
  apply mul_le_mul_right'
  exact hn
  done

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro k
  obtain ⟨N, hN⟩ := h₁ k
  obtain ⟨M, hM⟩ := h₂ k
  use max N M
  intro n hn
  dsimp only [Pi.add_apply]
  rw [mul_add]
  grw [hN n ?_, hM n ?_]
  · trans max N M
    apply hn
    exact Nat.le_max_right N M

  · trans max N M
    apply hn
    exact Nat.le_max_left N M
  done

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  use fun n => (n)!
  constructor
  ·
    intro k
    use k
    intro n hn
    simp only
    rw [Nat.factorial]
    gcongr
    linarith
  ·
    intro n
    exact factorial_ne_zero n
  done

end Growth
