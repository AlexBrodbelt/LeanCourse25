import Mathlib

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

open Nat Finset Real


abbrev IsPowerful (N : ℕ) := ∃ p, p.Prime ∧ p ∣ N ∧ ¬ p^2 ∣ N

/-
https://www.erdosproblems.com/137
-/
theorem erdos_137 (k : ℕ) (hk : 3 ≤ k) :
  ∃ m > 0, IsPowerful (Finset.prod (range k) (fun i => m + i)) := by
  sorry

/-
https://www.erdosproblems.com/887
-/
theorem erdos_887 : ∃ K, ∀ C > 0, ∀ᶠ n in Filter.atTop,
  #{ d ∈ Ioo (⌊(n : ℝ)^(1 / 2)⌋) (⌈ n^(1 / 2) + C * n^(1 / 4)⌉) | d ∣ n } ≤ K := by
  sorry

#check Filter.forall_eventually_of_eventually_forall
