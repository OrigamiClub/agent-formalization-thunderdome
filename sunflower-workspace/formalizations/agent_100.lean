import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

open scoped BigOperators

/-- A finite family `P` of sets is a **sunflower with `r` petals and core `core`** if it has
exactly `r` members, the core is contained in every member, and any two distinct members meet
exactly in the core.

The last clause forces every element lying in at least two members to lie in all of them, and
makes the petals `S \ core` pairwise disjoint. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (r : ℕ) (P : Finset (Finset α)) (core : Finset α) : Prop :=
  P.card = r ∧
  (∀ S ∈ P, core ⊆ S) ∧
  (∀ ⦃S⦄, S ∈ P → ∀ ⦃T⦄, T ∈ P → S ≠ T → S ∩ T = core)

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all `k ≥ 2` and `r ≥ 1`, over any ambient
type `α`, every finite family `W` of `k`-element subsets of `α` with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals: some subfamily `P ⊆ W` is a
sunflower with `r` petals (for a suitable core).

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

`Real.log` is the natural logarithm. The hypothesis `2 ≤ k` avoids the degenerate regime
`k ∈ {0, 1}` where `log k ≤ 0` makes the right-hand side vacuous; the `k = 1` case of the
informal "all positive `k`" statement is handled separately and trivially. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (core : Finset α) (P : Finset (Finset α)),
            P ⊆ W ∧ IsSunflower r P core := by
  sorry
