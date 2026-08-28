import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke:

There is an absolute constant `C` such that for all `k ≥ 2` and `r ≥ 1`, every
finite family `W` of sets each of size exactly `k` with
`|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

Only the statement is given here; the proof is `sorry`.
-/

namespace ImprovedSunflower

open scoped Classical

variable {α : Type*}

/-- `IsSunflower petals core` : the finsets in `petals` pairwise intersect in
exactly the finset `core`.  (`Set.Pairwise` quantifies over *distinct* members,
so this is the usual "every pairwise intersection equals the core" condition.
Any element lying in two of the petals then lies in `core`, hence in all of
them, and the sets `s \ core` for `s ∈ petals` are pairwise disjoint.)

This mirrors `Finset.IsSunflower` from `Mathlib.Combinatorics.Sunflower`; it is
restated locally so that this file is self-contained. -/
def IsSunflower [DecidableEq α] (petals : Finset (Finset α)) (core : Finset α) : Prop :=
  (petals : Set (Finset α)).Pairwise fun s t => s ∩ t = core

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that, for every type `α`, all integers
`k ≥ 2` and `r ≥ 1`, and every finite family `W` of subsets of `α`, each of
cardinality exactly `k`, if

  `(C * r * Real.log k) ^ k  <  |W|`,

then `W` contains a sub-family `S` of exactly `r` sets which is a sunflower with
some core `core` (so the `r` sets are pairwise-intersecting exactly in `core`,
and their `r` petals `s \ core` are pairwise disjoint and, by the equal-size
hypothesis with `r ≥ 2`, nonempty).

`Real.log` is the natural logarithm; the statement is restricted to `k ≥ 2` since
for `k = 1` one has `Real.log 1 = 0` and the displayed bound degenerates (and is
false), while `k ≥ 2` is the range in which the estimate is stated in the
literature. The constant `C` is quantified outside the type `α` and outside
`k`, `r`, capturing that it is genuinely absolute. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
        2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ S ⊆ W, ∃ core : Finset α, S.card = r ∧ IsSunflower S core := by
  sorry

/-- Equivalent phrasing via the *sunflower function* `f k r`, defined as the
least `N` forcing a sunflower with `r` petals among any `N` distinct `k`-sets.
Here it is stated as: for a suitable absolute `C`, whenever the family is large
enough the sunflower exists (i.e. `f k r ≤ (C r log k)^k`).  This is the same
content as `improved_sunflower_lemma`, written with the family supplied as an
indexed collection of distinct sets rather than as a `Finset (Finset α)`. -/
theorem improved_sunflower_lemma_indexed :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
        2 ≤ k → 1 ≤ r →
        ∀ (ι : Type*) (A : ι → Finset α) (T : Finset ι),
          Set.InjOn A T →
          (∀ i ∈ T, (A i).card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (T.card : ℝ) →
          ∃ P ⊆ T, ∃ core : Finset α,
            P.card = r ∧ (P : Set ι).Pairwise fun i j => A i ∩ A j = core := by
  sorry

end ImprovedSunflower
