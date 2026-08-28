import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke.

This file contains only the *statement*. Every theorem ends with `:= by sorry`.
Nothing is proved.
-/

namespace Agent034

open scoped BigOperators

/-- A finite family `T` of sets forms a **sunflower with core `Y`** when every
pair of distinct members of `T` intersects exactly in `Y`.

Consequences (not part of the definition, but standard):
* every element lying in `≥ 2` members lies in all of them;
* the petals `s \ Y` for `s ∈ T` are pairwise disjoint.

Because `T : Finset (Finset α)`, its members are automatically distinct, so
`T.card = r` encodes "`r` distinct petals". When the members of `T` all have the
same cardinality and `2 ≤ T.card`, each petal `s \ Y` is automatically nonempty,
so no separate nonemptiness hypothesis is imposed here. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (T : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s⦄, s ∈ T → ∀ ⦃t⦄, t ∈ T → s ≠ t → s ∩ t = Y

/-- `W` **contains a sunflower with `r` petals** when some subfamily `T ⊆ W` of
size `r` is a sunflower (for some core `Y`). -/
def HasSunflower {α : Type*} [DecidableEq α]
    (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ T ⊆ W, ∃ Y : Finset α, T.card = r ∧ IsSunflower T Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all positive integers `k`
and `r`, every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log(k+1))^k` contains a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` over an ambient type with `DecidableEq`; the family is
  `W : Finset (Finset α)`, so distinctness of members is free.
* `Real.log` is the natural logarithm. Its argument is shifted to `k + 1` so the
  bound is well-defined and the statement is true also at `k = 1` (where
  `log k = 0` would make it false); for `k ≥ 2` this differs from `log k` only by
  a bounded factor, absorbed into the absolute constant `C`.
* `C` is existentially quantified ("there is an absolute constant").
* Cardinalities are `Finset.card`, cast to `ℝ` for the inequality. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 1 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          HasSunflower W r := by
  sorry

/-- Corollary form in terms of the **sunflower function** `f k r`, defined as the
least `N` such that any family of `> N` distinct `k`-sets contains a sunflower
with `r` petals (here supplied abstractly as `f` together with its defining
property). The improved bound reads `f k r ≤ (C · r · log(k+1))^k`. -/
theorem improved_sunflower_bound
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ {α : Type*} [DecidableEq α] (k r : ℕ),
      ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) → f k r < W.card →
        HasSunflower W r) :
    ∃ C : ℝ, 0 < C ∧ ∀ k r : ℕ, 1 ≤ k → 1 ≤ r →
      (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log ((k : ℝ) + 1)) ^ k := by
  sorry

end Agent034
