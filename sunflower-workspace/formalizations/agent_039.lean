import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the refinements of Rao and of
Bell–Chueluecha–Warnke.

This file contains only the *statement*; every theorem ends with `:= by sorry`.
-/

namespace Agent039

open scoped BigOperators

variable {α : Type*}

/-- A finite family `S` of finite sets is a *sunflower with core `Y`* if every two
distinct members meet exactly in `Y`.  Equivalently, the petals `s \ Y` for `s ∈ S`
are pairwise disjoint.  (When `S` has at least two members this forces `Y ⊆ s` for
every `s ∈ S`, so `Y` is the common core; the number of petals is `S.card`.) -/
def IsSunflower [DecidableEq α] (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma.**
There is an absolute constant `C > 0` such that for every ambient type `α`, all
integers `k ≥ 2` and `r ≥ 1`, and every finite family `W` of `k`-element subsets of
`α` with
`|W| > (C · r · log k)^k`,
the family `W` contains a sunflower with `r` petals: an `r`-element subfamily
`S ⊆ W` together with a core `Y` such that any two distinct members of `S` intersect
precisely in `Y`.

Encoding notes:
* Sets are `Finset α`; a family is a `Finset (Finset α)`, so members are automatically
  distinct and `S.card` is the number of petals.
* `log` is the natural logarithm `Real.log`; the base is irrelevant since it can be
  absorbed into `C`.  The cardinality `|W|` is cast to `ℝ`.
* `k ≥ 2` is assumed: for `k = 1` one has `log 1 = 0`, making the bound `0` and the
  statement false, and `k = 0` is degenerate.
* `C` is existentially quantified *outside* the universal quantifier over `α, k, r, W`,
  so it is genuinely absolute. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ S ⊆ W, ∃ Y : Finset α, S.card = r ∧ IsSunflower S Y := by
  sorry

/-- Reformulation in terms of the *sunflower function* `f k r`, defined as the least
`N` such that every family of `N` sets of size `k` contains a sunflower with `r`
petals.  Here it is supplied abstractly as any function `f` with the "forcing"
property; the conclusion is the upper bound `f k r ≤ (C r log k)^k`. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ (α : Type) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
      1 ≤ r → (∀ s ∈ W, s.card = k) → f k r ≤ W.card →
      ∃ S ⊆ W, ∃ Y : Finset α, S.card = r ∧ IsSunflower S Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ k r : ℕ, 2 ≤ k → 1 ≤ r →
      (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end Agent039
