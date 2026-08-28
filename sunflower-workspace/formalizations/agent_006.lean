/-
  Agent 006 — Independent formalization diversity study
  Statement of the improved sunflower lemma
  (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by Bell–Chueluecha–Warnke).

  STATEMENT ONLY.  Every theorem ends with `:= by sorry`.  Nothing is proved.
-/
import Mathlib

open scoped BigOperators

namespace Agent006

/-- A finite family `T` of sets is a **sunflower** (with common core `Y`) when the
pairwise intersections of its (distinct) members all coincide with a single set `Y`.

This is exactly the "there is a core set `Y` with `Sᵢ ∩ Sⱼ = Y` for every `i ≠ j`"
formulation.  Consequences (for `T` with at least two members):
`Y ⊆ S` for every `S ∈ T`, and the petals `S \ Y` are pairwise disjoint.

The number of petals of such a sunflower is `T.card` (members of a `Finset` are
distinct, so no separate distinctness hypothesis is needed).

We do NOT require the petals `S \ Y` to be nonempty, matching the classical
Erdős–Rado convention. -/
def IsSunflower {α : Type*} [DecidableEq α] (T : Finset (Finset α)) : Prop :=
  ∃ Y : Finset α, ∀ ⦃S₁ : Finset α⦄, S₁ ∈ T → ∀ ⦃S₂ : Finset α⦄, S₂ ∈ T →
    S₁ ≠ S₂ → S₁ ∩ S₂ = Y

/--
**Improved sunflower lemma (statement).**

There is an absolute constant `C > 0` such that: for every type `α` with decidable
equality, all naturals `k` and `r` with `2 ≤ k` and `1 ≤ r`, and every finite
family `W` of subsets of `α` each of cardinality exactly `k`, if

  `(C * r * Real.log k) ^ k  <  W.card`

then `W` contains a sunflower with `r` petals: a subfamily `T ⊆ W` with `T.card = r`
and `IsSunflower T`.

Encoding notes (see `agent_006.md`):
* Sets are `Finset α`; the family is `W : Finset (Finset α)`; cardinalities via
  `Finset.card`.
* The logarithm is `Real.log` (natural log).  The literal bound `(C r log k)^k`
  from the statement is kept verbatim; `k = 0, 1` are excluded by `2 ≤ k`
  (there `Real.log k ≤ 0` degenerates the bound and the statement is false).
* `C` is existentially quantified inside the theorem.
* `W.card`, `r`, `k` are coerced into `ℝ` for the inequality.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ T ⊆ W, T.card = r ∧ IsSunflower T := by
  sorry

/--
**Improved sunflower lemma, "sunflower function" form (statement).**

Let `sunflowerFree α k r` say that a family of `k`-sets contains no `r`-petal
sunflower.  Then there is an absolute constant `C > 0` such that every
`sunflowerFree` family `W` (of `k`-sets, `2 ≤ k`, `1 ≤ r`) satisfies
`W.card ≤ (C r log k)^k`; i.e. the sunflower function `f(k, r)` is at most
`(C r log k)^k`.
-/
theorem improved_sunflower_lemma_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (¬ ∃ T ⊆ W, T.card = r ∧ IsSunflower T) →
        (W.card : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end Agent006
