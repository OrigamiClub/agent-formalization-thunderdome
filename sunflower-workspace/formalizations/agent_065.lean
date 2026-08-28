import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke: there is an absolute constant `C` such that any finite
family of `k`-element sets with more than `(C · r · log k)^k` members contains a
sunflower with `r` petals.

This file contains the *statement only*.  The single theorem is closed with
`:= by sorry`; nothing is proved.
-/

open scoped BigOperators

/-- `IsSunflower r Y P` says that the finite family `P` of finite sets is a
*sunflower with `r` petals* and *core* `Y`:

* `P` has exactly `r` members (they are automatically pairwise distinct, being
  elements of a `Finset`), and
* any two distinct members of `P` intersect in exactly `Y`.

Equivalently, every element lying in at least two members of `P` lies in all of
them, and the petals `s \ Y` for `s ∈ P` are pairwise disjoint. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
    ∀ ⦃s₁ : Finset α⦄, s₁ ∈ P → ∀ ⦃s₂ : Finset α⦄, s₂ ∈ P → s₁ ≠ s₂ → s₁ ∩ s₂ = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and
`r ≥ 1`, over any ambient type `α`, every finite family `W` of finite subsets of
`α`, each of cardinality exactly `k`, with

  `(C · r · log k) ^ k < |W|`

contains a sunflower with `r` petals: some subfamily `P ⊆ W` with a core `Y`
such that `IsSunflower r Y P`.

Encoding notes:
* `C` is existentially quantified (an absolute constant), and `α` is bound
  *inside* the `∃ C`, so `C` may not depend on the type or the family.
* `Real.log` is the natural logarithm; the choice of base is irrelevant since a
  change of base only rescales `C`.
* `k ≥ 2` is imposed: at `k = 1` one has `Real.log 1 = 0`, collapsing the right
  side to `0` and making the statement false (and `k = 0` gives no `k`-sets of
  interest).  A `Real.log (k + 1)` variant would admit `k = 1`.
* "sunflower with `r` petals" is `P.card = r` together with the
  pairwise-intersection condition; distinctness of the petals is free. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ P ⊆ W, ∃ Y : Finset α, IsSunflower r Y P := by
  sorry
